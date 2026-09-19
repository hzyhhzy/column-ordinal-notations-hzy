/* ACD candidate, 2026-09-18. Ancestral-Context Diagrams.
 * Each column is a parent -> head-source map, stored as pairs [parent, head].
 * BOTH references point left. No trees, ordinal labels, or histories in data.
 * Standard expressions are descendants of the compatible seeds.
 * Global well-ordering and embeddings of BTBMS/e0MN/IPD are NOT proved.
 * Self-contained NER custom notation. Engineering limits are not math rules.
 */
(() => {
  'use strict';
  const TOP = null;
  const LIMITS = { ms: 800, countMs: 160, work: 2000000, columns: 1200,
    edges: 120000, comparisons: 120000, contextCells: 600000, drawing: 100,
    cachedCores: 16, cachedContextCells: 800000 };

  class ResourceLimit extends Error {
    constructor(reason) { super('ACD：' + reason + '（资源限制，不表示不终止）'); }
  }
  class Budget {
    constructor(ms = LIMITS.ms) { this.end = Date.now() + ms; this.work = 0; }
    tick() {
      if (++this.work > LIMITS.work) throw new ResourceLimit('工作量超限');
      if ((this.work & 255) === 0 && Date.now() > this.end) throw new ResourceLimit('计算时间超限');
    }
  }
  const sign = (a, b) => (a > b ? 1 : a < b ? -1 : 0);
  const natural = x => Number.isSafeInteger(x) && x >= 0;

  // Mathematical core: a profile is the closed ancestor diagram itself.
  // A temporary view holds [local parent, original head link, local head].
  // Its comparison is the native column order, NOT a tree path order.
  class Core {
    constructor(columns, budget = new Budget()) {
      if (!Array.isArray(columns)) throw Error('ACD：需要列列表');
      this.columns = []; this.ancestors = []; this.views = []; this.memo = new Map();
      this.budget = budget; this.edgeCount = 0; this.contextCells = 0; this.knownCounts = [];
      for (const column of columns) this.append(column);
    }
    headCompare(left, right) {
      this.budget.tick();
      if (left === right) return 0;
      const a = this.views[left], b = this.views[right];
      // Every one-column ancestor diagram is the same empty column.
      if (a.length === 1 || b.length === 1) return sign(a.length, b.length);
      const key = left + ',' + right;
      if (this.memo.has(key)) return this.memo.get(key);
      let result = 0;
      for (let j = 0; !result && j < Math.min(a.length, b.length); j++) {
        const x = a[j], y = b[j];
        for (let i = 0; !result && i < Math.min(x.length, y.length); i++) {
          result = sign(x[i][0], y[i][0]) ||
            this.headCompare(x[i][1], y[i][1]) || sign(x[i][2], y[i][2]);
        }
        if (!result) result = sign(x.length, y.length);
      }
      if (!result) result = sign(a.length, b.length);
      if (this.memo.size < LIMITS.comparisons) this.memo.set(key, result);
      return result;
    }
    sourceCompare(a, b) { return this.headCompare(a, b) || sign(a, b); }
    normalize(column, child) {
      if (!Array.isArray(column)) throw Error('ACD：列必须是有限关系列表');
      const parents = new Map();
      for (const edge of column) {
        this.budget.tick();
        if (!Array.isArray(edge) || edge.length !== 2) throw Error('ACD：关系格式是父列:头列');
        const [p, h] = edge;
        if (!natural(p) || !natural(h) || p >= child || h >= child) throw Error('ACD：两个引用都必须指向前列');
        if (!parents.has(p) || this.sourceCompare(h, parents.get(p)) > 0) parents.set(p, h);
      }
      return [...parents].sort((a, b) => b[0] - a[0]);
    }
    append(raw) {
      this.budget.tick();
      const child = this.columns.length;
      if (child >= LIMITS.columns) throw new ResourceLimit('列数超限');
      const column = this.normalize(raw, child);
      this.edgeCount += column.length;
      if (this.edgeCount > LIMITS.edges) throw new ResourceLimit('关系数超限');
      this.columns.push(column);
      const support = new Set([child]);
      for (const [p, h] of column) for (const ref of [p, h]) {
        for (const i of this.ancestors[ref]) { this.budget.tick(); support.add(i); }
      }
      const ancestors = [...support].sort((a, b) => a - b);
      const address = new Map(ancestors.map((old, local) => [old, local]));
      const view = [];
      for (const old of ancestors) {
        this.budget.tick();
        this.contextCells += 1 + this.columns[old].length;
        if (this.contextCells > LIMITS.contextCells) throw new ResourceLimit('祖先图缓存大小超限');
        view.push(this.columns[old].map(([p, h]) => [address.get(p), h, address.get(h)]));
      }
      this.ancestors.push(ancestors); this.views.push(view);
    }
    control(column) {
      let best = column[0];
      for (const edge of column) {
        const relation = this.headCompare(edge[1], best[1]);
        if (relation > 0 || relation === 0 && edge[0] > best[0]) best = edge;
      }
      return best;
    }
    lowerColumn(column, child) {
      const [cut, head] = this.control(column);
      let predecessor = null;
      if (this.columns[head].length) for (let i = 0; i < child; i++) {
        if (this.headCompare(i, head) < 0 &&
          (predecessor === null || this.sourceCompare(i, predecessor) > 0)) predecessor = i;
      }
      const result = column.filter(([p]) => p !== cut);
      if (predecessor !== null) result.push([cut, predecessor]);
      result.push(...this.columns[cut]);
      return { cut, column: this.normalize(result, child) };
    }
    reflect() {
      const last = this.columns.length - 1;
      const { cut, column } = this.lowerColumn(this.columns[last], last);
      const span = last - cut, move = i => i < cut ? i : i + span;
      const out = new Core(this.columns.slice(0, last), this.budget);
      out.append(column);
      for (let j = cut + 1; j <= last; j++) out.append(this.columns[j].map(([p, h]) => [move(p), move(h)]));
      return out;
    }
  }

  const compiled = new WeakMap(), countCache = new WeakMap(), recent = new Map();
  let cachedContextCells = 0;
  function remember(expr, core) {
    const keys = [expr, core.columns];
    for (const key of keys) { compiled.set(key, core); countCache.set(key, core.knownCounts); }
    recent.set(core, keys); cachedContextCells += core.contextCells;
    while (recent.size > LIMITS.cachedCores || cachedContextCells > LIMITS.cachedContextCells) {
      const [old, aliases] = recent.entries().next().value;
      for (const key of aliases) compiled.delete(key);
      recent.delete(old); cachedContextCells -= old.contextCells;
    }
  }
  function compile(expr, budget = new Budget()) {
    let core = compiled.get(expr);
    if (!core) {
      core = new Core(expr, budget);
      core.knownCounts = countCache.get(expr) || [];
      remember(expr, core);
    } else {
      const aliases = recent.get(core); recent.delete(core); recent.set(core, aliases);
    }
    core.budget = budget;
    return core;
  }
  function seed(n) {
    if (!natural(n)) throw Error('ACD：指标必须是非负安全整数');
    if (n >= LIMITS.columns) throw new ResourceLimit('种子列数超限');
    return [[], ...Array.from({ length: n }, (_, j) => [[j, j]])];
  }
  function FS(expr, n) {
    if (!natural(n)) throw Error('ACD：指标必须是非负安全整数');
    if (expr === TOP) return seed(n);
    if (!expr.length) return [];
    if (!n || !expr.at(-1).length) return expr.slice(0, -1);
    const budget = new Budget();
    let current = compile(expr, budget);
    for (let i = 0; i < n; i++) current = current.reflect();
    // The final, still-unlowered template is NOT part of the fundamental item.
    return current.columns.slice(0, -1);
  }
  function compare(a, b) {
    if (a === b) return 0;
    if (a === TOP || b === TOP) return a === TOP ? 1 : -1;
    const budget = new Budget(), ca = compile(a, budget), cb = compile(b, budget);
    for (let j = 0; j < Math.min(a.length, b.length); j++) {
      const x = ca.columns[j], y = cb.columns[j];
      for (let i = 0; i < Math.min(x.length, y.length); i++) {
        const v = sign(x[i][0], y[i][0]) || ca.sourceCompare(x[i][1], y[i][1]);
        if (v) return v;
      }
      if (x.length !== y.length) return sign(x.length, y.length);
    }
    return sign(a.length, b.length);
  }
  function counts(expr, ms = LIMITS.countMs) {
    if (expr === TOP) return null;
    const answer = [];
    let core;
    try { core = compile(expr, new Budget(ms)); }
    catch (error) {
      if (!(error instanceof ResourceLimit) && !(error instanceof RangeError)) throw error;
      const known = countCache.get(expr) || [];
      return expr.map((c, i) => known[i] !== undefined ? known[i] : c.length ? null : 1n);
    }
    let exhausted = false;
    for (let child = 0; child < core.columns.length; child++) {
      let column = core.columns[child];
      if (core.knownCounts[child] !== undefined) { answer.push(core.knownCounts[child]); continue; }
      if (!column.length) { answer.push(1n); core.knownCounts[child] = 1n; continue; }
      if (exhausted) { answer.push(null); continue; }
      let count = 1n;
      try {
        while (column.length) { core.budget.tick(); column = core.lowerColumn(column, child).column; count++; }
        answer.push(count); core.knownCounts[child] = count;
      } catch (error) {
        if (!(error instanceof ResourceLimit) && !(error instanceof RangeError)) throw error;
        answer.push(null); exhausted = true;
      }
    }
    return answer;
  }

  // Display and NER interface. Lists use zero-based addresses.
  function text(expr) {
    if (expr === TOP) return 'Limit of ACD';
    return expr.map(c => '[' + c.map(([p, h]) => p + ':' + h).join(';') + ']').join('') || '0';
  }
  function parse(source) {
    const s = source.trim();
    if (/^(top|limit|Limit of ACD|ACD)$/i.test(s)) return TOP;
    if (/^S\d+$/i.test(s)) return seed(Number(s.slice(1)));
    if (s === '0' || !s) return [];
    const parts = s.match(/\[[^\[\]]*\]/g);
    if (!parts || parts.join('') !== s.replace(/\s/g, '')) {
      // Normalize whitespace once; do not accept ignored trailing input.
      if (/\s/.test(s)) return parse(s.replace(/\s/g, ''));
      throw Error('ACD：请输入 [父列:头列;...]、S3、0 或 Limit of ACD');
    }
    const columns = parts.map(part => {
      const body = part.slice(1, -1);
      if (!body) return [];
      return body.split(';').map(entry => {
        if (!/^\d+:\d+$/.test(entry)) throw Error('ACD：关系格式是非负整数:非负整数');
        return entry.split(':').map(Number);
      });
    });
    return new Core(columns).columns;
  }
  function countText(expr) {
    if (expr === TOP) return 'Limit of ACD';
    return counts(expr).map(x => x === null ? '?' : String(x)).join(',') || '0';
  }
  function tableHTML(expr) {
    if (expr === TOP || !expr.length) return text(expr);
    if (expr.length > LIMITS.drawing) return countText(expr) + '<br>图表过大，未绘制；请查看完整列表。';
    let html = '<span>' + countText(expr) + '</span><table style="border-collapse:collapse;margin-top:3px;font:inherit;text-align:center">';
    for (let p = 0; p < expr.length; p++) {
      html += '<tr>';
      if (p) html += '<td colspan="' + p + '" style="border:0"></td>';
      for (let j = p; j < expr.length; j++) {
        const edge = expr[j].find(e => e[0] === p);
        html += '<td style="border:1px solid #8b93a1;padding:0 2px;min-width:12px;' +
          (p === j ? 'background:rgba(128,144,166,.24);' : '') + '">' + (p === j ? j : edge ? edge[1] : '') + '</td>';
      }
      html += '</tr>';
    }
    return html + '</table>';
  }
  const listDisplay = { name: '列表', plain: text, html: text, from_display: parse };
  const countDisplay = { name: '计数序列', plain: countText, html: countText };
  const tableDisplay = { name: '邻接表', plain: text, html: tableHTML };
  const notation = {
    id: 'acd-candidate-20260918', name: 'ACD候选', simple_name: 'ACD',
    description: [
      '祖先上下文图：每条关系为父列:头来源列。头读取同种记号的完整祖先图，两个引用都指向前列。',
      '仅规定种子的有限展开后代属于标准域。良序和相对 BTBMS/e0MN/IPD 的强度尚未证明。',
      '计数为固定前缀下的精确局部倒计数；? 表示本次预算未算出，不参与比较。'
    ],
    display: listDisplay,
    display_equiv: { '计数序列': countDisplay, '邻接表': tableDisplay },
    is_limit: a => a === TOP || !!a.at(-1)?.length,
    compare, FS, FS_alter: FS, FS_short: FS,
    init: () => [TOP, [[]], []],
    debug: { Core, Budget, ResourceLimit, LIMITS, seed, parse, text, counts, countText, tableHTML }
  };
  if (typeof register_notation === 'function') register_notation(notation);
  if (typeof module !== 'undefined' && module.exports) module.exports = notation;
})();
