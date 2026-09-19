/* ICP candidate — Interpolating Copy Patterns, 2026-09-19.
 * Monotone address copying, root-first control, and live-prefix interpolation.
 * A new version, NOT the ill-founded IRP. Global well-ordering is unproved.
 */
(() => {
  'use strict';
  const TOP = null;
  const LIMITS = {ms: 750, countMs: 100, columns: 1400, edges: 180000,
    work: 1800000, drawing: 90, inputChars: 2500000};
  const natural = x => Number.isSafeInteger(x) && x >= 0;
  const sign = (a, b) => a < b ? -1 : a > b ? 1 : 0;
  class ResourceLimit extends Error {
    constructor(message) { super('ICP：' + message + '（资源限制，不代表不终止）'); }
  }
  class Budget {
    constructor(ms = LIMITS.ms) { this.end = Date.now() + ms; this.work = 0; }
    tick(work = 1) {
      this.work += work;
      if (this.work > LIMITS.work || Date.now() > this.end)
        throw new ResourceLimit('本次计算预算用尽');
    }
    size(columns, edges) {
      this.tick();
      if (columns > LIMITS.columns || edges > LIMITS.edges)
        throw new ResourceLimit('展开结果过大');
    }
  }

  // Complete mathematical kernel; all edge coordinates are earlier addresses.
  function column(edges) {
    const values = new Map();
    for (const [p, q] of edges) values.set(p, Math.max(q, values.get(p) ?? -1));
    return [...values].sort((a, b) => b[0] - a[0]);
  }
  function control(c) {
    return c.reduce((a, b) => b[1] > a[1] || b[1] === a[1] && b[0] > a[0] ? b : a);
  }
  function lower(prefix, c) {
    const [parent, root] = control(c);
    const edges = [...c.filter(([p]) => p !== parent), ...prefix[parent]];
    if (root) edges.push([parent, root - 1]);
    return column(edges);
  }
  function reflect(pattern, budget = new Budget()) {
    if (!pattern.length || !pattern.at(-1).length) return pattern;
    const [cut] = control(pattern.at(-1));
    const output = [...pattern.slice(0, -1), lower(pattern, pattern.at(-1))];
    let edges = output.reduce((n, c) => n + c.length, 0);
    budget.size(output.length, edges);
    const image = [...Array.from({length: cut}, (_, p) => p), output.length - 1];
    function append(c) {
      edges += c.length; budget.tick(1 + c.length);
      budget.size(output.length + 1, edges); output.push(c);
    }
    for (let i = cut + 1; i < pattern.length; i++) {
      budget.tick(1 + pattern[i].length);
      let current = column(pattern[i].map(([p, q]) => [image[p], image[q]]));
      const ancestors = [];
      if (current.length) {
        const [parent, root] = control(current);
        let at = root;
        while (output[at].length) {
          budget.tick(); at = control(output[at])[0];
          if (at <= parent) break;
          ancestors.push(at);
        }
      }
      append(current);
      for (let k = ancestors.length - 1; k >= 0; k--) {
        current = column([...current, [ancestors[k], output.length - 1]]);
        append(current);
      }
      image.push(output.length - 1);
    }
    return output;
  }
  function seed(height) {
    if (!natural(height)) throw Error('ICP：种子指标必须为非负安全整数');
    new Budget().size(height + 1, height * (height + 1) / 2);
    return [[], ...Array.from({length: height}, (_, k) =>
      Array.from({length: k + 1}, (_, p) => [k - p, k]))];
  }
  function FS(pattern, n) {
    if (!natural(n)) throw Error('ICP：基本列指标必须为非负安全整数');
    if (pattern === TOP) return seed(n);
    if (!n || !pattern.length || !pattern.at(-1).length) return pattern.slice(0, -1);
    const budget = new Budget();
    let current = pattern;
    for (let i = 0; i < n; i++) { budget.tick(); current = reflect(current, budget); }
    return current.slice(0, -1);
  }
  function compare(a, b) {
    if (a === b) return 0;
    if (a === TOP || b === TOP) return a === TOP ? 1 : -1;
    for (let j = 0; j < Math.min(a.length, b.length); j++) {
      const x = a[j], y = b[j];
      for (let i = 0; i < Math.min(x.length, y.length); i++) {
        const order = sign(x[i][0], y[i][0]) || sign(x[i][1], y[i][1]);
        if (order) return order;
      }
      if (x.length !== y.length) return sign(x.length, y.length);
    }
    return sign(a.length, b.length);
  }
  function count(prefix, current, budget = new Budget(LIMITS.countMs)) {
    let value = 1n;
    while (current.length) {
      budget.tick(1 + current.length);
      current = lower(prefix, current); value++;
    }
    return value;
  }

  // Display and NER integration do not change FS or comparison.
  const cache = new WeakMap();
  function counts(pattern, ms = LIMITS.countMs) {
    if (pattern === TOP) return null;
    const known = cache.get(pattern) || [], result = [], budget = new Budget(ms);
    let exhausted = false;
    for (let j = 0; j < pattern.length; j++) {
      if (known[j] !== undefined) { result.push(known[j]); continue; }
      if (!pattern[j].length) { result.push(1n); known[j] = 1n; continue; }
      if (exhausted) { result.push(null); continue; }
      try {
        const value = count(pattern.slice(0, j), pattern[j], budget);
        result.push(value); known[j] = value;
      } catch (error) {
        if (!(error instanceof ResourceLimit)) throw error;
        result.push(null); exhausted = true;
      }
    }
    cache.set(pattern, known); return result;
  }
  function text(pattern) {
    if (pattern === TOP) return 'Limit of ICP';
    return pattern.map(c => '[' + c.map(([p, q]) => p + ':' + q).join(',') + ']').join('') || '0';
  }
  function parse(input) {
    if (input.length > LIMITS.inputChars) throw new ResourceLimit('输入过长');
    const s = input.replace(/\s/g, '');
    if (/^(top|limit|LimitofICP|ICP)$/i.test(s)) return TOP;
    if (/^S\d+$/i.test(s)) return seed(Number(s.slice(1)));
    if (!s || s === '0') return [];
    const parts = s.match(/\[[^\[\]]*\]/g);
    if (!parts || parts.join('') !== s) throw Error('ICP：请输入 [父地址:根地址,...]、S2、0 或 Limit of ICP');
    const budget = new Budget(); let edges = 0;
    budget.size(parts.length, edges);
    return parts.map((part, j) => {
      const body = part.slice(1, -1);
      const raw = !body ? [] : body.split(/[,;]/).map(entry => {
        if (!/^\d+:\d+$/.test(entry)) throw Error('ICP：每条边必须为两个非负整数 p:q');
        const edge = entry.split(':').map(Number);
        if (edge.some(x => !natural(x) || x >= j)) throw Error('ICP：地址必须指向前列');
        budget.tick(); return edge;
      });
      edges += raw.length; budget.size(parts.length, edges);
      return column(raw);
    });
  }
  function countText(pattern) {
    if (pattern === TOP) return 'Limit of ICP';
    return counts(pattern).map(x => x === null ? '?' : String(x)).join(',') || '0';
  }
  function tableHTML(pattern) {
    if (pattern === TOP || !pattern.length) return text(pattern);
    if (pattern.length > LIMITS.drawing)
      return countText(pattern) + '<br>表格过大，未绘制；请查看完整列表。';
    let html = '<span>' + countText(pattern) + '</span><table style="border-collapse:collapse;margin-top:3px;font:inherit;text-align:center">';
    for (let p = 0; p < pattern.length; p++) {
      html += '<tr>' + (p ? '<td colspan="' + p + '" style="border:0"></td>' : '');
      for (let j = p; j < pattern.length; j++) {
        const edge = pattern[j].find(e => e[0] === p);
        html += '<td style="border:1px solid #89919d;padding:0 2px;' +
          (p === j ? 'background:rgba(128,144,166,.24);' : '') + '">' +
          (p === j ? j : edge ? edge[1] : '') + '</td>';
      }
      html += '</tr>';
    }
    return html + '</table>';
  }
  const notation = {
    id: 'icp-candidate-20260919', name: 'ICP候选', simple_name: 'ICP',
    description: [
      '插值复制图：每条边两个前列地址，控制先比根、再比父；地址搬运严格递增。',
      '本版本不良序：标准式 S3[1][1][0]（计数 1,2,5,10）反复取 [1] 产生无穷降链。',
      '保留原规则供复核；ICP 1,2 和 1,2,4 以下的 RPD 局部对应不受此反例影响。',
      '计数是固定位置的精确局部倒计数；? 表示当前预算未算完，不参与大小比较。'
    ],
    display: {name: '列表', plain: text, html: text, from_display: parse},
    display_equiv: {
      '计数序列': {plain: countText, html: countText},
      '邻接表': {plain: text, html: tableHTML, from_display: parse}
    },
    init: () => [TOP, [[]], []],
    is_limit: a => a === TOP || !!a.at(-1)?.length,
    compare, FS, FS_alter: FS, FS_short: FS,
    debug: {column, control, lower, reflect, seed, count, counts,
      text, parse, countText, tableHTML, Budget, ResourceLimit, LIMITS}
  };
  if (typeof register_notation === 'function') register_notation(notation);
  if (typeof module !== 'undefined' && module.exports) module.exports = notation;
})();
