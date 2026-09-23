/* FMP candidate: Finite Map Patterns, 2026-09-20.
 * Standalone ne-rewritten user notation; no imports or external requests.
 * Mathematical companion: fmp.py and definition.zh-CN.md.
 * Projection copy: an unavailable source map becomes an empty column.
 * Stars are essential to expansion even though local counts omit them.
 */
(() => {
  'use strict';
  const TOP = 'Limit of FMP';
  const LIMITS = {
    expandMs: 450, countMs: 70, compareMs: 130,
    columns: 1600, edges: 180000, work: 1800000,
    cacheEntries: 24, cacheCharacters: 500000
  };
  const now = () => typeof performance === 'undefined' ? Date.now() : performance.now();
  const natural = n => Number.isSafeInteger(n) && n >= 0;

  class ResourceLimit extends Error {
    constructor(message) { super(message); this.name = 'ResourceLimit'; }
  }
  class Budget {
    constructor(ms) {
      this.deadline = now() + ms;
      this.work = 0;
      this.nextCheck = 0;
    }
    tick(amount = 1) {
      this.work += amount;
      if (this.work > LIMITS.work) throw new ResourceLimit('FMP：本次运算量预算已用完，未返回截断的展开式。');
      if (this.work >= this.nextCheck) {
        this.nextCheck = this.work + 128;
        if (now() > this.deadline) throw new ResourceLimit('FMP：本次计算超时；保护阈值不是记号规则。');
      }
    }
    size(columns, edges = 0) {
      this.tick();
      if (!natural(columns) || columns > LIMITS.columns || edges > LIMITS.edges)
        throw new ResourceLimit('FMP：展开规模超过网页预算；没有截断或改写数学结果。');
    }
  }

  // NER persists expression objects with JSON.  Store arrays on the wire;
  // keep Set acceleration only in a weak runtime cache, never in the data.
  const starCache = new WeakMap();
  function starSet(c) {
    if (!starCache.has(c)) starCache.set(c, new Set(c.stars));
    return starCache.get(c);
  }
  function column(edges = [], stars = []) {
    const marks = new Set(stars);
    const result = {edges, stars: [...marks].sort((a, b) => a - b)};
    starCache.set(result, marks);
    return result;
  }
  const pivot = c => c.edges[c.edges.length - 2][0];
  const endpoint = c => c.edges[c.edges.length - 1][0];
  const edgeCount = a => a.reduce((n, c) => n + c.edges.length, 0);
  function relabel(c, image, budget) {
    budget.tick(c.edges.length + c.stars.length);
    return column(c.edges.map(([x, y]) => [image(x), image(y)]), [...c.stars].map(image));
  }
  function trace(columns, head, source, budget) {
    const path = [];
    while (head > source) {
      budget.tick();
      path.push(head);
      const c = columns[head - 1];
      if (!c || !c.edges.length) return [];
      head = pivot(c);
    }
    return head === source ? path : [];
  }

  function copyTail(pattern, budget) {
    const size = pattern.length, controller = pattern[size - 1];
    const a = controller.edges[0][0], p = pivot(controller);
    const table = new Map(controller.edges);
    const image = x => x < a ? x : x >= p ? x + size - p : table.get(x);
    const result = pattern.slice(0, -1);
    let total = edgeCount(result);
    budget.size(2 * size - p, total);
    for (let i = p - 1; i < size; i++) {
      const sourceColumn = pattern[i], edges = [];
      let available = true;
      for (const [x, y] of sourceColumn.edges) {
        budget.tick();
        const sx = image(x), ty = image(y);
        if (sx === undefined || ty === undefined) { available = false; break; }
        edges.push([sx, ty]);
      }
      if (!available) { result.push(column()); continue; }
      const stars = [];
      for (let j = 0; j < sourceColumn.edges.length; j++) {
        const [source, head] = sourceColumn.edges[j];
        if (!starSet(sourceColumn).has(head)) continue;
        const path = trace(pattern, head, source, budget);
        if (!path.length) continue;
        let keep;
        if (path[path.length - 1] >= p) keep = true;
        else {
          const low = path.find(v => v < p);
          keep = low < a || (table.has(low) && starSet(controller).has(image(low)) && edges[j + 1][0] <= a);
        }
        if (keep && trace(result, image(head), image(source), budget).length) stars.push(image(head));
      }
      result.push(column(edges, stars));
      total += edges.length;
      budget.size(result.length, total);
    }
    if (!result[result.length - 1].edges.length)
      throw new Error('FMP：控制表不满足自闭不变量，不能把它当作标准输入。');
    return result;
  }

  function complete(pattern, start, budget) {
    const columns = pattern.slice(), widths = new Map();
    let r = start, total = edgeCount(columns);
    while (r <= columns.length) {
      budget.size(columns.length, total);
      let c = columns[r - 1];
      if (!c.edges.length) { r++; continue; }
      const table = new Map(c.edges), stars = new Set(c.stars);
      const sources = new Map(c.edges.map(([x, y]) => [y, x]));
      for (const head of [...c.stars].sort((x, y) => x - y)) {
        const source = sources.get(head), path = trace(columns, head, source, budget);
        const width = path.length ? widths.get(path[path.length - 1]) || 0 : 0;
        if (width) {
          const next = c.edges.find(([x]) => x > source);
          if (!next || source + width >= next[0] || head + width >= next[1])
            throw new Error('FMP：补全间隙不满足定义不变量；请保留当前式供检查。');
        }
        budget.size(columns.length, total + width);
        for (let j = 1; j <= width; j++) {
          budget.tick();
          table.set(source + j, head + j);
          stars.add(head + j);
        }
        total += width;
      }
      c = column([...table].sort((x, y) => x[0] - y[0]), stars);
      columns[r - 1] = c;
      const p = pivot(c), e = endpoint(c), width = e - p - 1;
      if (width < 0) throw new Error('FMP：来源端点倒置。');
      if (width) {
        total += width * c.edges.length + width * (width + 1) / 2;
        budget.size(columns.length + width, total);
        const shift = x => x > r ? x + width : x;
        for (let i = r; i < columns.length; i++) columns[i] = relabel(columns[i], shift, budget);
        widths.set(r, width);
        const edges = c.edges.slice(0, -1);
        for (let j = 1; j <= width; j++) edges.push([p + j, r + j]);
        edges.push([e, r + width + 1]);
        const family = [], accumulated = new Set(c.stars);
        for (let j = 0; j <= width; j++) {
          if (j) accumulated.add(r + j - 1);
          budget.tick(c.edges.length + j + accumulated.size);
          family.push(column(edges.slice(0, c.edges.length + j), accumulated));
        }
        columns.splice(r - 1, 1, ...family);
      }
      r += width + 1;
    }
    return columns;
  }

  function seed(n, budget = new Budget(LIMITS.expandMs)) {
    if (!natural(n)) throw new Error('FMP：基本列指标须为可精确表示的非负整数。');
    budget.size(2 + 2 * n, 2 + 6 * n);
    const result = [column(), column([[1, 2], [2, 3]])];
    for (let i = 0; i < n; i++) {
      const a = 2 * i + 1;
      for (const step of [1, 2]) {
        const r = result.length + 1, edges = [];
        for (let x = a; x <= r - step + 1; x++) edges.push([x, x + step]);
        result.push(column(edges));
        budget.tick(edges.length);
      }
    }
    return result;
  }
  function expandCore(pattern, index, budget) {
    if (!pattern.length) return pattern;
    if (index === 0 || !pattern[pattern.length - 1].edges.length) return pattern.slice(0, -1);
    const size = pattern.length, span = size - pivot(pattern[size - 1]);
    budget.size(size - 1 + index * span, edgeCount(pattern));
    let work = pattern;
    for (let i = 0; i < index; i++) work = copyTail(work, budget);
    return complete(work.slice(0, -1), size, budget);
  }
  function FS(pattern, index) {
    if (!natural(index)) throw new Error('FMP：基本列指标须为可精确表示的非负整数。');
    const budget = new Budget(LIMITS.expandMs);
    return pattern === TOP ? seed(index, budget) : expandCore(pattern, index, budget);
  }

  const stateCache = new WeakMap(), columnKeyCache = new WeakMap();
  function makeState(p, edges) {
    return {p, edges, key: p + '|' + edges.map(([x, y]) => x + ':' + y).join(',')};
  }
  function state(c) {
    if (!c.edges.length) return null;
    if (!stateCache.has(c)) stateCache.set(c, makeState(pivot(c), c.edges.slice(0, -2)));
    return stateCache.get(c);
  }
  const stateKey = s => s === null ? '' : s.key;
  function columnKey(c) {
    if (!columnKeyCache.has(c)) columnKeyCache.set(c, c.edges.map(([x, y]) =>
      x + ':' + y + (starSet(c).has(y) ? '*' : '')).join(','));
    return columnKeyCache.get(c);
  }
  function localStep(states, current, budget) {
    const source = states[current.p - 1];
    if (source === undefined) throw new Error('FMP：局部控制引用超出了左侧上下文。');
    if (source === null || !current.edges.length) return source;
    const a = current.edges[0][0], table = new Map(current.edges);
    const image = x => x < a ? x : table.get(x);
    budget.tick(current.edges.length + source.edges.length);
    if (source.p + 1 < current.p && image(source.p + 1) === undefined) return null;
    const p = image(source.p);
    if (p === undefined) return null;
    const edges = [];
    for (const [x, y] of source.edges) {
      const sx = image(x), ty = image(y);
      if (sx === undefined || ty === undefined) return null;
      edges.push([sx, ty]);
    }
    return makeState(p, edges);
  }
  class Counter {
    constructor(pattern, budget) {
      this.states = [];
      for (const c of pattern) { budget.tick(c.edges.length + 1); this.states.push(state(c)); }
      this.memo = new Map([['', 1n]]);
      this.characters = 0;
    }
    count(current, budget) {
      const path = [], seen = new Set();
      let key = stateKey(current);
      while (!this.memo.has(key)) {
        budget.tick();
        if (seen.has(key)) throw new Error('FMP：检测到局部循环，请保留当前式供检查。');
        seen.add(key); path.push(key);
        current = localStep(this.states, current, budget);
        key = stateKey(current);
      }
      let value = this.memo.get(key);
      for (let i = path.length - 1; i >= 0; i--) {
        value++;
        if (this.characters + path[i].length <= LIMITS.cacheCharacters) {
          this.memo.set(path[i], value);
          this.characters += path[i].length;
        }
      }
      return value;
    }
  }
  const countCache = new Map();
  function countValues(pattern) {
    const budget = new Budget(LIMITS.countMs);
    let entry = countCache.get(pattern);
    try {
      if (!entry) {
        entry = {counter: new Counter([], budget), values: []};
        countCache.set(pattern, entry);
        if (countCache.size > LIMITS.cacheEntries) countCache.delete(countCache.keys().next().value);
      }
      while (entry.values.length < pattern.length) {
        budget.tick();
        if (entry.counter.states.length <= entry.values.length) {
          const c = pattern[entry.values.length];
          budget.tick(c.edges.length + 1);
          entry.counter.states.push(state(c));
        }
        entry.values.push(entry.counter.count(entry.counter.states[entry.values.length], budget));
      }
    } catch (error) {
      if (!(error instanceof ResourceLimit)) throw error;
    }
    const values = entry ? entry.values.slice() : [];
    while (values.length < pattern.length) values.push(null);
    return values;
  }
  function compareStates(states, left, right, budget) {
    const seen = [new Map(), new Map()], current = [left, right];
    for (let depth = 0; ; depth++) {
      if (current[0] === null || current[1] === null) {
        if (current[0] === current[1]) throw new Error('FMP：同计数却不同列，可能不属于同一个标准可达域。');
        return current[0] === null ? -1 : 1;
      }
      for (let side = 0; side < 2; side++) {
        budget.tick();
        const key = stateKey(current[side]);
        if (seen[1 - side].has(key)) {
          let difference = depth - seen[1 - side].get(key);
          if (side) difference = -difference;
          if (!difference) throw new Error('FMP：同计数却不同列，可能不属于同一个标准可达域。');
          return Math.sign(difference);
        }
        if (seen[side].has(key)) throw new Error('FMP：比较时检测到局部循环。');
        seen[side].set(key, depth);
        current[side] = localStep(states, current[side], budget);
      }
    }
  }
  function compare(a, b) {
    if (a === b) return 0;
    if (a === TOP) return 1;
    if (b === TOP) return -1;
    const budget = new Budget(LIMITS.compareMs), length = Math.min(a.length, b.length);
    for (let i = 0; i < length; i++) {
      budget.tick();
      if (columnKey(a[i]) !== columnKey(b[i])) {
        const counter = new Counter(a.slice(0, i), budget);
        return compareStates(counter.states, state(a[i]), state(b[i]), budget);
      }
    }
    return Math.sign(a.length - b.length);
  }

  function text(pattern, full = false) {
    if (pattern === TOP) return TOP;
    if (!pattern.length) return '0';
    return pattern.map(c => {
      if (!c.edges.length) return '[]';
      const edges = full ? c.edges : c.edges.slice(0, -2);
      let body = edges.map(([x, y]) => x + ':' + y + (starSet(c).has(y) ? '*' : '')).join(',');
      if (!full) body += (body ? ';' : '') + pivot(c);
      return '[' + body + ']';
    }).join('');
  }
  function validate(pattern, budget = new Budget(LIMITS.expandMs)) {
    budget.size(pattern.length, edgeCount(pattern));
    for (let i = 0; i < pattern.length; i++) {
      const r = i + 1, c = pattern[i], e = c.edges;
      budget.tick(e.length);
      if (!e.length) {
        if (c.stars.length) throw new Error('FMP：空列不能带星号。');
        continue;
      }
      if (e.length < 2) throw new Error('FMP：非空列缺少两条端点边。');
      const p = pivot(c), domain = new Set(e.map(pair => pair[0]));
      if (p < 1 || p >= r || endpoint(c) !== p + 1 ||
          e[e.length - 2][1] !== r || e[e.length - 1][1] !== r + 1)
        throw new Error('FMP：端点必须是 p→本列、p+1→下一边界。');
      for (let j = 0; j < e.length; j++) {
        const [x, y] = e[j];
        if (!natural(x) || !natural(y) || x < 1 || x >= y ||
            (j && (x <= e[j - 1][0] || y <= e[j - 1][1])))
          throw new Error('FMP：对应表须严格递增，且每条边来源小于目标。');
        if (y < p && !domain.has(y)) throw new Error('FMP：每个小于 p 的目标也必须是本表来源。');
        if (starSet(c).has(y) && (j >= e.length - 2 || y < p + 1 || !trace(pattern, y, x, budget).length))
          throw new Error('FMP：星号须在内部上窗，并有准确的父追溯。');
      }
      if ([...c.stars].some(y => !e.some(pair => pair[1] === y))) throw new Error('FMP：星号没有对应边。');
    }
    return pattern;
  }
  function parse(input) {
    const source = String(input).replace(/\s+/g, '');
    if (/^(LimitofFMP|top|Ω)$/i.test(source)) return TOP;
    if (!source || source === '0' || source === '∅') return [];
    const matches = [...source.matchAll(/\[([^\[\]]*)\]/g)];
    if (matches.map(m => m[0]).join('') !== source) throw new Error('FMP：请按 [列][列] 输入。');
    const budget = new Budget(LIMITS.expandMs);
    budget.size(matches.length);
    const pattern = matches.map((match, index) => {
      const body = match[1], r = index + 1;
      if (!body) return column();
      let part, pText = null;
      if (body.includes(';')) {
        const pieces = body.split(';');
        if (pieces.length !== 2) throw new Error('FMP：每列最多一个分号，用于分隔末端 p。');
        [part, pText] = pieces;
      } else if (!body.includes(':')) { part = ''; pText = body; }
      else part = body;
      const edges = [], stars = [];
      for (const token of part ? part.split(',') : []) {
        budget.tick();
        const edge = /^(\d+):(\d+)(\*)?$/.exec(token);
        if (!edge) throw new Error('FMP：内部对应写为 x:y 或 x:y*。');
        const x = Number(edge[1]), y = Number(edge[2]);
        edges.push([x, y]);
        if (edge[3]) stars.push(y);
      }
      if (pText !== null) {
        if (!/^\d+$/.test(pText)) throw new Error('FMP：末端 p 须为正整数。');
        const p = Number(pText);
        edges.push([p, r], [p + 1, r + 1]);
      }
      return column(edges, stars);
    });
    return validate(pattern, budget);
  }
  function countText(pattern) {
    if (pattern === TOP) return TOP;
    return countValues(pattern).map(n => n === null ? '?' : String(n)).join(',') || '0';
  }

  // A single triangular table: column r stores its images at source rows x.
  // Omit only the final cap edge (p+1)->(r+1); the visible p->r recovers it.
  const VIEW = {ms: 120, columns: 256, pixels: 8000000, dimension: 8192, svgCharacters: 1800000};
  const escape = value => String(value).replace(/[&<>"']/g,
    c => ({'&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;'}[c]));
  function adjacencyText(pattern) {
    if (pattern === TOP || !pattern.length) return pattern === TOP ? TOP : '0';
    const budget = new Budget(VIEW.ms);
    return pattern.map(c => {
      if (!c.edges.length) return '[]';
      budget.tick(pivot(c));
      const slots = Array(pivot(c)).fill('');
      for (const [x, y] of c.edges.slice(0, -1)) slots[x - 1] = y + (starSet(c).has(y) ? '*' : '');
      return '[' + slots.join(',') + ']';
    }).join('');
  }
  function adjacencyParse(input) {
    const source = String(input).replace(/\s+/g, '');
    if (!source || /^(0|∅|LimitofFMP|top|Ω)$/i.test(source)) return parse(source);
    const matches = [...source.matchAll(/\[([^\[\]]*)\]/g)];
    if (matches.map(m => m[0]).join('') !== source) throw new Error('FMP：邻接文字须为连续的 [列][列]。');
    const budget = new Budget(LIMITS.expandMs);
    budget.size(matches.length);
    const result = matches.map((match, index) => {
      const slots = match[1] ? match[1].split(',') : [];
      while (slots.length && !slots[slots.length - 1]) slots.pop();
      if (!slots.length) return column();
      budget.tick(slots.length);
      if (slots.length > index) throw new Error('FMP：邻接来源必须在本列以前。');
      const edges = [], stars = [];
      slots.forEach((slot, i) => {
        if (!slot) return;
        const value = /^(\d+)(\*)?$/.exec(slot);
        if (!value) throw new Error('FMP：邻接格只填目标数字，可附星号；空位保留逗号。');
        const y = Number(value[1]);
        edges.push([i + 1, y]);
        if (value[2]) stars.push(y);
      });
      if (edges[edges.length - 1][1] !== index + 1)
        throw new Error('FMP：每个非空邻接列的最后一个目标须为本列号。');
      edges.push([slots.length + 1, index + 2]);
      return column(edges, stars);
    });
    return validate(result, budget);
  }
  function diagramMessage(message, warning = false) {
    return {width: Math.max(80, message.length * 13 + 8), height: 24, elements: [],
      extra_text: [{text: message, x: 4, y: 12, size: 13, align: 'left',
        color: {type: warning ? 'red' : 'text'}}],
      _fmp: {complete: !warning, warning}};
  }
  function adjacencyDiagram(pattern) {
    if (pattern === TOP || !pattern.length) return diagramMessage(pattern === TOP ? TOP : '0');
    const n = pattern.length;
    if (n > VIEW.columns) throw new ResourceLimit('FMP：完整表格超过绘图预算；未截取局部，请用列表查看。');
    const cell = Math.ceil(String(n).length * 7.4 + 7), rowHeight = 14, pad = 3;
    const tableWidth = n * cell, lineLimit = Math.max(20, Math.floor(tableWidth / 7.5));
    const sequence = countText(pattern), countLines = [];
    let line = '';
    for (const token of sequence.match(/[^,]+,?/g) || []) {
      if (line && line.length + token.length > lineLimit) { countLines.push(line); line = ''; }
      line += token;
    }
    if (line) countLines.push(line);
    const top = 3 + 16 * countLines.length + 4;
    const width = Math.ceil(Math.max(tableWidth + 2 * pad,
      ...countLines.map(s => s.length * 7.5 + 2 * pad)));
    const height = top + n * rowHeight + pad;
    if (width > VIEW.dimension || height > VIEW.dimension || width * height > VIEW.pixels)
      throw new ResourceLimit('FMP：完整表格画布超过预算；未截取局部，请用列表查看。');
    const budget = new Budget(VIEW.ms), elements = [], extra_text = [], entries = [];
    const label = (value, x, y, kind, color = 'text', align = 'center', fields = {}) => {
      budget.tick();
      extra_text.push({text: String(value), x, y, size: 12, align,
        color: {type: color}, _fmp: {kind, ...fields}});
    };
    for (let i = 0; i < countLines.length; i++)
      label(countLines[i], pad, 10 + 16 * i, 'counts', 'text', 'left');
    for (let j = 0; j < n; j++) {
      const cy = top + (j + 0.5) * rowHeight;
      elements.push({type: 'line', x1: pad + j * cell, y1: cy,
        x2: pad + (j + 1) * cell, y2: cy, stroke: true, width: rowHeight,
        stroke_color: {color: {r: 93, g: 155, b: 217, a: 0.24}}, _fmp: {kind: 'diagonal-fill'}});
      label(j + 1, pad + (j + 0.5) * cell, cy, 'diagonal', 'text', 'center', {column: j + 1});
      for (const [x, y] of pattern[j].edges.slice(0, -1)) {
        const starred = starSet(pattern[j]).has(y), entry = {column: j + 1, source: x, target: y, starred};
        label(y + (starred ? '*' : ''), pad + (j + 0.5) * cell,
          top + (x - 0.5) * rowHeight, 'entry', starred ? 'red' : 'text', 'center', entry);
        entries.push(entry);
      }
    }
    for (let i = 0; i <= n; i++) {
      budget.tick();
      elements.push({type: 'line', x1: pad + Math.max(0, i - 1) * cell, y1: top + i * rowHeight,
        x2: pad + tableWidth, y2: top + i * rowHeight, stroke: true, width: 0.6,
        stroke_color: {type: 'gray'}, _fmp: {kind: 'horizontal'}});
      elements.push({type: 'line', x1: pad + i * cell, y1: top, x2: pad + i * cell,
        y2: top + Math.min(n, i + 1) * rowHeight, stroke: true, width: 0.6,
        stroke_color: {type: 'gray'}, _fmp: {kind: 'vertical'}});
    }
    return {width, height, elements, extra_text,
      _fmp: {complete: true, columns: n, entries, countText: sequence, cell, rowHeight, top}};
  }
  function safeAdjacencyDiagram(pattern) {
    try { return adjacencyDiagram(pattern); }
    catch (error) {
      if (!(error instanceof ResourceLimit)) throw error;
      return diagramMessage(error.message, true);
    }
  }
  const svgColor = spec => spec.color ?
    'rgba(' + [spec.color.r, spec.color.g, spec.color.b, spec.color.a ?? 1].join(',') + ')' :
    spec.type === 'gray' ? 'var(--color-text-muted,#999)' :
    spec.type === 'red' ? 'var(--color-danger,#b54c43)' : 'currentColor';
  function adjacencySVG(pattern) {
    const value = safeAdjacencyDiagram(pattern), parts = [
      '<svg xmlns="http://www.w3.org/2000/svg" role="img" width="' + value.width +
      '" height="' + value.height + '" viewBox="0 0 ' + value.width + ' ' + value.height +
      '" style="display:block;max-width:none;font-family:inherit" aria-label="FMP 上三角对应表">',
      '<title>FMP 对应表</title><desc>顶部是计数序列。对角格标记列号与来源行号；',
      '格内数字为该列在该来源的目标，红色星号保留复合标记。最后的 cap 边由末来源恢复。</desc>'
    ];
    for (const item of value.elements) parts.push('<line x1="' + item.x1 + '" y1="' + item.y1 +
      '" x2="' + item.x2 + '" y2="' + item.y2 + '" stroke="' + svgColor(item.stroke_color) +
      '" stroke-width="' + item.width + '" stroke-linecap="butt"/>');
    for (const item of value.extra_text) {
      const info = item._fmp;
      const title = info?.kind === 'entry' ? '<title>第 ' + info.column + ' 列：' + info.source +
        ' → ' + info.target + (info.starred ? '，星边' : '') + '</title>' : '';
      parts.push('<text x="' + item.x + '" y="' + item.y + '" font-size="' + item.size +
        '" dominant-baseline="middle" text-anchor="' + ({left: 'start', center: 'middle', right: 'end'}[item.align]) +
        '" fill="' + svgColor(item.color) + '">' + title + escape(item.text) + '</text>');
    }
    parts.push('</svg>');
    const result = parts.join('');
    if (result.length > VIEW.svgCharacters)
      return '<span style="color:var(--color-danger,#b54c43)">FMP：完整表格文字超过预算，未截取局部；请用列表查看。</span>';
    return result;
  }

  const notation = {
    id: 'fmp-candidate-20260920', name: 'FMP', simple_name: 'FMP',
    description: [
      '有限映射图样：投影复制末段，再统一补齐来源端点间隙；空列是后继。',
      '[x:y*,…;p] 中星号记复合信息；省略的端点是 p→本列、p+1→下一边界。[p] 只有端点边。',
      '已附 ZFC + I3 下的纸面良序证明稿；尚未 Lean 形式化或独立终审。没有与整个 IBLP 的大小结论。',
      '计数是精确局部倒计数；? 只表示预算未完成。比较不使用近似计数。手写输入只检查有限格式，不认证可达性。',
      '邻接表按来源定位：每列 [] 内第 x 个格位填写 F(x)，逗号分隔，星边带 *，空位留空。最后的 cap 边自动恢复。',
      '图表只用一张上三角表；对角线浅色格同时充当行列号，顶部是计数序列，无外侧编号。绘图超限不显示局部。'
    ],
    display: {name: '列表', plain: a => text(a), html: a => text(a), from_display: parse},
    display_equiv: {
      '计数序列': {plain: countText, html: countText},
      '完整对应表': {plain: a => text(a, true), html: a => text(a, true), from_display: parse},
      '邻接表（文字）': {plain: adjacencyText, html: adjacencyText,
        latex: a => '\\text{' + adjacencyText(a) + '}', from_display: adjacencyParse},
      '邻接表（图）': {plain: adjacencyText, html: adjacencySVG,
        latex: a => '\\text{' + adjacencyText(a) + '}', from_display: adjacencyParse}
    },
    init: () => [TOP, parse('[][1][2]'),
      parse('[][1][1][1:3*;2][1][1:5*;2][1:5*,2:6*;3][1:5*,2:6*;3]'),
      parse('[][1][1][1:3*;2][1][1:5*;2][1:5*,2:6*;3]'),
      seed(0), [column()], []],
    is_limit: a => a === TOP || (a.length > 0 && a[a.length - 1].edges.length > 0),
    compare, FS, FS_alter: FS, FS_short: FS,
    draw_diagram: {default_data: {}, draw_diagram: safeAdjacencyDiagram},
    debug: {TOP, LIMITS, Budget, ResourceLimit, column, trace, copyTail, complete,
      seed, expandCore, validate, parse, text, state, localStep, Counter,
      countValues, countText, compareStates, adjacencyText, adjacencyParse,
      adjacencyDiagram, adjacencySVG, VIEW, clearCountCache: () => countCache.clear()}
  };
  if (typeof register_notation === 'function') register_notation(notation);
  if (typeof module !== 'undefined' && module.exports) module.exports = notation;
})();
