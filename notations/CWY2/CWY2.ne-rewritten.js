/* CWY2 experimental direct-profile kernel. Exact equivalence not yet proved.
 * wY views are optional and do not participate in expansion.
 * Diagram renderer adapted from smilelee-lyx/ne-rewritten. Original wY: Yukito/Naruyoko.
 * Built 2026-09-16; see output/cwy-direct-20260916/README.zh-CN.md. */
"use strict";
(() => {
  // output/cwy-direct-20260916/cwy_direct.mjs
  function compareWords(a, b) {
    if (a[0] !== b[0]) return Math.sign(a[0] - b[0]);
    if (a.length !== b.length) return Math.sign(a.length - b.length);
    for (let i = 1; i < a.length; i++)
      if (a[i] !== b[i]) return Math.sign(a[i] - b[i]);
    return 0;
  }
  function normalizeWord(word) {
    let start = 0;
    while (start + 1 < word.length && word[start] === word[start + 1]) start++;
    return word.slice(start);
  }
  function skyline(rows) {
    const largest = /* @__PURE__ */ new Map();
    for (const [p, word] of rows)
      if (!largest.has(p) || compareWords(word, largest.get(p)) > 0) largest.set(p, word);
    const result = [];
    for (const [p, word] of [...largest].sort((a, b) => b[0] - a[0]))
      if (!result.length || compareWords(result.at(-1)[1], word) < 0) result.push([p, word]);
    return result;
  }
  var lift = (word, from, to) => word.map((q) => q === from ? to : q);
  function belowOrigin(columns, word) {
    const origin = word.at(-1);
    let previous = null;
    for (const [parent, maximum] of columns[origin]) {
      if (compareWords(maximum, word) < 0) {
        previous = maximum;
        continue;
      }
      const lower = word.slice();
      lower[lower.indexOf(origin)] = parent;
      const normalized = normalizeWord(lower);
      return previous && compareWords(previous, normalized) > 0 ? previous : normalized;
    }
    return previous;
  }
  function removeOriginalTop(columns, column = columns.at(-1), child = columns.length - 1) {
    const [parent, word] = column.at(-1), lower = belowOrigin(columns, word);
    return skyline([
      ...column.slice(0, -1),
      ...lower ? [[parent, lift(lower, word.at(-1), child)]] : []
    ]);
  }
  function minusColumn(columns) {
    const child = columns.length - 1, column = columns[child];
    if (!column?.length) throw Error("Expected a nonempty limit column");
    const parent = column.at(-1)[0];
    return skyline([
      ...removeOriginalTop(columns),
      ...columns[parent].map(([p, word]) => [p, lift(word, parent, child)])
    ]);
  }
  function fs(columns, index, maxColumns = 2e4, longer = false) {
    if (!Number.isSafeInteger(index) || index < 0) throw Error("Index must be a natural safe integer");
    if (!columns.length) return [];
    if (!index && !longer || !columns.at(-1).length) return columns.slice(0, -1);
    const last = columns.length - 1, cut = columns[last].at(-1)[0], width = last - cut;
    if (last + index * width + Number(longer) > maxColumns) throw Error("Output column budget exceeded");
    const lowered = minusColumn(columns), result = columns.slice(0, last);
    function moved(column, block) {
      const shift = (q) => q < cut ? q : q + block * width;
      return column.map(([p, word]) => [shift(p), word.map(shift)]);
    }
    for (let block = 0; block < index; block++) {
      result.push(moved(lowered, block));
      for (let k = cut + 1; k < last; k++) result.push(moved(columns[k], block + 1));
    }
    if (longer) result.push(moved(lowered, index));
    return result;
  }
  function seed(m) {
    if (!Number.isSafeInteger(m) || m < 1 || m > 1e4) throw Error("Seed out of range");
    return m === 1 ? [[], []] : [[], [[0, [0, ...Array(m - 2).fill(1)]]]];
  }
  function compare(a, b) {
    function lex(x, y, cmp) {
      for (let i = 0; i < Math.min(x.length, y.length); i++) {
        const result = cmp(x[i], y[i]);
        if (result) return result;
      }
      return Math.sign(x.length - y.length);
    }
    return lex(a, b, (x, y) => lex(
      x,
      y,
      (v, w) => Math.sign(v[0] - w[0]) || compareWords(v[1], w[1])
    ));
  }

  // output/wy-linear-20260914/compressed_core.mjs
  function compareWords2(a, b) {
    if (a[0] !== b[0]) return a[0] - b[0];
    if (a.length !== b.length) return a.length - b.length;
    for (let i = 1; i < a.length; ++i)
      if (a[i] !== b[i]) return a[i] - b[i];
    return 0;
  }

  // output/wy-linear-20260914/canonical_geometry.mjs
  var GeometryLimit = class extends Error {
  };
  var InvalidGeometry = class extends Error {
  };
  function heightCompare(a, b) {
    if (a.length !== b.length) return Math.sign(a.length - b.length);
    for (let i = a.length - 1; i >= 0; i--)
      if (a[i] !== b[i]) return Math.sign(a[i] - b[i]);
    return 0;
  }
  function difference(a, b) {
    for (let i = Math.max(a.length, b.length) - 1; i >= 0; i--)
      if ((a[i] ?? 0) !== (b[i] ?? 0)) return i;
    return -1;
  }
  function raised(height, dimension) {
    const result = height.slice();
    while (result.length <= dimension) result.push(0);
    result[dimension]++;
    result.fill(0, 0, dimension);
    return result;
  }
  function profileOf(parent, dimension, child) {
    const old = parent.cap ? parent.cap.profile : [parent.x];
    if (!old) throw new InvalidGeometry("A phantom cannot be an upper subtraction parent");
    const result = [...Array(Math.max(0, dimension + 1 - old.length)).fill(old[0]), ...old];
    if (dimension) result.fill(child, result.length - dimension);
    let first = 0;
    while (first + 1 < result.length && result[first] === result[first + 1]) first++;
    return result.slice(first);
  }
  function highestAtMost(column, height) {
    let low = 0, high = column.length - 1;
    while (low < high) {
      const middle = Math.ceil((low + high) / 2);
      if (heightCompare(column[middle].height, height) <= 0) low = middle;
      else high = middle - 1;
    }
    return column[low];
  }
  function recoverGeometry(graph, options = {}) {
    const limits = { milliseconds: 2e3, nodes: 25e3, columns: 96, wordLength: 128, ...options };
    const started = Date.now();
    let count = 0, dimension = 0;
    if (!Array.isArray(graph)) throw new InvalidGeometry("Expected columns");
    if (graph.length > limits.columns) throw new GeometryLimit("Column limit");
    for (let child = 0; child < graph.length; child++) {
      const column = graph[child];
      if (!Array.isArray(column)) throw new InvalidGeometry("Expected a column array");
      let previousParent = child;
      for (const edge of column) {
        if (!Array.isArray(edge) || edge.length !== 2) throw new InvalidGeometry("Expected [parent, profile]");
        const [parent, word] = edge;
        if (!Number.isSafeInteger(parent) || parent < 0 || parent >= previousParent)
          throw new InvalidGeometry("Parents must be strictly descending and earlier");
        previousParent = parent;
        if (!Array.isArray(word) || !word.length) throw new InvalidGeometry("Expected a profile");
        if (word.length > limits.wordLength) throw new GeometryLimit("Word length limit");
        if (word[0] > parent || word.length > 1 && word[0] === word[1])
          throw new InvalidGeometry("Profile is not normalized");
        for (let i = 0; i < word.length; i++)
          if (!Number.isSafeInteger(word[i]) || word[i] < 0 || word[i] > parent && word[i] !== child || i && word[i] < word[i - 1])
            throw new InvalidGeometry("Invalid ROOT/SELF profile");
        dimension = Math.max(dimension, word.length - 1);
      }
    }
    const mountain = [];
    function point(child, height, below, left, profile) {
      if (++count > limits.nodes || Date.now() - started >= limits.milliseconds)
        throw new GeometryLimit("Geometry reconstruction budget exhausted; validity unknown");
      const result = { x: child, height, below, left, cap: void 0, outgoing: [], profile };
      if (below) below.cap = result;
      if (left) left.outgoing.push(result);
      return result;
    }
    for (let child = 0; child < graph.length; child++) {
      const phantom = point(child, [], void 0, void 0, void 0);
      let top = point(child, [1], phantom, child ? mountain[child - 1][0] : void 0, void 0);
      const column = [phantom, top];
      mountain.push(column);
      for (const [parentIndex, maximum] of graph[child]) {
        while (true) {
          const parent = highestAtMost(mountain[parentIndex], top.height);
          const jump = difference(parent.height, top.height) + 1;
          if (jump > dimension) throw new InvalidGeometry("Required jump exceeds the graph dimension");
          const profile = profileOf(parent, jump, child);
          const comparison = compareWords2(profile, maximum);
          if (comparison > 0 || top.profile && compareWords2(top.profile, profile) >= 0)
            throw new InvalidGeometry("The claimed maximum lies in a geometry gap");
          top = point(child, raised(top.height, jump), top, parent, profile);
          column.push(top);
          if (comparison === 0) break;
        }
      }
    }
    return mountain;
  }

  // .research-ne-rewritten/src/notations/draw_mountain_util.ts
  function draw_mountain_diagram(data, opts) {
    const {
      W = 30,
      WV = 50,
      H_off = 10,
      padding = 10,
      text_size = 14,
      invert_vertical = false,
      display_html_vertical = false
    } = opts ?? {};
    const { sorted_verticals, heights, line_heights, entries, left_legs } = data;
    const cols = entries.length;
    if (cols === 0) return void 0;
    const height_last = heights[heights.length - 1] + padding;
    const total_height = height_last + padding;
    const width = WV + cols * W;
    const calc_cy = (vj) => invert_vertical ? padding + heights[vj] : height_last - heights[vj];
    const h_off_vec = invert_vertical ? -H_off : H_off;
    const elements = [];
    const lines = [];
    const extra_text = [];
    const black = { type: "text" };
    const gray = { type: "gray" };
    for (const h of line_heights) {
      const y = invert_vertical ? h + padding : height_last - h;
      lines.push({
        type: "line",
        x1: 0,
        y1: y,
        x2: width,
        y2: y,
        stroke: true,
        stroke_color: gray,
        width: 1
      });
    }
    for (let vj = 0; vj < sorted_verticals.length; vj++) {
      const label = sorted_verticals[vj];
      if (label === void 0) continue;
      extra_text.push({
        text: label,
        x: WV / 2,
        y: calc_cy(vj),
        size: text_size,
        color: black,
        align: "center",
        ...display_html_vertical ? { display_html: true } : {}
      });
    }
    for (let i = 0; i < cols; i++) {
      for (let vj = 0; vj < sorted_verticals.length; vj++) {
        const text = entries[i][vj];
        if (text === void 0) continue;
        const cx = WV + W * i + W / 2;
        const cy = calc_cy(vj);
        if (vj > 0) {
          let kv = vj - 1;
          while (kv > 0 && entries[i][kv] === void 0) kv--;
          if (entries[i][kv] !== void 0) {
            const cy_below = calc_cy(kv);
            lines.push({
              type: "line",
              x1: cx,
              y1: cy + h_off_vec,
              x2: cx,
              y2: cy_below - h_off_vec,
              stroke: true,
              stroke_color: black,
              width: 1
            });
          }
        }
        const leg = left_legs[i][vj];
        if (leg !== void 0 && vj > 0) {
          const [pi, pvj] = leg;
          const p_cx = WV + W * pi + W / 2;
          const cy_mid = calc_cy(vj - 1);
          const cy_target = calc_cy(pvj);
          lines.push({
            type: "line",
            x1: cx,
            y1: cy + h_off_vec,
            x2: p_cx,
            y2: cy_mid - h_off_vec,
            stroke: true,
            stroke_color: black,
            width: 1
          });
          lines.push({
            type: "line",
            x1: p_cx,
            y1: cy_mid - h_off_vec,
            x2: p_cx,
            y2: cy_target - h_off_vec,
            stroke: true,
            stroke_color: black,
            width: 1
          });
        }
        extra_text.push({
          text,
          x: cx,
          y: cy,
          size: text_size,
          color: black,
          align: "center"
        });
      }
    }
    elements.unshift(...lines);
    return { width, height: total_height, elements, extra_text };
  }

  // output/cwy-direct-20260916/cwy2_views.ts
  var LIMIT = { ms: 500, nodes: 6e3, columns: 192, word: 128, text: 3e5, grid: 6e4, bits: 32768 };
  var maxValue = (1n << BigInt(LIMIT.bits)) - 1n;
  var geometryCalls = 0;
  var cache = /* @__PURE__ */ new Map();
  var cacheNodes = 0;
  function difference2(a, b) {
    for (let i = Math.max(a.length, b.length) - 1; i >= 0; i--)
      if ((a[i] ?? 0) !== (b[i] ?? 0)) return i;
    return -1;
  }
  function shifted(a, d) {
    const h = a.slice();
    while (h.length <= d) h.push(0);
    h[d]++;
    h.fill(0, 0, d);
    return h;
  }
  function checkValue(v) {
    if (v > maxValue) throw Error("数值视图超过位数预算");
  }
  function getMountain(graph) {
    const key = JSON.stringify(graph), found = cache.get(key);
    if (found) return found.mountain;
    geometryCalls++;
    const mountain = recoverGeometry(graph, {
      milliseconds: LIMIT.ms,
      nodes: LIMIT.nodes,
      columns: LIMIT.columns,
      wordLength: LIMIT.word
    });
    let nodes = 0;
    for (const column of mountain) {
      nodes += column.length;
      column.at(-1).value = 1n;
      for (let i = column.length - 2; i >= 1; i--) {
        column[i].value = column[i + 1].value + column[i + 1].left.value;
        checkValue(column[i].value);
      }
      for (const entry of column.slice(2)) {
        const cap = entry.left.cap;
        entry.sep = difference2(entry.height, entry.left.height);
        entry.depth = 1 + (cap?.depth ?? 0);
        entry.asheepDepth = 1 + (cap && heightCompare(cap.height, entry.height) === 0 ? cap.asheepDepth ?? 0 : 0);
      }
    }
    while (cache.size && (cache.size >= 6 || cacheNodes + nodes > 1e4)) {
      const oldest = cache.keys().next().value;
      cacheNodes -= cache.get(oldest).nodes;
      cache.delete(oldest);
    }
    cache.set(key, { mountain, nodes });
    cacheNodes += nodes;
    return mountain;
  }
  function numerical(graph) {
    if (!graph.length) return "0";
    if (graph.length === 1) return "1";
    if (graph.length === 2) return "1," + (graph[1].length ? graph[1][0][1].length + 1 : 1);
    const result = getMountain(graph).map((c) => String(c[1].value)).join(",");
    if (result.length > LIMIT.text) throw Error("数列视图文字超过预算");
    return result;
  }
  function dbms(graph, type) {
    let result = "";
    for (const column of getMountain(graph)) {
      result += "(";
      for (const e of column.slice(2)) {
        const commas = ",".repeat(e.sep + 1), depth = type === "ADBMS" ? e.asheepDepth : e.depth;
        result += type === "DBMS" ? depth + commas : commas + depth;
        if (result.length > LIMIT.text) throw Error("矩阵视图文字超过预算");
      }
      result += (type === "DBMS" ? "0" : "") + ")";
    }
    return result;
  }
  function heightText(h) {
    if (h.length === 1) h = h[0] === 1 ? [] : [h[0] - 1];
    const result = [];
    for (let i = h.length - 1; i >= 0; i--) if (h[i])
      result.push(i === 0 ? String(h[i]) : (i === 1 ? "ω" : `ω<sup>${i}</sup>`) + (h[i] === 1 ? "" : h[i]));
    return result.join("+") || "0";
  }
  function mountainDiagram(graph, data) {
    if (!graph.length) return void 0;
    const mountain = getMountain(graph), unique = /* @__PURE__ */ new Map();
    for (const c of mountain) for (const e of c) unique.set(String(e.height), e.height);
    const sorted = [...unique.values()].sort(heightCompare);
    if (graph.length * sorted.length > LIMIT.grid) throw Error("山脉图网格超过预算；未绘制局部图");
    const lookup = new Map(sorted.map((h, i) => [String(h), i]));
    const entries = graph.map(() => Array(sorted.length - 1));
    const left_legs = graph.map(() => Array(sorted.length - 1));
    const mode = data.current_equiv;
    for (let i = 0; i < mountain.length; i++) for (const e of mountain[i].slice(1)) {
      const y = lookup.get(String(e.height)) - 1;
      if (mode === "DBMS") entries[i][y] = e.cap ? e.cap.depth + ",".repeat(e.cap.sep + 1) : "0";
      else if (mode === "DBMS_MN" || mode === "ADBMS")
        entries[i][y] = e.sep === void 0 ? "*" : ",".repeat(e.sep + 1) + (mode === "ADBMS" ? e.asheepDepth : e.depth);
      else entries[i][y] = String(e.value);
      if (e.left?.height.length) left_legs[i][y] = [e.left.x, lookup.get(String(e.left.height)) - 1];
    }
    const heights = [0], line_heights = [];
    for (let i = 2; i < sorted.length; i++) {
      const sep = difference2(sorted[i], sorted[i - 1]);
      heights.push(heights[i - 2] + 40 + 5 * sep);
      for (let k = 0; k <= sep; k++) line_heights.push(heights[i - 2] + 20 + 5 * k);
    }
    return draw_mountain_diagram(
      {
        sorted_verticals: sorted.slice(1).map(heightText),
        heights,
        line_heights,
        entries,
        left_legs
      },
      { invert_vertical: !!data.invert_vertical, display_html_vertical: true }
    );
  }
  function fromNumerical(text) {
    text = text.trim();
    if (text === "0" || !text) return [];
    if (text.length > 1e5 || !/^\d+(?:\s*,\s*\d+)*$/.test(text)) throw Error("请输入正整数数列");
    const seq = text.split(",").map((x) => BigInt(x.trim()));
    if (seq[0] !== 1n || seq.some((x) => x < 1n)) throw Error("wY 数列须以 1 开头且全部为正整数");
    if (seq.length > LIMIT.columns) throw Error("导入列数超过预算");
    const started = Date.now(), mountain = [], graph = [];
    let nodes = 0, work = 0;
    function tick2() {
      if (++work > 3e5 || nodes > LIMIT.nodes || Date.now() - started > LIMIT.ms) throw Error("数列导入超过预算");
    }
    for (let j = 0; j < seq.length; j++) {
      checkValue(seq[j]);
      tick2();
      const phantom = { x: j, height: [], left: null, cap: null };
      let top = { x: j, height: [1], value: seq[j], left: j ? mountain[j - 1][0] : null, cap: null };
      phantom.cap = top;
      const column = [phantom, top], rows = [];
      nodes += 2;
      while (top.value !== 1n) {
        tick2();
        let parent = top;
        do {
          let next = parent.left;
          if (!next) throw Error("无合法父节点");
          while (next.cap && heightCompare(next.cap.height, parent.height) <= 0) {
            tick2();
            next = next.cap;
          }
          parent = next;
          tick2();
        } while (parent.value >= top.value);
        const d = difference2(parent.height, top.height) + 1;
        const original = parent.cap?.profile ?? [parent.x];
        if (Math.max(original.length, d + 1) > LIMIT.word) throw Error("祖先词超过导入预算");
        const word = [...Array(Math.max(0, d + 1 - original.length)).fill(original[0]), ...original];
        if (d) word.fill(j, word.length - d);
        const upper = {
          x: j,
          height: shifted(top.height, d),
          value: top.value - parent.value,
          left: parent,
          cap: null,
          profile: normalizeWord(word)
        };
        top.cap = upper;
        top = upper;
        column.push(top);
        rows.push([parent.x, top.profile]);
        nodes++;
      }
      mountain.push(column);
      graph.push(skyline(rows));
    }
    return graph;
  }
  var viewDebug = () => ({ geometryCalls, cacheEntries: cache.size, cacheNodes, limits: LIMIT });

  // output/cwy-direct-20260916/cwy2_entry.ts
  var TOP = "Limit";
  var LIMIT2 = { ms: 700, columns: 12e3, atoms: 9e5, text: 4e6, path: 256 };
  var cache2 = /* @__PURE__ */ new Map();
  var cacheChars = 0;
  var isTop = (g) => g === TOP;
  function tick(start) {
    if (Date.now() - start > LIMIT2.ms) throw Error("CWY2 计算达到时间预算，未返回截断项");
  }
  function natural(n) {
    if (typeof n === "bigint" && n >= 0n && n <= BigInt(Number.MAX_SAFE_INTEGER)) n = Number(n);
    if (!Number.isSafeInteger(n) || n < 0) throw Error("指标须为非负安全整数");
    return n;
  }
  function remember(key, g) {
    if (key.length > 2e5 || cache2.has(key)) return;
    while (cache2.size && (cache2.size >= 64 || cacheChars + key.length > 2e6)) {
      const oldest = cache2.keys().next().value;
      cacheChars -= oldest.length;
      cache2.delete(oldest);
    }
    cache2.set(key, g);
    cacheChars += key.length;
  }
  function write(g) {
    if (isTop(g)) return TOP;
    const result = g.map((c) => "[" + c.map(([p, w]) => p + ":(" + w.join(",") + ")").join(";") + "]").join("") || "0";
    if (result.length > LIMIT2.text) throw Error("CWY2 完整字符串超过预算");
    return result;
  }
  function validate(g, start) {
    if (isTop(g)) return g;
    if (g.length > LIMIT2.columns) throw Error("列数超过预算");
    let atoms = 0;
    for (let j = 0; j < g.length; j++) {
      tick(start);
      let previous = j, previousWord;
      for (const [p, w] of g[j]) {
        if (!Number.isSafeInteger(p) || p < 0 || p >= previous) throw Error("父地址须严格递减并指向前列");
        previous = p;
        if (!w.length || w[0] > p || w.length > 1 && w[0] === w[1]) throw Error("非法或未正规的祖先词");
        for (let i = 0; i < w.length; i++) if (!Number.isSafeInteger(w[i]) || w[i] < 0 || w[i] > p && w[i] !== j || i > 0 && w[i] < w[i - 1]) throw Error("词字母须为非降 ROOT/SELF 地址");
        if (previousWord && compareWords(previousWord, w) >= 0) throw Error("列不满足 skyline 正规性");
        previousWord = w;
        atoms += w.length + 1;
        if (atoms > LIMIT2.atoms) throw Error("关系数据超过预算");
      }
    }
    return g;
  }
  function expand(g, n, variant = "normal") {
    n = natural(n);
    if (n > LIMIT2.columns) throw Error("展开指标超过输出预算");
    if (isTop(g)) return seed(n + 1);
    if (!g.length) return [];
    if (!g.at(-1).length || !n && variant !== "alter") return g.slice(0, -1);
    const last = g.length - 1, cut = g[last].at(-1)[0], width = last - cut;
    const data = g.reduce((sum, c) => sum + c.reduce((t, [, w]) => t + w.length + 1, 0), 0);
    if (variant === "short" && n === 1) {
      if (data * 2 > LIMIT2.atoms) throw Error("完整输出关系数据超过预算");
      return [...g.slice(0, -1), minusColumn(g)];
    }
    if (variant === "short" && width !== 1) n--;
    const longer = variant === "alter";
    if (last + n * width + Number(longer) > LIMIT2.columns) throw Error("完整输出列数超过预算");
    if (data * (n + 2) > LIMIT2.atoms) throw Error("完整输出关系数据超过预算");
    return fs(g, n, LIMIT2.columns, longer);
  }
  function readColumns(text) {
    if (/\[(?:S|⊤)\]/.test(text)) throw Error("新版不含特殊标记；旧式请使用 CWY2 legacy");
    const matches = [...text.matchAll(/\[([^\[\]]*)\]/g)];
    if (!matches.length || matches.map((m) => m[0]).join("") !== text) throw Error("请输入逐列列表、Top、E3[2] 或自然数");
    return matches.map((m, j) => m[1] === "" ? [] : m[1].split(";").map((row) => {
      const parts = /^(\d+):\(([^()]*)\)$/.exec(row);
      if (!parts) throw Error("关系应写成 父:(词)");
      const letters = parts[2].split(",");
      if (letters.some((q) => !/^(?:\d+|\*)$/.test(q))) throw Error("祖先词只能包含自然数或 *");
      return [Number(parts[1]), letters.map((q) => q === "*" ? j : Number(q))];
    }));
  }
  function parse(raw, start = Date.now()) {
    const text = String(raw).replace(/\s+/g, "");
    if (text.length > LIMIT2.text) throw Error("输入超过预算");
    const cached = cache2.get(text);
    if (cached) return cached;
    let g;
    if (/^(?:Limit(?:ofCWY2)?|Top|∞)$/i.test(text)) g = TOP;
    else if (/^\d+$/.test(text)) {
      const n = natural(BigInt(text));
      if (n > LIMIT2.columns) throw Error("有限列数超过预算");
      g = Array.from({ length: n }, () => []);
    } else if (/^(?:E\d+|Top|Limit)(?:\[\d+\])*$/i.test(text)) {
      const head = text.match(/^(?:E\d+|Top|Limit)/i)[0];
      g = /^E/i.test(head) ? seed(natural(BigInt(head.slice(1)))) : TOP;
      const steps = [...text.slice(head.length).matchAll(/\[(\d+)\]/g)];
      if (steps.length > LIMIT2.path) throw Error("输入路径超过预算");
      for (const step of steps) {
        tick(start);
        g = expand(g, BigInt(step[1]));
      }
    } else g = readColumns(text);
    validate(g, start);
    remember(text, g);
    return g;
  }
  function compare2(a, b) {
    if (isTop(a)) return isTop(b) ? 0 : 1;
    if (isTop(b)) return -1;
    return compare(a, b);
  }
  function neFS(raw, n, variant = "normal") {
    const start = Date.now(), g = expand(parse(raw, start), n, variant);
    validate(g, start);
    tick(start);
    const result = write(g);
    remember(result, g);
    return result;
  }
  var escape = (s) => s.replace(/[&<>"']/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" })[c]);
  var html = (s) => '<span style="font-family:inherit;white-space:nowrap">' + escape(s) + "</span>";
  var mainPlain = (raw) => isTop(parse(raw)) ? "Limit of CWY2" : write(parse(raw));
  function optionalView(raw, type) {
    try {
      const g = parse(raw);
      if (isTop(g)) return "Limit";
      return type === "ω-Y 数列" ? numerical(g) : dbms(g, type);
    } catch (e) {
      return "视图暂不可显示：" + (e instanceof Error ? e.message : String(e));
    }
  }
  var equivalent = {
    "ω-Y 数列": {
      plain: (a) => optionalView(a, "ω-Y 数列"),
      from_display: (s) => /^(?:Limit|Top|∞)$/i.test(s.trim()) ? TOP : write(validate(fromNumerical(s), Date.now()))
    }
  };
  for (const name of ["DBMS", "DBMS_MN", "ADBMS"]) equivalent[name] = { plain: (a) => optionalView(a, name) };
  register_notation({
    id: "cwy2-direct-v2",
    name: "CWY2",
    simple_name: "CWY2",
    description: [
      "CWY2：无特殊列的直接祖先词实验版。有限表达式完全由普通列 [父:(词);…] 构成。",
      "例如 wY(1,3) 对应 [][0:(0,1)]。不拆根部，不保存操作历史，不使用特殊标记列。",
      "默认 FS 直接使用统一块复制规则：第零项删末列，后续项逐列前缀增长；纯种子没有移位特判。",
      "基本列编号对齐原 omega-Y 的 weak magma：默认、长展开和 lnz-1 分别对应原页面的三个选项。",
      "长展开会保留最后的降低列，所以长展开第零项不满足删末列；上述前缀约定指默认 FS。",
      "Top/Limit 是外部顶端，其第 n 项为 E(n+1)，对应 wY(1,n+1)；顶端不要求逐项前缀增长。",
      "展开只用原轮廓下方查询、父列合并、skyline 与地址搬运，不恢复山脉，也不调用原 wY FS。",
      "全域精确等价和相应良序性仍待完成证明；有限对照支持继续研究，不代表已证等价或更强。",
      "默认列表之外保留 ω-Y 数列、DBMS、DBMS_MN、ADBMS；不另设仅改写本列地址的重复视图。",
      "勾选“显示图表”并悬停节点可看完整 wY 风格山脉图；显示几何不参与展开或比较。",
      "数值视图使用 BigInt，视图独立限时；无法显示不妨碍核心列表展开，不绘制局部图。",
      "可输入 E3、E3[2]、Top[2]、完整列表或有限自然数；E3[2] 对应 wY(1,2,4)。",
      "旧版另名 CWY2 legacy，保留原字符串和展开编号；新旧是不同内部 ID，不会覆盖彼此。",
      "手写列表只检验结构，不保证属于标准域。原 CWY 与 RWD 文件未改变。"
    ],
    display: { plain: (a) => mainPlain(a), html: (a) => html(mainPlain(a)), from_display: (s) => write(parse(s)) },
    display_equiv: equivalent,
    FS: (a, n) => neFS(a, n),
    FS_alter: (a, n) => neFS(a, n, "alter"),
    FS_short: (a, n) => neFS(a, n, "short"),
    compare: (a, b) => compare2(parse(a), parse(b)),
    is_limit: (a) => {
      const g = parse(a);
      return isTop(g) || !!g.at(-1)?.length;
    },
    init: () => [TOP, "[]", "0"],
    draw_diagram: {
      default_data: { current_equiv: void 0, invert_vertical: false },
      draw_diagram: (a, data) => {
        try {
          const g = parse(a);
          return isTop(g) ? void 0 : mountainDiagram(g, data);
        } catch (e) {
          return { width: 500, height: 40, elements: [], extra_text: [{ text: "完整山脉图暂不可显示：" + (e instanceof Error ? e.message : String(e)), x: 8, y: 20, size: 12, color: { type: "text" }, align: "left" }] };
        }
      },
      handle_action: (data, action) => action.type === "scroll" && ["up", "down"].includes(action.direction) ? { ...data, invert_vertical: action.direction === "down" } : null
    },
    debug: {
      view_stats: viewDebug,
      limits: LIMIT2,
      columns: (s) => structuredClone(parse(s)),
      source_columns: (s) => {
        const g = parse(s);
        if (isTop(g)) throw Error("顶端没有有限列串");
        return structuredClone(g);
      },
      from_source: (g) => write(validate(g, Date.now())),
      minus_source: minusColumn,
      view_from_numerical: fromNumerical,
      cache_stats: () => ({ entries: cache2.size, characters: cacheChars })
    }
  });
})();
