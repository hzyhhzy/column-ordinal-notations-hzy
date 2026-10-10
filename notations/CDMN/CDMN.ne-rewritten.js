/* CDMN — Compact Deep Mountain Notation. Well-ordering remains open. */
(() => {
const module={exports:{}};
"use strict";

// CDMN: compact deep mountain notation, the guarded fixed-block rule.
// This is a new candidate, not an ordinal-equivalent implementation of HMN.
// Prefix-zero revision: at the active copy layer, [0] deletes its last column.
// Enclosing layers recurse at the same index; all positive-index rules are unchanged.
// Limits below are implementation guards, not parts of its mathematical rule.
function createCDMN(options = {}) {
  const limits = { milliseconds: 350, events: 500000, cells: 1200000,
    columns: 1200, depth: 180, ...options };
  let deadline, events, cells, depth;
  const ZERO = [], ONE = [[]];
  function reset() { deadline = Date.now() + limits.milliseconds; events = cells = depth = 0; }
  function enter() {
    if (++events > limits.events || ++depth > limits.depth ||
      (!(events % 128) && Date.now() > deadline)) throw Error("CDMN resource limit");
  }
  function leave(value) { depth--; return value; }
  function reserve(n) { if ((cells += n) > limits.cells) throw Error("CDMN allocation limit"); }
  reset();

  function compare(a, b) {
    enter();
    if (a === b) return leave(0);
    for (let j = 0; j < Math.min(a.length, b.length); j++) {
      for (let k = 0; k < Math.min(a[j].length, b[j].length); k++) {
        const x = a[j][k], y = b[j][k];
        const d = Math.sign(x.p - y.p) || compare(x.r, y.r);
        if (d) return leave(d);
      }
      if (a[j].length !== b[j].length) return leave(Math.sign(a[j].length - b[j].length));
    }
    return leave(Math.sign(a.length - b.length));
  }

  function move(g, cut, distance, memo = new WeakMap()) {
    enter();
    if (!distance) return leave(g);
    if (memo.has(g)) return leave(memo.get(g));
    reserve(1 + g.length + g.reduce((s, c) => s + 2 * c.length, 0));
    const out = g.map(c => c.map(e => ({ p: e.p < cut ? e.p : e.p + distance,
      r: move(e.r, cut, distance, memo) })));
    memo.set(g, out); return leave(out);
  }

  function replaceRow(g, row) {
    const column = g.at(-1), old = column.at(-1);
    reserve(g.length + column.length + 1);
    return [...g.slice(0, -1), [...column.slice(0, -1), ...(row.length ? [{ p: old.p, r: row }] : [])]];
  }

  function prune(g) {
    enter();
    if (!g.length || !g.at(-1).length) return leave(g.slice(0, -1));
    const row = g.at(-1).at(-1).r;
    return leave(row.at(-1).length ? replaceRow(g, prune(row)) : g.slice(0, -1));
  }

  function expand(g, n, context) {
    enter();
    if (!g.length || !g.at(-1).length) return leave(g.slice(0, -1));
    if (!n) return leave(prune(g));
    const all = context.concat(g), m = all.length - 1;
    const control = g.at(-1).at(-1), c = control.p, r = control.r;
    if (r.at(-1).length) return leave(replaceRow(g, expand(r, n, all.slice(0, -1))));

    const distance = m - c;
    if (distance <= 0) throw Error("Invalid CDMN parent");
    if (typeof options.trace === "function") options.trace({ c, m, n, base: context.length });
    if (n > (limits.columns - g.length + 1) / distance) throw Error("CDMN column limit");
    const seam = replaceRow(g, r.slice(0, -1)).at(-1);
    let floor = ZERO;
    for (const e of seam) if (compare(floor, e.r) < 0) floor = e.r;
    for (const e of all[c]) {
      const row = move(e.r, c, distance);
      if (compare(floor, row) < 0) { seam.push({ p: e.p, r: row }); floor = row; }
    }
    const block = [seam, ...move(all.slice(c + 1, m), c, distance)];
    const out = g.slice(0, -1);
    for (let j = 0; j < n; j++) { reserve(block.length); out.push(...move(block, c, j * distance)); }
    return leave(out);
  }

  function legal(g, base) {
    enter();
    return leave(Array.isArray(g) && g.length <= limits.columns && g.every((col, j) =>
      Array.isArray(col) && col.every((e, k) => e && Number.isSafeInteger(e.p) &&
        0 <= e.p && e.p < base + j && Array.isArray(e.r) && e.r.length &&
        (!k || col[k - 1].p > e.p) && legal(e.r, base + j))));
  }

  function seed(n) {
    reset();
    if (!Number.isSafeInteger(n) || n < 0 || n > 100) throw Error("CDMN seed limit");
    if (!n) return ONE;
    let row = ONE;
    for (let j = 1; j < n; j++) row = [[{ p: 0, r: row }]];
    return [[], [{ p: 0, r: row }]];
  }

  function FS(g, n, context = ZERO) {
    reset();
    if (!Number.isSafeInteger(n) || n < 0) throw Error("Invalid CDMN index");
    return expand(g, n, context);
  }

  return { ZERO, ONE, seed, FS,
    cmp: (a, b) => { reset(); return compare(a, b); },
    isLegal: (g, base = 0) => { reset(); return legal(g, base); },
    prune: g => { reset(); return prune(g); } };
}

module.exports = { createCDMN };

// NER adapter. No sharing names and no suspended computations are used.
const H = module.exports.createCDMN({ milliseconds: 450, events: 450000,
  cells: 1000000, columns: 1200, depth: 150 });
const TOP = "Limit of CDMN";
const CAP = { milliseconds: 900, events: 450000, characters: 160000,
  depth: 150, columns: 1200, cacheEntries: 32, cacheNodes: 80000, cacheChars: 650000 };
const cache = new Map(); let cacheNodes = 0, cacheChars = 0;

function memo(key, graph) {
  const seen = new WeakSet(); let nodes = 0;
  function count(g) {
    if (seen.has(g) || nodes > 20000) return;
    seen.add(g); nodes += g.length + 1;
    for (const c of g) for (const e of c) { nodes++; count(e.r); }
  }
  count(graph); if (nodes > 20000 || key.length > CAP.characters) return;
  const previous = cache.get(key);
  if (previous) { cacheNodes -= previous.nodes; cacheChars -= key.length; cache.delete(key); }
  cache.set(key, { graph, nodes }); cacheNodes += nodes; cacheChars += key.length;
  while (cache.size > CAP.cacheEntries || cacheNodes > CAP.cacheNodes || cacheChars > CAP.cacheChars) {
    const first = cache.keys().next().value, item = cache.get(first);
    cacheNodes -= item.nodes; cacheChars -= first.length; cache.delete(first);
  }
}

function run(action) {
  const deadline = Date.now() + CAP.milliseconds; let events = 0;
  const tick = () => {
    if (++events > CAP.events || (!(events % 128) && Date.now() > deadline))
      throw Error("CDMN 输入或显示资源上限；未返回截断式子");
  };
  try { return action(tick); } catch (e) {
    if (/CDMN .*limit/.test(e.message)) throw Error("CDMN 计算资源上限；不表示不终止");
    throw e;
  }
}

function parse(raw, tick) {
  const original = String(raw).trim(); tick();
  if (/^(Limit|Limit of CDMN|Top|T)$/i.test(original)) return null;
  if (cache.has(original)) return cache.get(original).graph;
  if (original.length > CAP.characters) throw Error("CDMN 输入长度上限");
  const s = original.replace(/\s/g, "");
  const route = /^(S(\d+)|Limit|T)((?:\[\d+\])*)$/i.exec(s);
  if (route && (route[2] !== undefined || route[3])) {
    let g = route[2] === undefined ? null : H.seed(Number(route[2]));
    const indices = [...route[3].matchAll(/\[(\d+)\]/g)];
    if (indices.length > 80) throw Error("CDMN 输入路径长度上限");
    for (const index of indices) { tick(); g = g === null ? H.seed(Number(index[1])) : H.FS(g, Number(index[1])); }
    memo(original, g); return g;
  }
  const btbms = s[0] === "(";
  const open = btbms ? "(" : "[", close = btbms ? ")" : "]", separator = btbms ? "," : ";";
  let at = 0, depth = 0;
  const fail = () => { throw Error("CDMN 列表语法错误，位置 " + (at + 1)); };
  function integer() {
    tick(); const begin = at; while (/\d/.test(s[at] ?? "")) at++;
    if (begin === at) fail(); const n = Number(s.slice(begin, at));
    if (!Number.isSafeInteger(n)) fail(); return n;
  }
  function graph() {
    tick(); if (++depth > CAP.depth) throw Error("CDMN 嵌套深度上限");
    if (/\d/.test(s[at] ?? "")) {
      const n = integer(); if (n > CAP.columns) throw Error("CDMN 自然数行长度上限");
      depth--; return Array.from({ length: n }, () => []);
    }
    const out = [];
    while (s[at] === open) {
      tick(); at++; const col = [];
      if (s[at] !== close) for (;;) {
        const p = integer() - (btbms ? 1 : 0); let r;
        if (p < 0) fail();
        if (btbms) {
          r = [[]];
          if (s[at] === "^") {
            at++; const braced = s[at] === "{";
            if (braced) at++;
            r = graph();
            if (braced && s[at++] !== "}") fail();
          }
        } else {
          if (s[at++] !== ":") fail(); r = graph();
        }
        col.push({ p, r });
        if (s[at] !== separator) break; at++;
      }
      if (s[at++] !== close) fail(); out.push(col);
      if (out.length > CAP.columns) throw Error("CDMN 列数上限");
    }
    if (!out.length) fail(); depth--; return out;
  }
  const g = graph(); if (at !== s.length) fail();
  if (!H.isLegal(g)) throw Error("CDMN 父列作用域、非零行或列内父顺序不合法");
  memo(original, g); return g;
}

function format(g, tick, numericRows = true) {
  let characters = 0; const parts = [];
  function write(s) {
    characters += s.length;
    if (characters > CAP.characters) throw Error("CDMN 完整显示长度上限；未返回截断式子");
    parts.push(s);
  }
  function visit(a, row = false) {
    tick();
    if (!a.length) { write("0"); return; }
    if (row && numericRows && a.every(c => !c.length)) { write(String(a.length)); return; }
    for (const col of a) {
      write("["); col.forEach((e, k) => { if (k) write(";"); write(e.p + ":"); visit(e.r, true); }); write("]");
    }
  }
  visit(g); return parts.join("");
}

// A reversible presentation only: superscripts are row graphs, not powers.
function formatBTBMS(g, tick, mode) {
  let characters = 0; const parts = [];
  function write(s) {
    characters += s.length;
    if (characters > CAP.characters) throw Error("CDMN 完整显示长度上限；未返回截断式子");
    parts.push(s);
  }
  function visit(a, row = false) {
    tick();
    if (!a.length) { write("0"); return; }
    if (row && a.every(c => !c.length)) { write(String(a.length)); return; }
    for (const col of a) {
      write("(");
      col.forEach((e, k) => {
        tick(); if (k) write(","); write(String(e.p + 1));
        if (e.r.length === 1 && !e.r[0].length) return;
        write(mode === "html" ? "<sup>" : mode === "latex" ? "^{" : "^");
        visit(e.r, true);
        if (mode === "html") write("</sup>");
        else if (mode === "latex") write("}");
      });
      write(")");
    }
  }
  visit(g); return parts.join("");
}

function plain(raw, full = false) {
  return run(tick => { const g = parse(raw, tick); return g === null ? TOP : format(g, tick, !full); });
}
function FS(raw, n) {
  return run(tick => {
    if (!Number.isSafeInteger(n) || n < 0) throw Error("基本列指标必须是非负安全整数");
    const g = parse(raw, tick), h = g === null ? H.seed(n) : H.FS(g, n);
    const text = format(h, tick); memo(text, h); return text;
  });
}
const escape = s => s.replace(/&/g,"&amp;").replace(/</g,"&lt;").replace(/>/g,"&gt;");
function display(full, name) {
  return { name, plain: s => plain(s, full),
    html: s => '<span style="font-family:inherit;white-space:normal">' + escape(plain(s, full)) + '</span>',
    latex: s => '\\texttt{' + plain(s, full).replace(/[{}\\_]/g, c => '\\' + c) + '}',
    from_display: s => plain(s) };
}
function btbms(raw, mode) {
  return run(tick => {
    const g = parse(raw, tick);
    return g === null ? (mode === "latex" ? "\\mathrm{Limit\\ of\\ CDMN}" : TOP) : formatBTBMS(g, tick, mode);
  });
}
const btbmsDisplay = {
  name: "BTBMS式", plain: s => btbms(s, "plain"),
  html: s => '<span style="font-family:inherit;white-space:normal">' + btbms(s, "html") + '</span>',
  latex: s => btbms(s, "latex"), from_display: s => plain(s)
};

// Exact frozen-prefix column counts on the closed, natural-row fragment.
// K[p][f] clears the strictly increasing skyline of donor column p above f.
// Its prefix sums evaluate an entire height descent, without replaying it.
const countCache = new WeakMap();
function flatCounts(g, options = {}) {
  const cap = { milliseconds: 180, events: 250000, cells: 80000, ...options };
  const deadline = Date.now() + cap.milliseconds;
  let events = 0, cells = 0;
  function limit() { const e = Error("CDMN 计数资源上限"); e.name = "CDMNCountLimit"; throw e; }
  function tick() {
    if (++events > cap.events || (!(events % 128) && Date.now() > deadline)) limit();
  }
  function reserve(n) { if ((cells += n) > cap.cells) limit(); }
  const flat = [];
  for (const col of g) {
    tick(); reserve(col.length + 1); const out = [];
    for (const e of col) {
      tick();
      for (const rowColumn of e.r) { tick(); if (rowColumn.length) return null; }
      out.push({ p: e.p, h: e.r.length });
    }
    flat.push(out);
  }
  const tables = [], sums = [], values = [];
  function work(p, h, floor) {
    tick(); const table = tables[p], sum = sums[p];
    const k = table[floor] ?? 0n;
    const at = u => sum[Math.min(u, sum.length - 1)];
    return BigInt(h) + BigInt(Math.min(h, floor + 1)) * k +
      (h > floor + 1 ? at(h) - at(floor + 1) : 0n);
  }
  let characters = Math.max(0, flat.length - 1);
  for (const col of flat) {
    tick(); let floor = 0, count = 1n, height = 0;
    for (const e of col) {
      count += work(e.p, e.h, floor); floor = Math.max(floor, e.h); height = Math.max(height, e.h);
    }
    const text = String(count); characters += text.length;
    if (characters > CAP.characters) limit(); values.push(count);
    reserve(2 * height + 1);
    const table = [], sum = [0n];
    for (let f = 0; f < height; f++) {
      tick(); let threshold = f, total = 0n;
      for (const e of col) {
        tick();
        if (e.h > threshold) { total += work(e.p, e.h, threshold); threshold = e.h; }
      }
      table.push(total); sum.push(sum.at(-1) + total);
    }
    tables.push(table); sums.push(sum);
  }
  return values;
}
function countResult(g, options) {
  if (g === null) return { values: null, reason: "top" };
  if (!options && countCache.has(g)) return countCache.get(g);
  try {
    const values = flatCounts(g, options);
    const result = { values, reason: values === null ? "nested-rows" : null };
    if (!options) countCache.set(g, result);
    return result;
  } catch (e) {
    if (e.name !== "CDMNCountLimit") throw e;
    return { values: null, reason: "resource-limit" };
  }
}
function counting(raw, mode) {
  return run(tick => {
    const g = parse(raw, tick), result = countResult(g);
    if (result.values !== null) return result.values.map(String).join(",") || "0";
    return g === null ? (mode === "latex" ? "\\mathrm{Limit\\ of\\ CDMN}" : TOP) : formatBTBMS(g, tick, mode);
  });
}
const countDisplay = {
  name: "计数序列", plain: s => counting(s, "plain"),
  html: s => '<span style="font-family:inherit;white-space:normal">' + counting(s, "html") + '</span>',
  latex: s => counting(s, "latex")
  // Display only. Raw legal nonstandard columns need not have unique counts.
};

register_notation({
  id: "cdmn-prefix-fs-unshifted-20261009", name: "CDMN", simple_name: "CDMN",
  description: [
    "紧凑深层山脉候选（Compact Deep Mountain Notation）。每列由父地址p和同类行图R组成；行图只能读取包含它的列之前的上下文。",
    "每一步只在最深活动处降低控制、过滤来源并复制一个固定块；外围只替换该行。比较按列、父地址、递归行图作字典序，不搜索展开路径。",
    "前缀零项规则：在活动复制层，[0]删除该层末列；[n]（n≥1）复制n个固定块，与旧版正指标完全相同，不平移指标。外围只递归替换控制行，因此嵌套展开的[0]不一定删除最外末列。",
    "在活动复制层，基本项从[0]起满足字面前缀关系。相邻基本项的可达性不再是旧版的纯[0]裁剪公式；不将前缀、可达性或字典序下降当作全局良序证明。完全展开的语法节点数满足size(A[n])≤(n+1)size(A)，n≥1。",
    "已有自审纸面等序型结论：S2=()(1^(1))等于普通BMS极限；自然数h≥1时，()(1^h)对应BMS的h行两列种子，特别地()(1^3)=BMS(000)(111)=BO。这不是逐指标基本列相同，也不是Lean认证或整体CDMN良序证明。",
    "输入S2、S3[2][2]、Limit[3]或[][0:[0:1]]。行内数字k代表k个空列；完整列表视图连这一缩写也展开。没有@共享名或隐藏待计算结构。",
    "默认BTBMS式视图用圆括号分列、逗号分记录，父地址显示为p+1，行图放在上标；行图1省略上标。上标不是普通乘方。纯文本示例()(1^3)(2^2,1)；原列表和完整列表仍可切换，输入兼容新旧两种格式。",
    "另有计数序列视图：全部行图都是自然数时，用BigInt精确计算固定前缀下的首接缝删空次数（含最后空列删除），不逐步倒计数；不是对整个式子反复取[0]或[1]的次数。正指标的首个新列减1；[0]删去末个计数。",
    "计数视图遇到嵌套行图、外顶端或计算保护上限时，整个式子回退BTBMS格式，不显示问号或近似数字。计数不参与比较、不提供数字序列的反向解析；回退不等于证明不存在有限计数。",
    "这是改变了HMN展开规则的新候选，不是声称等价的优化。全局良序以及是否超过普通e0MN、strong-e0MN、HMN均未证明。",
    "手输合法式不自动获得标准可达性认证。输入、计算和显示有资源保护；超限不表示不终止。"
  ],
  display: btbmsDisplay, display_equiv: { list: display(false, "列表"), full: display(true, "完整列表"), count: countDisplay },
  FS, FS_alter: FS, FS_short: FS,
  compare: (a,b) => run(tick => { const x=parse(a,tick),y=parse(b,tick);
    return x===null ? (y===null?0:1) : y===null ? -1 : H.cmp(x,y); }),
  is_limit: s => run(tick => { const g=parse(s,tick); return g===null || !!g.at(-1)?.length; }),
  init: () => [TOP, "[]", "0"],
  debug: { core: H, parse: s => run(tick => parse(s,tick)),
    format: (g,full=false) => run(tick => format(g,tick,!full)), limits: CAP,
    counts: (raw,options) => run(tick => countResult(parse(raw,tick),options)),
    cacheStatus: () => ({ entries: cache.size, nodes: cacheNodes, characters: cacheChars }),
    clearCache: () => { cache.clear(); cacheNodes=cacheChars=0; } }
});

})();
