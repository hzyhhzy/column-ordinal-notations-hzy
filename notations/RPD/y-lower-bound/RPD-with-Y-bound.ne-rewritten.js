// Standalone NER: RPD >= Y mountain.
// Bound annotations are display-only; no network or external libraries.
// Standardness of translated annotations is not guaranteed. Bounds are ranks.
// Generated from output/rpd-y-converter-20260914/ner/build-ner.cjs.
(function (register) {
'use strict';
const R = (() => { const module = {exports:{}};
'use strict';

// Current RPD's finite graph rules. Indices are bounded safe integers;
// local counters use BigInt. No standardness test is hidden in validity.
class BudgetError extends Error {
  constructor(message) { super(message); this.name = 'BudgetError'; }
}

class Budget {
  constructor(options = {}) {
    this.maxWidth = options.maxWidth ?? 64;
    this.maxLayer = options.maxLayer ?? 31;
    this.maxAtoms = options.maxAtoms ?? 40000;
    this.maxWork = options.maxWork ?? 2000000;
    this.deadline = Date.now() + (options.ms ?? 2500);
    this.work = 0;
  }
  tick(amount = 1) {
    this.work += amount;
    if (this.work > this.maxWork || Date.now() > this.deadline)
      throw new BudgetError('time/work limit; no partial graph is a result');
  }
  checkGraph(g) {
    this.tick();
    if (!Number.isSafeInteger(g.size) || g.size < 0 || g.size > this.maxWidth)
      throw new BudgetError('width limit or invalid width');
    if (!Array.isArray(g.atoms)) throw new TypeError('atoms must be an array');
    if (g.atoms.length > this.maxAtoms) throw new BudgetError('atom limit');
  }
}

function lex(a, b) {
  for (let i = 0; i < Math.min(a.length, b.length); i++)
    if (a[i] !== b[i]) return a[i] < b[i] ? -1 : 1;
  return Math.sign(a.length - b.length);
}

function normalize(g, budget = new Budget()) {
  budget.checkGraph(g);
  const edges = new Map();
  for (const edge of g.atoms) {
    budget.tick();
    if (!Array.isArray(edge) || edge.length !== 4 ||
        Array.from(edge).some(x => !Number.isSafeInteger(x) || x < 0))
      throw new TypeError('edges must be four nonnegative safe integers');
    const [k, q, p, j] = edge;
    if (!(q <= p && p < j && j < g.size)) throw new RangeError('need q <= p < child < width');
    if (k > budget.maxLayer) throw new BudgetError('layer limit');
    for (let u = 0; u <= q; u++) {
      budget.tick();
      const e = [k, u, p, j]; edges.set(e.join(','), e);
      if (edges.size > budget.maxAtoms) throw new BudgetError('atom limit');
    }
  }
  return {size: g.size, atoms: [...edges.values()].sort(lex)};
}

function seed(k, budget = new Budget()) {
  if (!Number.isSafeInteger(k) || k < 0 || k > budget.maxLayer)
    throw new BudgetError('seed layer limit');
  return normalize({size: 2, atoms: Array.from({length: k + 1}, (_, i) => [i, 0, 0, 1])}, budget);
}

function control(g) {
  const last = g.atoms.filter(e => e[3] === g.size - 1);
  return last.length ? last.reduce((a, b) => lex(a.slice(0, 3), b.slice(0, 3)) < 0 ? b : a) : null;
}

function drop(g) {
  if (!g.size) return {size: 0, atoms: []};
  return {size: g.size - 1, atoms: g.atoms.filter(e => e[3] < g.size - 1)};
}

function fs(g, n, budget = new Budget()) {
  budget.checkGraph(g);
  if (!Number.isSafeInteger(n) || n < 0) throw new TypeError('index must be a nonnegative safe integer');
  const e = control(g);
  if (!g.size || n === 0 || e === null) return drop(g);
  const [K, r, c, x] = e, length = x - c, size = x + n * length;
  budget.checkGraph({size, atoms: []});
  const result = new Map();
  function add(k, q, p, j) {
    for (let u = 0; u <= q; u++) {
      budget.tick();
      const a = [k, u, p, j]; result.set(a.join(','), a);
      if (result.size > budget.maxAtoms) throw new BudgetError('atom limit');
    }
  }
  for (let b = 0; b <= n; b++) {
    const move = i => i < c ? i : i + b * length;
    for (const [k, q, p, j] of g.atoms) {
      budget.tick();
      if (j < x) add(k, move(q), move(p), move(j));
      else if (b < n) {
        const bound = k < K ? move(q) : k === K ? Math.min(move(q), move(r) - 1) : -1;
        if (bound >= 0) add(k, bound, move(p), x + b * length);
      }
    }
  }
  return {size, atoms: [...result.values()].sort(lex)};
}

function localStep(g, budget = new Budget()) {
  budget.tick();
  const e = control(g);
  if (!e) throw new RangeError('T requires a nonempty final column');
  const [K, r, c, x] = e;
  return normalize({size: g.size, atoms: [
    ...g.atoms.filter(([k, q, , j]) => j < x || k < K || k === K && q < r),
    ...g.atoms.filter(a => a[3] === c).map(([k, q, p]) => [k, q, p, x]),
  ]}, budget);
}

function fromPath(path, budget = new Budget()) {
  if (!path.length || !Number.isSafeInteger(path[0])) throw new TypeError('path starts with the TOP seed index');
  let g = seed(path[0], budget);
  for (const op of path.slice(1)) {
    if (typeof op === 'number') g = fs(g, op, budget);
    else if (/^T\d+$/.test(op)) {
      const count = Number(op.slice(1));
      if (!Number.isSafeInteger(count) || count > 10000) throw new BudgetError('T path limit');
      for (let i = 0; i < count; i++) g = localStep(g, budget);
    } else throw new TypeError('path operations are integers or T followed by a count');
  }
  return g;
}

function parseList(text, budget = new Budget()) {
  if (text.length > 200000) throw new BudgetError('input text limit');
  text = text.replace(/\s/g, '');
  if (['', '0', '∅'].includes(text)) return {size: 0, atoms: []};
  const columns = [...text.matchAll(/\[([^\[\]]*)\]/g)];
  if (!columns.length || columns.map(m => m[0]).join('') !== text) throw new TypeError('expected [column][column]...');
  budget.checkGraph({size: columns.length, atoms: []});
  const atoms = [];
  columns.forEach((col, j) => {
    const triples = [...col[1].matchAll(/\((\d+),(\d+),(\d+)\)/g)];
    if (col[1].replace(/\((\d+),(\d+),(\d+)\)/g, '').replace(/[,;]/g, '') !== '')
      throw new TypeError('column entries are (layer,parent,maxRoot)');
    for (const m of triples) atoms.push([Number(m[1]), Number(m[3]), Number(m[2]), j]);
  });
  return normalize({size: columns.length, atoms}, budget);
}

function toList(g) {
  if (!g.size) return '∅';
  const columns = Array.from({length: g.size}, () => new Map());
  for (const [k, q, p, j] of g.atoms) {
    const key = `${k},${p}`, old = columns[j].get(key);
    if (!old || old[2] < q) columns[j].set(key, [k, p, q]);
  }
  return columns.map(c => '[' + [...c.values()].sort((a, b) => lex([b[1], b[0], b[2]], [a[1], a[0], a[2]]))
    .map(e => '(' + e.join(',') + ')').join(',') + ']').join('');
}

function includes(g, h) {
  if (g.size !== h.size) return false;
  const set = new Set(g.atoms.map(e => e.join(',')));
  return h.atoms.every(e => set.has(e.join(',')));
}

function relationParents(g) {
  const groups = new Map();
  for (const [k, q, p, j] of g.atoms) {
    const key = `${k},${q}`;
    if (!groups.has(key)) groups.set(key, Array.from({length: g.size}, () => new Set()));
    groups.get(key)[j].add(p);
  }
  return groups;
}

function checkVF(g, budget = new Budget()) {
  budget.tick();
  const set = new Set(g.atoms.map(e => e.join(',')));
  let V = true, F = true, witnessV = null, witnessF = null;
  for (const [k, q, p, j] of g.atoms) {
    budget.tick();
    if (k > 0 && !set.has([k - 1, p, p, j].join(','))) {
      V = false; witnessV ??= {edge: [k, q, p, j], missing: [k - 1, p, p, j]};
    }
  }
  for (const [key, parents] of relationParents(g)) {
    const reach = Array(g.size).fill(0n);
    for (let j = 0; j < g.size; j++) {
      for (const p of parents[j]) { budget.tick(); reach[j] |= reach[p] | (1n << BigInt(p)); }
      if (!parents[j].size) continue;
      const c = Math.max(...parents[j]);
      for (const p of parents[j]) {
        budget.tick();
        if (p < c && !(reach[c] & (1n << BigInt(p)))) {
          F = false; witnessF ??= {relation: key, child: j, parents: [p, c]};
        }
      }
    }
  }
  return {V, F, witnessV, witnessF};
}

// Add V and missing ancestor-chain witnesses. Root weakening is automatic.
// This is an initial translator closure, NOT a change to RPD.fs.
function saturateVF(input, budget = new Budget(), mode = 'forest') {
  if (!['forest', 'direct'].includes(mode)) throw new TypeError('closure is forest or direct');
  const g = normalize(input, budget), edges = new Map(), queue = [], groups = new Map();
  function add(k, q, p, j) {
    budget.tick();
    const e = [k, q, p, j], key = e.join(',');
    if (edges.has(key)) return;
    if (edges.size >= budget.maxAtoms) throw new BudgetError('saturation atom limit');
    edges.set(key, e); queue.push(e);
    const relation = `${k},${q}`;
    if (!groups.has(relation)) groups.set(relation, Array.from({length: g.size}, () => new Set()));
    groups.get(relation)[j].add(p);
  }
  function hasPath(parents, small, large) {
    const todo = [large], seen = new Set();
    while (todo.length) {
      budget.tick(); const c = todo.pop();
      if (c === small) return true;
      if (c < small || seen.has(c)) continue;
      seen.add(c); for (const p of parents[c]) todo.push(p);
    }
    return false;
  }
  for (const e of g.atoms) add(...e);
  for (let i = 0; i < queue.length; i++) {
    const [k, q, p, j] = queue[i];
    if (q > 0) add(k, q - 1, p, j);
    if (k > 0) add(k - 1, p, p, j);
    const parents = groups.get(`${k},${q}`);
    for (const c of parents[j]) {
      budget.tick(); if (c === p) continue;
      const small = Math.min(p, c), large = Math.max(p, c);
      if (mode === 'direct' || !hasPath(parents, small, large)) add(k, q, small, large);
    }
  }
  const result = {size: g.size, atoms: [...edges.values()].sort(lex)};
  const invariant = checkVF(result, budget);
  if (!invariant.V || !invariant.F || !includes(result, g)) throw new Error('internal saturation invariant failure');
  return {graph: result, added: result.atoms.length - g.atoms.length, invariant};
}

// Exact compressed counts for the finite same-width lowering operation T.
function counts(g, budget = new Budget()) {
  const labels = [...new Map(g.atoms.map(([k, q]) => [`${k},${q}`, [k, q]])).values()].sort(lex);
  const ids = new Map(labels.map((a, i) => [a.join(','), i]));
  const rows = Array.from({length: g.size}, () => new Map()), memo = new Map();
  for (const [k, q, p, j] of g.atoms) {
    const i = ids.get(`${k},${q}`); rows[j].set(i, Math.max(p, rows[j].get(i) ?? -1));
  }
  function lower(c, cut) {
    budget.tick(); const key = `${c}:${cut}`;
    if (memo.has(key)) return memo.get(key);
    const active = new Map(rows[c]); let steps = 0n;
    while (true) {
      budget.tick(); let i = -1;
      for (const a of active.keys()) if (a >= cut && a > i) i = a;
      if (i < 0) break;
      const parent = active.get(i); active.delete(i);
      const sub = lower(parent, i); steps += 1n + sub.steps;
      for (const [a, p] of sub.rest) active.set(a, Math.max(p, active.get(a) ?? -1));
    }
    if (memo.size > 100000) throw new BudgetError('count memo limit');
    const result = {steps, rest: active}; memo.set(key, result); return result;
  }
  return Array.from({length: g.size}, (_, c) => lower(c, 0).steps + 1n);
}

module.exports = {Budget, BudgetError, normalize, seed, control, drop, fs, localStep, fromPath,
  parseList, toList, includes, checkVF, saturateVF, relationParents, counts, lex};

return module.exports; })();
const exact = (() => { const module = {exports:{}};
'use strict';

// Proven, deliberately small equal-value fragment: n and omega * m + n.
// RPD atoms use [layer, root, parent, child], not the display's (k,p,q).
// See EXACT-FRAGMENTS.zh-CN.md for standard-reachability constructions.

const MAX_SAFE_SIZE = BigInt(Number.MAX_SAFE_INTEGER);
const MAX_Y_COLUMNS = 1_000_000n;
const MAX_RPD_ATOMS = 1_000_000n;

function validGraph(graph) {
  if (graph === null || typeof graph !== 'object' ||
      !Number.isSafeInteger(graph.size) || graph.size < 0 ||
      !Array.isArray(graph.atoms)) return false;

  for (const atom of graph.atoms) {
    if (!Array.isArray(atom) || atom.length !== 4 ||
        !Array.from(atom).every(x => Number.isSafeInteger(x) && x >= 0)) return false;
    const [, root, parent, child] = atom;
    if (!(root <= parent && parent < child && child < graph.size)) return false;
  }
  return true;
}

function recognizeRPD(graph) {
  if (!validGraph(graph)) return null;

  if (graph.atoms.length === 0) {
    return { kind: 'finite', n: BigInt(graph.size) };
  }

  // Only this exact full graph is recognized.  In particular, ignoring other
  // atoms or reading just the displayed count sequence would be unsound.
  if (graph.size >= 3 && graph.atoms.length === 1) {
    const [layer, root, parent, child] = graph.atoms[0];
    if (layer === 0 && root === 0 && parent === 1 && child === 2) {
      return { kind: 'omega-plus', n: BigInt(graph.size - 3) };
    }
  }

  // m independent omega blocks, with their common harmless first empty
  // column. Recognize the entire set, not merely a subset of a larger graph.
  const m = graph.atoms.length;
  if (m >= 2 && graph.size >= 2 * m + 1) {
    const children = new Set();
    for (const [layer, root, parent, child] of graph.atoms) {
      if (layer !== 0 || root !== 0 || parent !== child - 1 ||
          child < 2 || child > 2 * m || child % 2 !== 0 || children.has(child)) {
        return null;
      }
      children.add(child);
    }
    return {kind: 'omega-multiple-plus', m: BigInt(m),
      n: BigInt(graph.size) - 2n * BigInt(m) - 1n};
  }
  return null;
}

function recognizeY(sequence) {
  if (!Array.isArray(sequence)) return null;
  // for...of also visits sparse holes as undefined; Array.every would skip
  // them and could misidentify a sparse array as a finite ordinal.
  for (const value of sequence) {
    if (typeof value !== 'bigint' || value <= 0n) return null;
  }

  if (sequence.every(x => x === 1n)) {
    return { kind: 'finite', n: BigInt(sequence.length) };
  }

  if (sequence.length >= 2 && sequence[0] === 1n && sequence[1] === 2n &&
      sequence.slice(2).every(x => x === 1n)) {
    return { kind: 'omega-plus', n: BigInt(sequence.length - 2) };
  }

  let pairs = 0;
  while (sequence[2 * pairs] === 1n && sequence[2 * pairs + 1] === 2n) pairs++;
  if (pairs >= 2 && sequence.slice(2 * pairs).every(x => x === 1n)) {
    return {kind: 'omega-multiple-plus', m: BigInt(pairs),
      n: BigInt(sequence.length - 2 * pairs)};
  }
  return null;
}

function checkedTag(tag) {
  if (tag === null || typeof tag !== 'object' ||
      !['finite', 'omega-plus', 'omega-multiple-plus'].includes(tag.kind) ||
      typeof tag.n !== 'bigint' || tag.n < 0n) {
    throw new TypeError('Expected a supported exact-fragment tag with nonnegative BigInt n.');
  }
  if (tag.kind === 'omega-multiple-plus' &&
      (typeof tag.m !== 'bigint' || tag.m < 2n)) {
    throw new TypeError('omega-multiple-plus requires BigInt m >= 2; use omega-plus for m=1.');
  }
  return tag;
}

function canonicalRPD(tag) {
  checkedTag(tag);
  const m = tag.kind === 'omega-multiple-plus' ? tag.m
    : tag.kind === 'omega-plus' ? 1n : 0n;
  const size = tag.n + (m > 0n ? 2n * m + 1n : 0n);
  if (size > MAX_SAFE_SIZE) {
    throw new RangeError('RPD graph.size exceeds the exact Number integer range.');
  }
  if (m > MAX_RPD_ATOMS) {
    throw new RangeError('Materializing RPD would exceed the 1,000,000-atom output budget.');
  }
  const atoms = [];
  for (let i = 1; i <= Number(m); i++) atoms.push([0, 0, 2 * i - 1, 2 * i]);
  return {
    size: Number(size),
    atoms,
  };
}

function canonicalY(tag) {
  checkedTag(tag);
  const m = tag.kind === 'omega-multiple-plus' ? tag.m
    : tag.kind === 'omega-plus' ? 1n : 0n;
  const size = tag.n + 2n * m;
  if (size > MAX_Y_COLUMNS) {
    throw new RangeError('Materializing Y would exceed the 1,000,000-column output budget.');
  }
  const sequence = Array(Number(size)).fill(1n);
  for (let i = 0; i < Number(m); i++) sequence[2 * i + 1] = 2n;
  return sequence;
}

module.exports = { recognizeRPD, recognizeY, canonicalRPD, canonicalY };

return module.exports; })();
const forest = (() => { const module = {exports:{}};
'use strict';

// Exact equal-rank translation on the smooth-ascent Y / anchored RPD-forest
// fragment. No changes to either notation's expansion rules.
// See FOREST-TRANSLATION.zh-CN.md: E is exact by rank, whereas its uniformly
// anchored auxiliary map F commutes with every nonempty-input FS operation.
const MAX_COLUMNS = 1_000_000;

function analyzeY(sequence) {
  if (!Array.isArray(sequence)) return null;
  if (sequence.length > MAX_COLUMNS) throw new RangeError('Forest translation column budget');
  if (sequence.length && sequence[0] !== 1n) return null;
  const parents = [], stack = [];
  let hasEdge = false;
  for (let j = 0; j < sequence.length; j++) {
    const value = sequence[j];
    if (typeof value !== 'bigint' || value < 1n ||
        (j > 0 && value > sequence[j - 1] + 1n)) return null;
    while (stack.length && sequence[stack.at(-1)] >= value) stack.pop();
    if (value === 1n) parents.push(-1);
    else {
      const parent = stack.at(-1);
      if (parent === undefined || sequence[parent] + 1n !== value) return null;
      parents.push(parent); hasEdge = true;
    }
    stack.push(j);
  }
  return {parents, hasEdge};
}

function anchoredGraph(sequence, analysis) {
  if (sequence.length >= MAX_COLUMNS) throw new RangeError('Forest translation anchored column budget');
  const atoms = [];
  for (let j = 0; j < sequence.length; j++) {
    const parent = analysis.parents[j];
    if (parent >= 0) atoms.push([0, 0, parent + 1, j + 1]);
  }
  atoms.sort((a, b) => a[2] - b[2] || a[3] - b[3]);
  return {size: sequence.length + 1, atoms};
}

// F(empty) is one empty column. This auxiliary map is NOT the equal-rank
// encoder for finite ordinals: rho(F(s)) = 1 + rho(s).
function encodeAnchoredY(sequence) {
  const analysis = analyzeY(sequence);
  return analysis === null ? null : anchoredGraph(sequence, analysis);
}

// E: finite ordinals are handled without the otherwise harmless anchor.
function encodeY(sequence) {
  const analysis = analyzeY(sequence);
  if (analysis === null) return null;
  return analysis.hasEdge ? anchoredGraph(sequence, analysis)
    : {size: sequence.length, atoms: []};
}

function decodeRPD(graph) {
  if (!graph || !Number.isSafeInteger(graph.size) || graph.size < 0 || !Array.isArray(graph.atoms)) return null;
  if (graph.size > MAX_COLUMNS || graph.atoms.length > MAX_COLUMNS) {
    throw new RangeError('Forest translation graph budget');
  }
  if (!graph.atoms.length) return Array(graph.size).fill(1n);
  if (graph.size < 3) return null;

  const parentByColumn = new Map();
  for (const atom of graph.atoms) {
    if (!Array.isArray(atom) || atom.length !== 4 ||
        !Array.from(atom).every(value => Number.isSafeInteger(value) && value >= 0)) return null;
    const [k, q, parent, child] = atom;
    // The control cut must stay strictly to the right of the fixed root 0.
    if (k !== 0 || q !== 0 || parent < 1 || parent >= child || child >= graph.size) return null;
    if (parentByColumn.has(child) && parentByColumn.get(child) !== parent) return null;
    parentByColumn.set(child, parent); // Exact duplicate atoms are harmless.
  }

  const sequence = [];
  for (let j = 1; j < graph.size; j++) {
    const parent = parentByColumn.get(j);
    sequence.push(parent === undefined ? 1n : sequence[parent - 1] + 1n);
  }
  const analysis = analyzeY(sequence);
  if (analysis === null || !analysis.hasEdge) return null;
  for (let j = 0; j < sequence.length; j++) {
    const expected = analysis.parents[j];
    const actual = parentByColumn.get(j + 1);
    if (expected < 0 ? actual !== undefined : actual !== expected + 1) return null;
  }
  return sequence;
}

module.exports = {encodeY, decodeRPD, encodeAnchoredY};

return module.exports; })();

function createBrowserYEngine(options) {
  'use strict';
  options = options ?? {};
  const defaults = {timeoutMs: 100, maxWork: 500000, maxWidth: 64, maxLayers: 32, maxDigits: 2000, maxAtoms: 40000};
  const __limits = {};
  for (const key of Object.keys(defaults)) {
    const value = options[key] ?? (key === 'timeoutMs' ? options.ms : undefined) ?? defaults[key];
    if (!Number.isSafeInteger(value) || value < 1) throw new RangeError(key + ' must be a positive safe integer');
    __limits[key] = value;
  }
  if (__limits.maxDigits > 100000) throw new RangeError('Browser Y maximum digit budget is 100000');
  const __valueLimit = 10n ** BigInt(__limits.maxDigits);
  let __work = 0, __deadline = 0, __badDepth = 0, __expandDepth = 0;
  function __budget(message) {
    const error = new RangeError(message);
    error.name = 'BudgetError'; error.code = 'Y_BUDGET'; throw error;
  }
  function __tick(amount = 1) {
    __work += amount;
    if (__work > __limits.maxWork) __budget('Y browser work limit');
    if (Date.now() > __deadline) __budget('Y browser time limit');
  }
  function __begin() {
    __work = 0; __deadline = Date.now() + __limits.timeoutMs;
    __badDepth = 0; __expandDepth = 0; __tick();
  }
  function __checkValue(value) {
    __tick();
    if (typeof value !== 'bigint' || value < 1n) throw new RangeError('Y values must be positive BigInts');
    if (value >= __valueLimit) __budget('Y browser integer digit limit');
  }
  function __validate(sequence) {
    if (!Array.isArray(sequence)) throw new TypeError('Y sequence must be a BigInt array');
    if (sequence.length > __limits.maxWidth) __budget('Y browser input width limit');
    for (const value of sequence) { __tick(); __checkValue(value); }
  }
  function __checkMountain(mountain) {
    __tick();
    if (mountain.length > __limits.maxLayers) __budget('Y browser mountain row limit');
    for (const row of mountain) {
      __tick();
      if (row.length > __limits.maxWidth) __budget('Y browser mountain width limit');
      for (const entry of row) { __tick(); __checkValue(entry.value); }
    }
    return mountain;
  }
  function calcMountain(sequence) {
    __tick(); return __checkMountain(__original_calcMountain(sequence));
  }
  function getBadRoot(sequence) {
    __tick();
    if (++__badDepth > __limits.maxLayers) { --__badDepth; __budget('Y browser diagonal depth limit'); }
    try { return __original_getBadRoot(sequence); } finally { --__badDepth; }
  }
  function expand(sequence, n, stringify) {
    __tick();
    if (++__expandDepth > __limits.maxLayers) { --__expandDepth; __budget('Y browser expansion depth limit'); }
    try { return __original_expand(sequence, n, stringify); } finally { --__expandDepth; }
  }
var itemSeparatorRegex=/[\t ,]/g
    function parseSequenceElement(s,i){
      if (s.indexOf("v")==-1||!isFinite(Number(s.substring(s.indexOf("v")+1)))){
        var numval=BigInt(s);
        return {
          value:numval,
          position:i,
          parentIndex:-1
        };
      }else{
        return {
          value:BigInt(s.substring(0,s.indexOf("v"))),
          position:i,
          parentIndex:Math.max(Math.min(i-1,Number(s.substring(s.indexOf("v")+1))),-1),
          forcedParent:true
        };
      }
    }
    function __original_calcMountain(s){
      //if (!/^(\d+,)*\d+$/.test(s)) throw Error("BAD");
      var lastLayer;
      if (typeof s=="string"){
        lastLayer=s.split(itemSeparatorRegex).map(parseSequenceElement);
      }
      else lastLayer=s;
      var calculatedMountain=[lastLayer]; //rows
      while (true){__tick();
        //assign parents
        var hasNextLayer=false;
        for (var i=0;i<lastLayer.length;i++){__tick();
          if (lastLayer[i].forcedParent){
            if (lastLayer[i].parentIndex!=-1) hasNextLayer=true;
            continue;
          }
          var p;
          if (calculatedMountain.length==1){
            p=lastLayer[i].position+1;
          }else{
            p=0;
            while (calculatedMountain[calculatedMountain.length-2][p].position<lastLayer[i].position+1) {__tick();p++;}
          }
          while (true){__tick();
            if (p<0) break;
            var j;
            if (calculatedMountain.length==1){
              p--;
              j=p-1;
            }else{ //ignoring
              p=calculatedMountain[calculatedMountain.length-2][p].parentIndex;
              if (p<0) break;
              j=0;
              while (lastLayer[j].position<calculatedMountain[calculatedMountain.length-2][p].position-1) {__tick();j++;}
            }
            if (j<0||j<lastLayer.length-1&&lastLayer[j].position+1!=lastLayer[j+1].position) break;
            if (lastLayer[j].value<lastLayer[i].value){
              lastLayer[i].parentIndex=j;
              hasNextLayer=true;
              break;
            }
          }
        }
        if (!hasNextLayer) break;
        var currentLayer=[];
        if (calculatedMountain.length >= __limits.maxLayers) __budget("Y mountain row limit"); calculatedMountain.push(currentLayer);
        for (var i=0;i<lastLayer.length;i++){__tick();
          if (lastLayer[i].parentIndex!=-1){
            currentLayer.push({value:lastLayer[i].value-lastLayer[lastLayer[i].parentIndex].value,position:lastLayer[i].position-1,parentIndex:-1});
          }
        }
        lastLayer=currentLayer;
      }
      return calculatedMountain;
    }
    function calcDiagonal(mountain){
      var diagonal=[];
      var diagonalTree=[];
      for (var i=0;i<mountain[0].length;i++){__tick(); //only one diagonal exists for each left-side-up diagonal line
        for (var j=mountain.length-1;j>=0;j--){__tick(); //prioritize the top
          var k=0;
          while (mountain[j][k]&&mountain[j][k].position+j<i) {__tick();k++;}
          if (!mountain[j][k]||mountain[j][k].position+j!=i) continue;
          var height=j;
          var lastIndex=k;
          while (true){__tick();
            if (height==0){
              lastIndex=mountain[height][lastIndex].parentIndex;
            }else{
              var l=0; //find right-down
              while (mountain[height-1][l].position!=mountain[height][lastIndex].position+1) {__tick();l++;}
              l=mountain[height-1][l].parentIndex; //go to its parent=left-down
              var m=0; //find up-left of that=left
              while (mountain[height][m].position<mountain[height-1][l].position-1) {__tick();m++;}
              if (mountain[height][m].position==mountain[height-1][l].position-1){ //left exists
                lastIndex=m;
              }else{
                height--;
                lastIndex=l;
              }
            }
            if (!mountain[height][lastIndex]||mountain[height][lastIndex].parentIndex==-1){
              diagonal.push(mountain[j][k].value);
              diagonalTree.push((mountain[height][lastIndex]?mountain[height][lastIndex].position:-1)+height);
              break;
            }
          }
          break;
        }
      }
      var pw=[];
      for (var i=0;i<diagonal.length;i++){__tick();
        var p=-1;
        for (var j=i-1;j>=0;j--){__tick();
          if (diagonal[j]<diagonal[i]){
            p=j;
            break;
          }
        }
        pw.push(p);
      }
      var r=[];
      for (var i=0;i<diagonal.length;i++){__tick();
        var p=i;
        while (true){__tick();
          p=diagonalTree[p];
          if (p<0||diagonal[p]<diagonal[i]) break;
        }
        if (p==pw[i]) r.push(diagonal[i]);
        else r.push(diagonal[i]+"v"+p);
      }
      //console.log(diagonalTree);
      return r.join(",");
    }
    function cloneMountain(mountain){
      var newMountain=[];
      for (var i=0;i<mountain.length;i++){__tick();
        var layer=[];
        for (var j=0;j<mountain[i].length;j++){__tick();
          layer.push({
            value:mountain[i][j].value,
            position:mountain[i][j].position,
            parentIndex:mountain[i][j].parentIndex,
            forcedParent:mountain[i][j].forcedParent
          });
        }
        newMountain.push(layer);
      }
      return newMountain;
    }
    function __original_getBadRoot(s){
      var mountain;
      if (typeof s=="string") mountain=calcMountain(s);
      else mountain=cloneMountain(s);
      var diagonal=calcMountain(calcDiagonal(mountain));
      if (diagonal[0][diagonal[0].length-1].value!=1){
        return getBadRoot(diagonal);
      }else{
        for (var i=mountain.length-1;i>=0;i--){__tick();
          if (mountain[i][mountain[i].length-1].position+i==mountain[0].length-1) return mountain[i-1][mountain[i-1][mountain[i-1].length-1].parentIndex].position+i-1;
        }
      }
    }
    function __original_expand(s,n,stringify){
      var mountain;
      if (typeof s=="string") mountain=calcMountain(s);
      else mountain=cloneMountain(s);
      var result=cloneMountain(mountain);
      if (mountain[0][mountain[0].length-1].parentIndex==-1){
        result[0].pop();
      }else{
        var result=cloneMountain(mountain);
        var cutHeight=mountain.length-1;
        while (mountain[cutHeight][mountain[cutHeight].length-1].position+cutHeight!=mountain[0].length-1) {__tick();cutHeight--;}
        var actualCutHeight=cutHeight;
        var badRootSeam=getBadRoot(mountain);
        var badRootHeight;
        var diagonal=calcMountain(calcDiagonal(mountain));
        var newDiagonal;
        var yamakazi=diagonal[0][diagonal[0].length-1].value==1; //Yamakazi-Funka dualilty
        if (yamakazi){
          newDiagonal=cloneMountain(diagonal);
          newDiagonal[0].pop();
          for (var i=0;i<n;i++){__tick();
            for (var j=badRootSeam;j<mountain[0].length-1;j++){__tick();
              newDiagonal[0].push(newDiagonal[0][j]); //who cares about mountains in diagonal?
            }
          }
          cutHeight--;
          badRootHeight=cutHeight;
        }else{
          newDiagonal=expand(diagonal,n,false);
          badRootHeight=mountain.length-1;
          while (true){__tick();
            var i=0;
            while (mountain[badRootHeight][i]&&mountain[badRootHeight][i].position+badRootHeight<badRootSeam) {__tick();i++;}
            if (mountain[badRootHeight][i]&&mountain[badRootHeight][i].position+badRootHeight==badRootSeam) break;
            badRootHeight--;
          }
        }
        for (var i=0;i<=actualCutHeight;i++) {__tick();result[i].pop();} //cut child
        if (!result[result.length-1].length) result.pop();
        var afterCutHeight=result.length;
        var afterCutMountain=cloneMountain(result);
        var afterCutLength=result[0].length;
        var badRootSeamHeight=afterCutHeight-1;
        while (true){__tick();
          var l=0;
          while (mountain[badRootSeamHeight][l]&&mountain[badRootSeamHeight][l].position+badRootSeamHeight<badRootSeam) {__tick();l++;}
          if (mountain[badRootSeamHeight][l]&&mountain[badRootSeamHeight][l].position+badRootSeamHeight==badRootSeam) break;
          badRootSeamHeight--;
        }
        badRootSeamHeight++;
        //Create Mt.Fuji shell
        for (var i=1;i<=n;i++){__tick(); //iteration
          for (var j=badRootSeam;j<afterCutLength;j++){__tick(); //seam
            var isAscending;
            var p=0; //simplified; may not work
            while (mountain[badRootHeight][p].position+badRootHeight<j) {__tick();p++;}
            if (mountain[badRootHeight][p].position+badRootHeight==j){
              while (true){__tick();
                if (!mountain[badRootHeight][p]||mountain[badRootHeight][p].position+badRootHeight<badRootSeam){
                  isAscending=false;
                  break;
                }
                if (mountain[badRootHeight][p].position+badRootHeight==badRootSeam){
                  isAscending=true;
                  break;
                }
                p=mountain[badRootHeight][p].parentIndex;
              }
            }else{
              isAscending=false;
            }
            var seamHeight=afterCutHeight-1;
            while (true){__tick();
              var l=0;
              while (mountain[seamHeight][l]&&mountain[seamHeight][l].position+seamHeight<j) {__tick();l++;}
              if (mountain[seamHeight][l]&&mountain[seamHeight][l].position+seamHeight==j) break;
              seamHeight--;
            }
            seamHeight++;
            var isReplacingCut=j==badRootSeam;
            //console.log([j,seamHeight]);
            if (isAscending){
              for (var k=0;k<seamHeight+(cutHeight-badRootHeight)*i;k++){__tick();
                if (!result[k]) { if (result.length >= __limits.maxLayers) __budget("Y output row limit"); result.push([]); }
                if (k<badRootHeight){ //Bb
                  var sy=k;
                  var sx;
                  if (isReplacingCut){
                    sx=mountain[sy].length-1;
                  }else{
                    sx=0;
                    while (mountain[sy][sx].position+sy<j) {__tick();sx++;}
                  }
                  var sourceParentIndex=mountain[sy][sx].parentIndex;
                  var parentShifts=i-isReplacingCut;
                  var parentPosition=mountain[sy][sourceParentIndex]?mountain[sy][sourceParentIndex].position+parentShifts*(afterCutLength-badRootSeam)*(mountain[sy][sourceParentIndex].position+sy>=badRootSeam)-(k-sy):-1;
                  var parentIndex=0;
                  while (result[k][parentIndex]&&result[k][parentIndex].position<parentPosition) {__tick();parentIndex++;}
                  if (!result[k][parentIndex]||result[k][parentIndex].position!=parentPosition) parentIndex=-1;
                  result[k].push({
                    value:parentIndex==-1?newDiagonal[0][j+(afterCutLength-badRootSeam)*i].value:NaN,
                    position:j+(afterCutLength-badRootSeam)*i-k,
                    parentIndex:parentIndex,
                    forcedParent:mountain[sy][sx].forcedParent
                  });
                }else if (k<=badRootHeight+(cutHeight-badRootHeight)*(i-isReplacingCut)){ //Br replace
                  var sy=badRootHeight;
                  var sx;
                  if (!yamakazi&&isReplacingCut){
                    sx=mountain[sy].length-1;
                  }else{
                    sx=0;
                    while (mountain[sy][sx].position+sy<j) {__tick();sx++;}
                  }
                  var sourceParentIndex=mountain[sy][sx].parentIndex;
                  var parentShifts=i-isReplacingCut;
                  var parentPosition=mountain[sy][sourceParentIndex]?mountain[sy][sourceParentIndex].position+parentShifts*(afterCutLength-badRootSeam)*(mountain[sy][sourceParentIndex].position+sy>=badRootSeam)-(k-sy):-1;
                  var parentIndex=0;
                  while (result[k][parentIndex]&&result[k][parentIndex].position<parentPosition) {__tick();parentIndex++;}
                  if (!result[k][parentIndex]||result[k][parentIndex].position!=parentPosition) parentIndex=-1;
                  result[k].push({
                    value:parentIndex==-1?newDiagonal[0][j+(afterCutLength-badRootSeam)*i].value:NaN,
                    position:j+(afterCutLength-badRootSeam)*i-k,
                    parentIndex:parentIndex,
                    forcedParent:mountain[sy][sx].forcedParent
                  });
                }else if (isReplacingCut&&k<=badRootHeight+(cutHeight-badRootHeight)*i){ //Br extend
                  var sy=k-(cutHeight-badRootHeight)*(i-1);
                  var sx;
                  if (!yamakazi&&isReplacingCut){
                    sx=mountain[sy].length-1;
                  }else{
                    sx=0;
                    while (mountain[sy][sx].position+sy<j) {__tick();sx++;}
                  }
                  var sourceParentIndex=mountain[sy][sx].parentIndex;
                  var parentShifts=i-isReplacingCut;
                  var parentPosition=mountain[sy][sourceParentIndex]?mountain[sy][sourceParentIndex].position+parentShifts*(afterCutLength-badRootSeam)*(mountain[sy][sourceParentIndex].position+sy>=badRootSeam)-(k-sy):-1;
                  var parentIndex=0;
                  while (result[k][parentIndex]&&result[k][parentIndex].position<parentPosition) {__tick();parentIndex++;}
                  if (!result[k][parentIndex]||result[k][parentIndex].position!=parentPosition) parentIndex=-1;
                  result[k].push({
                    value:parentIndex==-1?newDiagonal[0][j+(afterCutLength-badRootSeam)*i].value:NaN,
                    position:j+(afterCutLength-badRootSeam)*i-k,
                    parentIndex:parentIndex,
                    forcedParent:mountain[sy][sx].forcedParent
                  });
                }else{ //Be
                  //if (isReplacingCut) console.warn("Climbing doesn't all the way. Makes sense.");
                  var sy=k-(cutHeight-badRootHeight)*i;
                  var sx;
                  if (!yamakazi&&isReplacingCut){
                    sx=mountain[sy].length-1;
                  }else{
                    sx=0;
                    while (mountain[sy][sx].position+sy<j) {__tick();sx++;}
                  }
                  var sourceParentIndex=mountain[sy][sx].parentIndex;
                  var parentShifts=i-isReplacingCut;
                  var parentPosition=mountain[sy][sourceParentIndex]?mountain[sy][sourceParentIndex].position+parentShifts*(afterCutLength-badRootSeam)*(mountain[sy][sourceParentIndex].position+sy>=badRootSeam)-(k-sy):-1;
                  var parentIndex=0;
                  while (result[k][parentIndex]&&result[k][parentIndex].position<parentPosition) {__tick();parentIndex++;}
                  if (!result[k][parentIndex]||result[k][parentIndex].position!=parentPosition) parentIndex=-1;
                  result[k].push({
                    value:parentIndex==-1?newDiagonal[0][j+(afterCutLength-badRootSeam)*i].value:NaN,
                    position:j+(afterCutLength-badRootSeam)*i-k,
                    parentIndex:parentIndex,
                    forcedParent:mountain[sy][sx].forcedParent
                  });
                }
              }
            }else{
              if (isReplacingCut) console.warn("Cut child and not connected to bad root. Makes sense.");
              for (var k=0;k<seamHeight;k++){__tick();
                if (!result[k]) { if (result.length >= __limits.maxLayers) __budget("Y output row limit"); result.push([]); }
                //if statement is here to line up indents
                if (true){ //Bb
                  var sy=k;
                  var sx;
                  if (isReplacingCut){
                    sx=mountain[sy].length-1;
                  }else{
                    sx=0;
                    while (mountain[sy][sx].position+sy<j) {__tick();sx++;}
                  }
                  var sourceParentIndex=mountain[sy][sx].parentIndex;
                  var parentShifts=i-isReplacingCut;
                  var parentPosition=mountain[sy][sourceParentIndex]?mountain[sy][sourceParentIndex].position+parentShifts*(afterCutLength-badRootSeam)*(mountain[sy][sourceParentIndex].position+sy>=badRootSeam)-(k-sy):-1;
                  var parentIndex=0;
                  while (result[k][parentIndex]&&result[k][parentIndex].position<parentPosition) {__tick();parentIndex++;}
                  if (!result[k][parentIndex]||result[k][parentIndex].position!=parentPosition) parentIndex=-1;
                  result[k].push({
                    value:parentIndex==-1?newDiagonal[0][j+(afterCutLength-badRootSeam)*i].value:NaN,
                    position:j+(afterCutLength-badRootSeam)*i-k,
                    parentIndex:parentIndex,
                    forcedParent:mountain[sy][sx].forcedParent
                  });
                }
              }
            }
          }
        }
      }
      //Build number from ltr, ttb
      for (var i=result.length-1;i>=0;i--){__tick();
        if (!result[i].length){
          result.pop();
          continue;
        }
        for (var j=0;j<result[i].length;j++){__tick();
          if (typeof result[i][j].value === "bigint") continue;
          var k=0; //find left-up
          while (result[i+1][k].position<result[i][j].position-1) {__tick();k++;}
          if (result[i+1][k].position!=result[i][j].position-1) throw Error("Mountain not complete");
          result[i][j].value=result[i][result[i][j].parentIndex].value+result[i+1][k].value; __checkValue(result[i][j].value);
        }
      }
      var rr;
      if (stringify){
        rr=[];
        for (var i=0;result[0]&&i<result[0].length;i++){__tick();
          rr.push(result[0][i].value+(result[0].forcedParent?"v"+result[0].parentIndex:""));
        }
        rr=rr.join(",");
      }else{
        rr=result;
      }
      return rr;
    }
    
  function __root(row, index) {
    for (let hops = 0; row[index].parentIndex >= 0; hops++) {
      __tick();
      if (hops >= __limits.maxWidth) __budget('Y browser ancestor traversal limit');
      const parent = row[index].parentIndex;
      if (!Number.isSafeInteger(parent) || parent < 0 || parent >= index) throw new RangeError('Invalid Y parent index');
      index = parent;
    }
    return index;
  }
  function fs(sequence, n) {
    __begin(); __validate(sequence);
    if (!Number.isSafeInteger(n) || n < 0) throw new RangeError('Y FS index must be a nonnegative safe integer');
    if (!sequence.length) return [];
    if (n === 0 || sequence.at(-1) === 1n) return sequence.slice(0, -1);
    const mountain = calcMountain(sequence.join(',')), x = mountain[0].length - 1;
    if (mountain[0][x].parentIndex >= 0) {
      const cut = getBadRoot(mountain);
      if (!Number.isSafeInteger(cut) || cut < 0 || cut >= x) throw new RangeError('Invalid Y bad root');
      if (BigInt(x) + BigInt(n) * BigInt(x - cut) > BigInt(__limits.maxWidth)) __budget('Y browser output width limit');
    }
    const result = __checkMountain(expand(mountain, n, false));
    const values = [];
    if (result[0]) for (const entry of result[0]) { __tick(); values.push(entry.value); }
    return values;
  }
  function diagram(sequence) {
    __begin(); __validate(sequence);
    if (!sequence.length) return {size: 0, atoms: []};
    let mountain = calcMountain(sequence.join(','));
    const size = sequence.length, atoms = new Map();
    for (let k = 0; k < __limits.maxLayers; k++) {
      __tick();
      for (let r = 0; r < mountain.length; r++) {
        __tick(); const row = mountain[r];
        for (const entry of row) {
          __tick();
          if (entry.parentIndex < 0) continue;
          const root = __root(row, entry.parentIndex);
          const qMax = row[root].position + r, parent = row[entry.parentIndex].position + r, child = entry.position + r;
          if (!(0 <= qMax && qMax <= parent && parent < child && child < size)) throw new RangeError('Invalid Y canonical edge');
          for (let q = 0; q <= qMax; q++) {
            __tick(); const atom = [k, q, parent, child]; atoms.set(atom.join(','), atom);
            if (atoms.size > __limits.maxAtoms) __budget('Y browser atom limit');
          }
        }
      }
      mountain = calcMountain(calcDiagonal(mountain));
      let terminal = true;
      for (const entry of mountain[0]) { __tick(); if (entry.value !== 1n) { terminal = false; break; } }
      if (terminal) {
        const ordered = [...atoms.values()];
        ordered.sort((a, b) => { __tick(); for (let i = 0; i < 4; i++) { __tick(); if (a[i] !== b[i]) return a[i] - b[i]; } return 0; });
        return {size, atoms: ordered};
      }
    }
    __budget('Y browser canonical diagonal layer limit');
  }
  function control(sequence) {
    __begin(); __validate(sequence);
    if (!sequence.length || sequence.at(-1) === 1n) return null;
    let mountain = calcMountain(sequence.join(','));
    const x = sequence.length - 1;
    if (mountain[0][x].parentIndex < 0) return null;
    for (let k = 0; k < __limits.maxLayers; k++) {
      __tick(); const next = calcMountain(calcDiagonal(mountain));
      if (next[0].at(-1).value !== 1n) { mountain = next; continue; }
      let height = mountain.length - 1;
      while (height >= 0) {
        __tick(); let found = false;
        for (const entry of mountain[height]) { __tick(); if (entry.position + height === x) { found = true; break; } }
        if (found) break;
        height--;
      }
      if (height <= 0) throw new RangeError('Missing Y top edge');
      const r = height - 1, row = mountain[r]; let entry;
      for (const candidate of row) { __tick(); if (candidate.position + r === x) { entry = candidate; break; } }
      if (!entry || entry.parentIndex < 0) throw new RangeError('Missing Y control parent');
      const parent = entry.parentIndex, root = __root(row, parent);
      return [k, row[root].position + r, row[parent].position + r, x];
    }
    __budget('Y browser control diagonal layer limit');
  }
  return {fs, diagram, control};
}

const reconstructCandidate = function reconstructCandidate(g, budget = new R.Budget()) {
  const groups = R.relationParents(g);
  const maxK = Math.max(-1, ...g.atoms.map(e => e[0]));
  const rows = Array.from({length: maxK + 1}, () => Array.from({length: g.size}, () => []));
  for (const [key, parents] of groups) {
    const [k, q] = key.split(',').map(Number);
    const max = parents.map(p => p.size ? Math.max(...p) : -1);
    for (let j = 0; j < g.size; j++) {
      budget.tick(); if (max[j] < 0) continue;
      let root = j;
      while (max[root] >= 0) { budget.tick(); root = max[root]; }
      if (root === q) rows[k][j].push({q, p: max[j]});
    }
  }
  let next = Array(g.size).fill(1n);
  for (let k = maxK; k >= 0; k--) {
    const column = rows[k].map(c => c.sort((a, b) => a.q - b.q));
    const maxHeight = Math.max(0, ...column.map(c => c.length));
    const value = Array.from({length: maxHeight + 1}, () => Array(g.size).fill(null));
    for (let r = maxHeight; r >= 0; r--) for (let j = 0; j < g.size; j++) {
      budget.tick();
      if (column[j].length < r) continue;
      if (column[j].length === r) value[r][j] = next[j];
      else {
        const p = column[j][r].p;
        if (value[r][p] === null || value[r + 1][j] === null)
          return null; // Not even a compatible mountain height/parent array.
        value[r][j] = value[r][p] + value[r + 1][j];
        if (value[r][j].toString().length > 2000) throw new R.BudgetError('reconstructed integer digit limit');
      }
    }
    next = value[0];
  }
  return next;
};
const recursiveBound = (() => {
  const modules = new Map([
    ['./rpd-engine.cjs', {exports:R}],
    ['./converter.cjs', {exports:{reconstructCandidate}}],
    ['./y-engine.cjs', {exports:{createYEngine: options => createBrowserYEngine({
      ...options,timeoutMs:Math.min(25,options.timeoutMs ?? 25),maxWork:75000})}}],
  ]);
  const factories = {"./protected-graph-operators.cjs":function(require,module){
'use strict';

// Finite graph constructors used by the protected-substitution paper.
// They are not new RPD expansion rules. All functions have caller budgets.
const R = require('./rpd-engine.cjs');

function project(input, base, end = input.size, budget = new R.Budget()) {
  budget.checkGraph(input);
  if (!Number.isSafeInteger(base) || base < 1 || base >= end || end > input.size)
    throw new RangeError('Independent unit needs 1 <= base < end <= width');
  return R.normalize({size: end, atoms: input.atoms.filter(e => e[2] >= base && e[3] < end)}, budget);
}

function requireUnit(unit, base, budget = new R.Budget()) {
  budget.checkGraph(unit);
  if (!Number.isSafeInteger(base) || base < 1 || base >= unit.size ||
      unit.atoms.some(e => e[2] < base)) throw new RangeError('Expected a nonempty independent active unit');
}

function insertionImage(unit, base, delta, budget = new R.Budget()) {
  requireUnit(unit, base, budget);
  if (!Number.isSafeInteger(delta) || delta < 0) throw new RangeError('Insertion shift must be nonnegative');
  const move = p => p < base ? p : p + delta;
  return R.normalize({size: unit.size + delta,
    atoms: unit.atoms.map(([k,q,p,j]) => [k,move(q),move(p),move(j)])}, budget);
}

function fixedOffset(graph, base, budget = new R.Budget()) {
  if (!Number.isSafeInteger(base) || base < 1) throw new RangeError('Offset must be positive');
  return R.normalize({size: graph.size + base,
    atoms: graph.atoms.map(([k,q,p,j]) => [k,q+base,p+base,j+base])}, budget);
}

function finiteBeta(unit, base, budget = new R.Budget()) {
  requireUnit(unit, base, budget);
  const end = unit.size;
  return R.normalize({size: end + 3, atoms: unit.atoms.concat(
    [[0,0,base,end], [0,base,end,end+1], [0,0,base,end+2]])}, budget);
}

// depth=1 is K of the paper. K_d envelops every finite K_(d-1)
// iteration for d>=2; K_1 instead envelops finiteBeta iterations.
function cap(unit, base, depth = 1, budget = new R.Budget()) {
  requireUnit(unit, base, budget);
  if (!Number.isSafeInteger(depth) || depth < 1 || depth > budget.maxWidth)
    throw new RangeError('Cap depth must be a positive bounded integer');
  const end = unit.size, atoms = unit.atoms.concat([[0,0,base,end]]);
  for (let i = 0; i <= depth; i++) {
    budget.tick(); atoms.push([0,base+i,end+i,end+i+1]);
  }
  return R.normalize({size: end + depth + 2, atoms}, budget);
}

function forest(unit, base, depths, budget = new R.Budget()) {
  requireUnit(unit, base, budget);
  const atoms = unit.atoms.slice(), stack = [];
  depths.forEach((depth, i) => {
    budget.tick(); const j = unit.size + i;
    if (!Number.isSafeInteger(depth) || depth < 1) throw new RangeError('Forest depth must be positive');
    while (stack.length && stack.at(-1).depth >= depth) stack.pop();
    const p = depth === 1 ? base : stack.at(-1)?.j;
    if (p === undefined || depth > 1 && stack.at(-1).depth !== depth-1)
      throw new RangeError('Non-forest depth word');
    atoms.push([0,0,p,j]); stack.push({depth,j});
  });
  return R.normalize({size: unit.size + depths.length, atoms}, budget);
}

function ancestry(graph, budget = new R.Budget()) {
  const relations = R.relationParents(graph), result = new Map();
  for (const [key, parents] of relations) {
    const rows = Array(graph.size).fill(0n);
    for (let j = 0; j < graph.size; j++) {
      budget.tick();
      for (const p of parents[j]) { budget.tick(); rows[j] |= rows[p] | (1n << BigInt(p)); }
    }
    result.set(key, rows);
  }
  return result;
}

function ancestorCover(target, source, budget = new R.Budget(), prepared) {
  if (target.size !== source.size) return false;
  const relations = prepared ?? ancestry(target, budget);
  return source.atoms.every(([k,q,p,j]) => {
    budget.tick(); return Boolean((relations.get(`${k},${q}`)?.[j] ?? 0n) & (1n << BigInt(p)));
  });
}

module.exports = {project, requireUnit, insertionImage, fixedOffset, finiteBeta, cap, forest,
  ancestry, ancestorCover};

},
"./smooth-y-ordinal.cjs":function(require,module){
'use strict';

// Exact expansion ranks of smooth-ascent Y forests, below epsilon_0.
// A node is omega^(ordered sum of its children); roots are added in order.
// CNF: [] is zero; otherwise [{exponent: CNF, coefficient: positive BigInt},...]
// with strictly decreasing exponents. Returned values are persistent structures:
// callers should not mutate them. No omega power is expanded into an integer.
//
// Why this is the actual FS rank, not just a decreasing bound: on the final
// leaf, deletion gives the predecessor when the final root is a leaf. Otherwise
// Y repeats the parent's preceding child forest n+1 times. At that parent this
// gives the usual cofinal sequence below omega^(beta+1); each ancestor's
// omega-power and each fixed left forest preserve strict increase/cofinality.
// Thus value(s)=sup_n(value(s[n])+1), with value(empty)=0, uniquely the FS rank.

class BudgetError extends RangeError {
  constructor(message) { super(message); this.name = 'BudgetError'; }
}

function createBudget(options = {}) {
  const maxWork = options.maxWork ?? 1000000;
  const deadline = Date.now() + (options.ms ?? 250);
  let work = 0;
  return {
    maxDepth: options.maxDepth ?? 256,
    maxChars: options.maxChars ?? 12000,
    tick(amount = 1) {
      work += amount;
      if (work > maxWork || Date.now() > deadline) throw new BudgetError('Smooth Y ordinal work/time limit');
    },
  };
}

function context(budget) {
  const result = budget ?? createBudget();
  if (!result || typeof result.tick !== 'function') throw new TypeError('Ordinal budget needs tick()');
  return result;
}

function depthGuard(budget, depth) {
  budget.tick();
  if (depth > (budget.maxDepth ?? 256)) throw new BudgetError('Smooth Y ordinal nesting limit');
}

function compareInternal(a, b, budget, depth = 0) {
  depthGuard(budget, depth);
  if (a === b) return 0;
  const length = Math.min(a.length, b.length);
  for (let i = 0; i < length; i++) {
    budget.tick();
    const exponentOrder = compareInternal(a[i].exponent, b[i].exponent, budget, depth + 1);
    if (exponentOrder) return exponentOrder;
    if (a[i].coefficient !== b[i].coefficient) return a[i].coefficient < b[i].coefficient ? -1 : 1;
  }
  return a.length < b.length ? -1 : a.length > b.length ? 1 : 0;
}

function addInternal(a, b, budget) {
  budget.tick();
  if (!a.length) return b;
  if (!b.length) return a;
  const leading = b[0];
  let keep = a.length, order = -1;
  while (keep > 0) {
    budget.tick();
    order = compareInternal(a[keep - 1].exponent, leading.exponent, budget);
    if (order >= 0) break;
    keep--;
  }
  const result = [];
  const merge = keep > 0 && order === 0;
  for (let i = 0; i < keep - Number(merge); i++) { budget.tick(); result.push(a[i]); }
  if (merge) {
    result.push({exponent: leading.exponent, coefficient: a[keep - 1].coefficient + leading.coefficient});
  }
  for (let i = Number(merge); i < b.length; i++) { budget.tick(); result.push(b[i]); }
  return result;
}

function natural(value) {
  if (typeof value !== 'bigint' || value < 0n) throw new TypeError('Natural coefficient must be a nonnegative BigInt');
  return value === 0n ? [] : [{exponent: [], coefficient: value}];
}

function omegaPow(exponent) {
  if (!Array.isArray(exponent)) throw new TypeError('Exponent must be a canonical CNF');
  return [{exponent, coefficient: 1n}];
}

function rank(sequence, budget) {
  const b = context(budget);
  if (!Array.isArray(sequence)) throw new TypeError('Expected a smooth Y BigInt array');
  if (sequence.length && sequence[0] !== 1n) throw new RangeError('Smooth Y must start with 1');
  // The first frame is an artificial root representing the whole forest.
  // All other frames are open actual nodes, with their child CNF accumulated.
  const frames = [{sum: []}];
  function closeNode() {
    b.tick();
    const closed = frames.pop();
    const parent = frames[frames.length - 1];
    parent.sum = addInternal(parent.sum, omegaPow(closed.sum), b);
  }
  for (let j = 0; j < sequence.length; j++) {
    b.tick();
    const value = sequence[j];
    if (typeof value !== 'bigint' || value < 1n) throw new TypeError('Smooth Y values must be positive BigInts');
    if (j > 0 && value > sequence[j - 1] + 1n) throw new RangeError('Y is outside the smooth-ascent forest fragment');
    if (value > BigInt(b.maxDepth ?? 256)) throw new BudgetError('Smooth Y ordinal nesting limit');
    const depth = Number(value);
    while (frames.length > depth) { b.tick(); closeNode(); }
    frames.push({sum: []});
  }
  while (frames.length > 1) { b.tick(); closeNode(); }
  return frames[0].sum;
}

function compare(a, b, budget) { return compareInternal(a, b, context(budget)); }
function add(a, b, budget) { return addInternal(a, b, context(budget)); }

function format(value, budget) {
  const b = context(budget), maxChars = b.maxChars ?? 12000;
  if (!Number.isSafeInteger(maxChars) || maxChars < 1 || maxChars > 100000) {
    throw new RangeError('Ordinal format maxChars must be 1..100000');
  }
  const coefficientLimit = 10n ** BigInt(maxChars);
  const pieces = []; let chars = 0;
  function text(part) {
    b.tick(); chars += part.length;
    if (chars > maxChars) throw new BudgetError('Smooth Y ordinal format length limit');
    pieces.push(part);
  }
  function coefficient(number) {
    if (typeof number !== 'bigint' || number < 1n) throw new TypeError('Invalid CNF coefficient');
    if (number >= coefficientLimit) throw new BudgetError('Smooth Y ordinal coefficient display limit');
    text(number.toString());
  }
  function isOne(alpha) {
    return alpha.length === 1 && alpha[0].exponent.length === 0 && alpha[0].coefficient === 1n;
  }
  function isOmega(alpha) {
    return alpha.length === 1 && alpha[0].coefficient === 1n && isOne(alpha[0].exponent);
  }
  function output(alpha, depth) {
    depthGuard(b, depth);
    if (!alpha.length) { text('0'); return; }
    for (let i = 0; i < alpha.length; i++) {
      b.tick(); if (i) text('+');
      const {exponent, coefficient: multiple} = alpha[i];
      if (!exponent.length) { coefficient(multiple); continue; }
      text('ω');
      if (!isOne(exponent)) {
        text('^');
        const simple = exponent.length === 1 && exponent[0].exponent.length === 0 || isOmega(exponent);
        if (!simple) text('(');
        output(exponent, depth + 1);
        if (!simple) text(')');
      }
      if (multiple !== 1n) { text('*'); coefficient(multiple); }
    }
  }
  output(value, 0);
  return pieces.join('');
}

module.exports = {rank, compare, format, add, natural, omegaPow, createBudget, BudgetError};

},
"./bms-macro-bound.cjs":function(require,module){
'use strict';

// Structural certificates for the BMS macro pattern. The BMS/Y(1,3) bridge is
// a separate paper argument, not a theorem checked by this finite program.
// Every preparation is an exact compression of original RPD T steps; no
// replacement expansion rule and no fallback lower bound is introduced.
const R = require('./rpd-engine.cjs');
const DEFAULTS = Object.freeze({ms: 100, maxWork: 300000, maxWidth: 64, maxLayer: 31,
  maxAtoms: 40000, maxMemo: 10000});

function makeBudget(options = {}) {
  return options && typeof options.tick === 'function' && typeof options.checkGraph === 'function'
    ? options : new R.Budget({...DEFAULTS, ...options});
}

function cloneRow(row, budget) {
  const result = new Map();
  for (const [label, parents] of row) {
    budget.tick(); const copy = new Set();
    for (const parent of parents) { budget.tick(); copy.add(parent); }
    result.set(label, copy);
  }
  return result;
}

function makePreparationContext(graph, budget, maxMemo = DEFAULTS.maxMemo) {
  const labelsByKey = new Map();
  for (const [k, q] of graph.atoms) { budget.tick(); labelsByKey.set(`${k},${q}`, [k, q]); }
  const labels = [...labelsByKey.values()].sort((a, b) => { budget.tick(); return R.lex(a, b); });
  const ids = new Map();
  labels.forEach((label, index) => { budget.tick(); ids.set(label.join(','), index); });
  const rows = [], high = [];
  for (let j = 0; j < graph.size; j++) { budget.tick(); rows.push(new Map()); high.push(-1); }
  for (const [k, q, p, j] of graph.atoms) {
    budget.tick(); const id = ids.get(`${k},${q}`);
    if (!rows[j].has(id)) rows[j].set(id, new Set());
    rows[j].get(id).add(p); high[j] = Math.max(high[j], id);
  }
  function maximum(parents) {
    let result = -1;
    for (const p of parents) { budget.tick(); result = Math.max(result, p); }
    return result;
  }
  function merge(active, rest) {
    for (const [label, parents] of rest) {
      budget.tick();
      if (!active.has(label)) active.set(label, new Set());
      for (const p of parents) { budget.tick(); active.get(label).add(p); }
    }
  }
  function isAncestor(label, ancestor, child) {
    const pending = [child], seen = new Set();
    while (pending.length) {
      budget.tick(); const at = pending.pop();
      if (seen.has(at)) continue;
      seen.add(at);
      for (const parent of rows[at].get(label) ?? []) {
        budget.tick();
        if (parent === ancestor) return true;
        if (parent > ancestor) pending.push(parent);
      }
    }
    return false;
  }
  const memo = new Map();
  function normalise(column, threshold) {
    budget.tick();
    if (high[column] < threshold) return {steps: 0n, rest: rows[column]};
    const key = `${column}:${threshold}`;
    if (memo.has(key)) return memo.get(key);
    const active = cloneRow(rows[column], budget); let steps = 0n;
    for (let label = high[column]; label >= threshold; label--) {
      budget.tick(); const parents = active.get(label);
      if (!parents) continue;
      const parent = maximum(parents); active.delete(label);
      if (!(0 <= parent && parent < column)) throw new RangeError('Preparation encountered a non-left parent');
      const sub = normalise(parent, label);
      steps += 1n + sub.steps; merge(active, sub.rest);
    }
    if (memo.size >= maxMemo) throw new R.BudgetError('BMS macro preparation memo limit');
    const result = {steps, rest: active}; memo.set(key, result); return result;
  }
  function prepare(target, width = graph.size) {
    budget.tick();
    if (!Array.isArray(target) || target.length !== 4 ||
        Array.from(target).some(n => !Number.isSafeInteger(n) || n < 0)) throw new TypeError('Expected target [k,q,p,x]');
    if (!Number.isSafeInteger(width) || width < 1 || width > graph.size) throw new RangeError('Invalid preparation prefix width');
    const [k, q, parent, x] = target;
    if (x !== width - 1 || !(q <= parent && parent < x)) throw new RangeError('Invalid preparation target coordinates');
    const label = ids.get(`${k},${q}`);
    // This is the deliberate extension of the old routine: an actual positive
    // same-label path suffices; target need not initially be a direct edge.
    if (label === undefined || !isAncestor(label, parent, x)) throw new RangeError('Preparation target is not an ancestor');
    const initial = normalise(x, label + 1), active = cloneRow(initial.rest, budget);
    let steps = initial.steps, iterations = 0, previous = x;
    while (true) {
      budget.tick(); const parents = active.get(label);
      if (!parents || !parents.size) throw new Error('Preparation lost the promised target ancestry');
      const current = maximum(parents);
      if (current === parent) break;
      if (!(parent < current && current < previous)) throw new Error('Preparation crossed the promised target');
      previous = current; active.delete(label);
      const sub = normalise(current, label + 1);
      steps += 1n + sub.steps; merge(active, sub.rest); iterations++;
    }
    const atoms = [];
    for (const atom of graph.atoms) { budget.tick(); if (atom[3] < x) atoms.push(atom.slice()); }
    for (const [id, parents] of active) {
      for (const p of parents) { budget.tick(); atoms.push([...labels[id], p, x]); }
    }
    const result = R.normalize({size: width, atoms}, budget);
    if (R.lex(R.control(result) ?? [], target) !== 0) throw new Error('Compressed preparation did not expose the target');
    return {graph: result, steps, iterations, memoEntries: memo.size};
  }
  return {prepare};
}

function requireVF(graph, budget) {
  const invariant = R.checkVF(graph, budget);
  if (!invariant.V || !invariant.F) throw new RangeError('BMS macro requires a valid V/F graph');
  return invariant;
}

function prepareAncestor(input, target, options = {}) {
  const budget = makeBudget(options), graph = R.normalize(input, budget);
  requireVF(graph, budget);
  return makePreparationContext(graph, budget, options.maxMemo ?? DEFAULTS.maxMemo).prepare(target);
}

function qZeroAncestry(graph, budget) {
  const parents = Array.from({length: graph.size}, () => []), ancestors = Array(graph.size).fill(0n);
  for (const [k, q, p, j] of graph.atoms) { budget.tick(); if (k === 0 && q === 0) parents[j].push(p); }
  for (let j = 0; j < graph.size; j++) {
    budget.tick();
    for (const p of parents[j]) { budget.tick(); ancestors[j] |= ancestors[p] | (1n << BigInt(p)); }
  }
  return ancestors;
}

function findBMSMacro(input, options = {}) {
  const budget = makeBudget(options), start = Date.now();
  try {
    const graph = R.normalize(input, budget), invariant = R.checkVF(graph, budget);
    if (!invariant.V || !invariant.F) return {status: 'unknown', reason: 'requires-VF', invariant};
    const ancestors = qZeroAncestry(graph, budget);
    const sourceEdges = [];
    for (const atom of graph.atoms) { budget.tick(); if (atom[0] === 0 && atom[3] === atom[2] + 1) sourceEdges.push(atom); }
    const preparation = makePreparationContext(graph, budget, options.maxMemo ?? DEFAULTS.maxMemo);
    let scanned = 0;
    // Global priority is the smallest b; then the shortest original prefix.
    for (let b = 0; b < graph.size - 1; b++) {
      budget.tick(); const bit = 1n << BigInt(b);
      for (let width = Math.max(3, b + 2); width <= graph.size; width++) {
        budget.tick(); const x = width - 1;
        if (!(ancestors[x] & bit)) continue;
        scanned++;
        // T never changes this internal source edge, so reject impossible
        // prefixes cheaply before invoking compressed preparation.
        let sourceEdge = null;
        for (const edge of sourceEdges) {
          budget.tick(); if (edge[1] >= b && edge[3] < x) { sourceEdge = edge; break; }
        }
        if (!sourceEdge) continue;
        const target = [0, 0, b, x], prepared = preparation.prepare(target, width);
        const certificate = {
          kind: 'bms-macro', version: 1, prefixWidth: width,
          deletedSuffixColumns: graph.size - width, b, target,
          sourceEdge: sourceEdge.slice(), preparationSteps: prepared.steps, blockLength: x - b,
        };
        return {status: 'found', method: 'bms-macro', yLowerBound: [1n, 3n], certificate,
          preparedGraph: prepared.graph, proofStatus: 'finite-structural-certificate; separate paper bridge; not Lean-certified',
          stats: {scanned, work: budget.work, memoEntries: prepared.memoEntries, elapsedMs: Date.now() - start}};
      }
    }
    return {status: 'unknown', reason: 'no-macro-found', stats: {scanned, work: budget.work, elapsedMs: Date.now() - start}};
  } catch (error) {
    if (error.name === 'BudgetError') return {status: 'unknown', reason: 'budget', detail: error.message};
    throw error;
  }
}

// Recompute the structural witness against the original graph. This does not
// purport to verify the separate BMS seed/limit comparison theorem.
function verifyCertificate(input, certificate, options = {}) {
  const budget = makeBudget(options);
  try {
    const graph = R.normalize(input, budget); requireVF(graph, budget);
    if (!certificate || certificate.kind !== 'bms-macro' || certificate.version !== 1) return {status: 'invalid', reason: 'certificate-kind'};
    const {prefixWidth: width, b, sourceEdge, preparationSteps, blockLength} = certificate;
    if (!Number.isSafeInteger(width) || width < 3 || width > graph.size ||
        !Number.isSafeInteger(b) || b < 0 || b >= width - 1 ||
        certificate.deletedSuffixColumns !== graph.size - width || blockLength !== width - 1 - b ||
        typeof preparationSteps !== 'bigint' || preparationSteps < 0n ||
        !Array.isArray(sourceEdge) || sourceEdge.length !== 4 ||
        Array.from(sourceEdge).some(n => !Number.isSafeInteger(n) || n < 0)) return {status: 'invalid', reason: 'certificate-fields'};
    const [k, q, a, child] = sourceEdge, target = [0, 0, b, width - 1];
    if (k !== 0 || q < b || q > a || child !== a + 1 || child >= width - 1 ||
        !Array.isArray(certificate.target) || R.lex(certificate.target, target) !== 0) return {status: 'invalid', reason: 'macro-geometry'};
    const prepared = makePreparationContext(graph, budget, options.maxMemo ?? DEFAULTS.maxMemo).prepare(target, width);
    if (prepared.steps !== preparationSteps) return {status: 'invalid', reason: 'preparation-step-count'};
    if (!prepared.graph.atoms.some(edge => R.lex(edge, sourceEdge) === 0)) return {status: 'invalid', reason: 'source-edge-absent'};
    return {status: 'valid', structuralOnly: true, preparedGraph: prepared.graph, preparationSteps: prepared.steps};
  } catch (error) {
    if (error.name === 'BudgetError') return {status: 'unknown', reason: 'budget', detail: error.message};
    if (error instanceof TypeError || error instanceof RangeError) return {status: 'invalid', reason: error.message};
    throw error;
  }
}

module.exports = {findBMSMacro, prepareAncestor, verifyCertificate, DEFAULTS};

},
"./protected-y-embedding.cjs":function(require,module){
'use strict';

// Root-aware weighted canonical Y diagrams. This is a compiler/recognizer
// helper, not a change to Y or RPD. See the separate proof obligations.
const R=require('./rpd-engine.cjs');
const P=require('./protected-graph-operators.cjs');

function protectedWord(t) {
  return !t.length || t[0]===1n && t.every((x,i)=>typeof x==='bigint' && x>0n &&
    (i===0 || t[i-1]!==1n || x===1n || x===2n));
}
function substitute(B,t) {return t.flatMap(x=>x===1n?B:[x]);}

function embedding(t,unit,base,Y,budget=new R.Budget()) {
  P.requireUnit(unit,base,budget);
  if(!protectedWord(t)) throw new RangeError('Y word is not root-protected');
  const width=unit.size-base,positions=[],atoms=[];let cursor=base;
  for(const value of t) {
    budget.tick();positions.push(cursor);
    if(value===1n) {atoms.push(...P.insertionImage(unit,base,cursor-base,budget).atoms);cursor+=width;}
    else cursor++;
  }
  const q=Y.diagram(t),maxima=new Map();
  for(const [k,r,p,j] of q.atoms) {
    budget.tick();const key=[k,p,j].join(',');
    const old=maxima.get(key);if(!old || old[1]<r) maxima.set(key,[k,r,p,j]);
  }
  for(const [k,r,p,j] of maxima.values()) {
    if(t[j]===1n) throw Error('Y root unexpectedly has an incoming edge');
    if(t[r]===1n && k!==0) throw Error('Positive extraction root crossed the protected 2');
    if(t[p]===1n && (k!==0 || t[r]!==1n)) throw Error('Positive Y relation points to a protected unit');
    atoms.push([k,t[r]===1n?0:positions[r],positions[p],positions[j]]);
  }
  const graph=R.normalize({size:cursor,atoms},budget);
  return {graph,positions};
}

function encodedControl(t,positions,Y) {
  const e=Y.control(t);if(!e) return null;
  const [k,r,p,j]=e;
  return [k,t[r]===1n?0:positions[r],positions[p],positions[j]];
}

// Only generates a candidate: artificial roots and extra edges can make
// reconstruction misleading. The forward embedding must always be checked.
function quotientCandidateGraph(input,base,unitEnd,budget=new R.Budget()) {
  const atoms=[],move=p=>p===base?0:p-unitEnd+1;
  for(const [k,q,p,j] of input.atoms) {
    budget.tick();if(j<unitEnd || p!==base && p<unitEnd) continue;
    if(k===0 && q===0) atoms.push([0,0,move(p),move(j)]);
    if(q>=unitEnd && p>=unitEnd) atoms.push([k,move(q),move(p),move(j)]);
  }
  return R.normalize({size:input.size-unitEnd+1,atoms},budget);
}

module.exports={protectedWord,substitute,embedding,encodedControl,quotientCandidateGraph};

},
"./star-beta-operators.cjs":function(require,module){
'use strict';
const R=require('./rpd-engine.cjs');
const P=require('./protected-graph-operators.cjs');

// F followed by m level-1 caps rooted at its first appended column.
function starBeta(unit,base,m,budget=new R.Budget()) {
  if(!Number.isSafeInteger(m)||m<0||m>budget.maxWidth)throw new RangeError('Invalid star count');
  const F=P.finiteBeta(unit,base,budget),atoms=F.atoms.slice();
  for(let i=0;i<m;i++)atoms.push([0,1,unit.size,F.size+i]);
  return R.normalize({size:F.size+m,atoms},budget);
}

function rootedForest(core,root,depths,budget=new R.Budget()) {
  const atoms=core.atoms.slice(),stack=[];
  for(let i=0;i<depths.length;i++) {
    budget.tick();const depth=depths[i],j=core.size+i;
    if(!Number.isSafeInteger(depth)||depth<1)throw new RangeError('Invalid forest depth');
    while(stack.length&&stack.at(-1).depth>=depth)stack.pop();
    const p=depth===1?root:stack.at(-1)?.j;
    if(p===undefined || depth>1&&stack.at(-1).depth!==depth-1)throw new RangeError('Non-forest');
    atoms.push([0,0,p,j]);stack.push({depth,j});
  }
  return R.normalize({size:core.size+depths.length,atoms},budget);
}
function starCore(core,root,count=1,budget=new R.Budget()) {
  if(!Number.isSafeInteger(count)||count<0||count>budget.maxWidth||root<1||root>=core.size)
    throw new RangeError('Invalid core star');
  return R.normalize({size:core.size+count,atoms:core.atoms.concat(
    Array.from({length:count},(_,i)=>[0,1,root,core.size+i]))},budget);
}
module.exports={starBeta,rootedForest,starCore};

},
"./dilated-geometric-y.cjs":function(require,module){
'use strict';

// A small all-layer inverse rule. Missing physical columns are gaps in a
// coordinate embedding, not deleted vertices with unchanged root labels.
const P=require('./protected-graph-operators.cjs');

function word(level,length) {
  const ratio=BigInt(level+2),out=[1n];
  while(out.length<length) out.push(out.at(-1)*ratio);
  return out;
}

function find(graph,base,end,budget) {
  const edges=graph.atoms.filter(([k,q,p,j])=>q===p && p>=base && j<end);
  const highest=Math.max(-1,...edges.map(e=>e[0])),found=[];
  for(let level=0;level<=highest;level++) {
    budget.tick();
    const length=Array(end).fill(1),previous=Array(end).fill(-1);
    for(let j=base+1;j<end;j++) for(const [k,q,p,child] of edges) {
      budget.tick();
      if(child===j && k>=level && length[p]+1>length[j]) {
        length[j]=length[p]+1;previous[j]=p;
      }
    }
    if(length[end-1]<2)continue;
    const positions=[];
    for(let j=end-1;j>=0;j=previous[j])positions.push(j);
    positions.reverse();
    found.push({level,positions,word:word(level,positions.length)});
  }
  return found;
}

// The caller checks VF. Then one highest-layer full-root ancestor chain
// supplies every smaller layer/root required by the geometric Y diagram.
function verify(graph,base,end,certificate,budget) {
  const {level,positions}=certificate;
  if(!Number.isSafeInteger(level)||level<0||level>budget.maxLayer ||
      !Array.isArray(positions)||positions.length<2||positions.length>graph.size||
      positions.some((p,i)=>!Number.isSafeInteger(p)||p<base||p>=end||i>0&&p<=positions[i-1])||
      positions.at(-1)!==end-1)return false;
  const expected=word(level,positions.length);
  if(certificate.word.length!==expected.length||!expected.every((x,i)=>x===certificate.word[i]))return false;
  const reach=P.ancestry(graph,budget);
  for(let i=1;i<positions.length;i++) {
    budget.tick();const p=positions[i-1],j=positions[i];
    if(!((reach.get(`${level},${p}`)?.[j]??0n)&(1n<<BigInt(p))))return false;
  }
  return true;
}

module.exports={word,find,verify};

},
"./y-reachability-certificate.cjs":function(require,module){
'use strict';

// Fast finite-target reachability certificates. Large fixed-width T runs
// are represented by the already proved Y first-seam decrement theorem.
// "unreachable" is not a reverse inequality of expansion ranks.
const {createYEngine}=require('./y-engine.cjs');

function terminalPrefixLE(target,source) {
  if(!target.length) return true;
  if(target.length>source.length) return false;
  return target.slice(0,-1).every((x,i)=>x===source[i]) && target.at(-1)<=source[target.length-1];
}

function proveReachable(target,source,options={}) {
  const limits={ms:100,maxWidth:128,maxLayers:48,maxStages:128,...options};
  const Y=options.Y??createYEngine({maxWidth:limits.maxWidth,maxLayers:limits.maxLayers,
    timeoutMs:Math.min(limits.ms,100)}),started=Date.now(),trace=[];
  const legal=s=>Array.isArray(s) && s.length<=limits.maxWidth &&
    (!s.length || s[0]===1n && s.every(x=>typeof x==='bigint' && x>0n));
  if(!legal(target) || !legal(source)) throw new RangeError('Expected bounded legal Y words');
  let current=source.slice(),stages=0;
  const result=status=>({status,trace,stages,elapsedMs:Date.now()-started,
    comparison:status==='reachable'?'rho_Y(target) <= rho_Y(source)':'no rank inequality asserted'});
  function tick(){if(Date.now()-started>limits.ms || stages>limits.maxStages) {
    const e=new RangeError('Reachability budget');e.name='BudgetError';throw e;}}
  function drop(width) {
    if(current.length>width){trace.push({op:'dropTo',width});current=current.slice(0,width);}
  }
  function lower(value) {
    if(current.at(-1)>value) {
      trace.push({op:'lowerLast',from:current.at(-1),to:value,repetitions:current.at(-1)-value});
      current=current.slice(0,-1).concat(value);
    }
  }
  try {
    while(true) {
      tick();stages++;
      if(terminalPrefixLE(target,current)) {drop(target.length);if(target.length)lower(target.at(-1));return result('reachable');}
      let first=0;while(first<Math.min(target.length,current.length) && target[first]===current[first])first++;
      if(first===Math.min(target.length,current.length) || target[first]>current[first]) return result('unreachable');
      drop(first+1);lower(target[first]+1n);
      const control=Y.control(current);
      if(!control || control[3]!==first) throw Error('Missing positive Y control');
      const block=first-control[2],index=Math.ceil((target.length-first)/block);
      const next=Y.fs(current,index);tick();
      if(next.length<target.length || !next.slice(0,first+1).every((x,i)=>x===target[i]))
        throw Error('Y first seam/length identity failed');
      trace.push({op:'expand',index});current=next;drop(target.length);
    }
  } catch(error) {
    if(error.name==='BudgetError') return {...result('unknown'),reason:'budget'};
    throw error;
  }
}

function verifyReachability(target,source,proof,options={}) {
  const Y=options.Y??createYEngine({maxWidth:options.maxWidth??128,maxLayers:48,timeoutMs:100});
  const start=Date.now(),ms=options.ms??200;let current=source.slice();
  if(!proof || proof.status!=='reachable' || !Array.isArray(proof.trace) || proof.trace.length>512) return false;
  for(const step of proof.trace) {
    if(Date.now()-start>ms)return false;
    if(step.op==='dropTo') {
      if(!Number.isSafeInteger(step.width) || step.width<0 || step.width>current.length)return false;
      current=current.slice(0,step.width);
    } else if(step.op==='lowerLast') {
      if(current.length<2 || typeof step.to!=='bigint' || step.to<1n || step.from!==current.at(-1) ||
          step.to>=step.from || step.repetitions!==step.from-step.to)return false;
      // This exact compression cites Numeric.expandValues_first_seam_succ.
      current=current.slice(0,-1).concat(step.to);
    } else if(step.op==='expand') {
      if(!Number.isSafeInteger(step.index) || step.index<0)return false;
      current=Y.fs(current,step.index);
    } else return false;
  }
  return current.length===target.length && current.every((x,i)=>x===target[i]);
}

module.exports={terminalPrefixLE,proveReachable,verifyReachability};

},
"./recursive-y-lower-bound.cjs":function(require,module){
'use strict';

// Bounded, proof-carrying research prototype. No NER asset is overwritten.
// A successful certificate checks finite hypotheses of the paper lemmas;
// it is not an automated proof of those lemmas and is not Lean-certified.
const R = require('./rpd-engine.cjs');
const P = require('./protected-graph-operators.cjs');
const O = require('./smooth-y-ordinal.cjs');
const M = require('./bms-macro-bound.cjs');
const E = require('./protected-y-embedding.cjs');
const S = require('./star-beta-operators.cjs');
const G = require('./dilated-geometric-y.cjs');
const {terminalPrefixLE}=require('./y-reachability-certificate.cjs');
const {createYEngine} = require('./y-engine.cjs');
const {reconstructCandidate} = require('./converter.cjs');

const DEFAULTS = Object.freeze({ms:1000,maxWork:2500000,maxWidth:64,maxLayer:31,
  maxAtoms:40000,maxCapDepth:16,maxStars:16,beamWidth:8,maxStates:3000,forests:true,macros:true,protectedY:true});
const one = () => ({kind:'smooth',value:O.natural(1n)});
const wordKey = s => s.join(',');
const dataKey = x => JSON.stringify(x,(_,v)=>typeof v==='bigint'?String(v):v);
const isOne = v => v.kind==='smooth' && dataKey(v.value)===dataKey(O.natural(1n));
function sameWord(a,b) { return a.length===b.length && a.every((v,i)=>v===b[i]); }
function singleRoot(s) { return s.length>0 && s[0]===1n && s.slice(1).every(x=>x>1n); }

function fromWord(s,budget) {
  if (s.every((x,i)=>i===0 || x<=s[i-1]+1n)) return {kind:'smooth',value:O.rank(s,budget)};
  if(s.slice(1).some(x=>x===1n)) {
    const parts=[];let begin=0;
    for(let i=1;i<=s.length;i++) if(i===s.length || s[i]===1n) {
      parts.push(fromWord(s.slice(begin,i),budget));begin=i;
    }
    return {kind:'sum',parts};
  }
  if (s.length===2 && s[0]===1n) {
    if (s[1]===3n) return {kind:'betaPower',base:one(),exponent:O.natural(1n)};
    return {kind:'seed',index:s[1]};
  }
  if(s.length>=3 && s[0]===1n && s[1]>=2n && s.slice(2).every((x,i)=>x===s[i+1]*s[1]))
    return {kind:'geometric',ratio:s[1],length:s.length};
  if(s.length>=3 && sameWord(s.slice(0,3),[1n,2n,5n]) && s.slice(3).every(x=>x===3n)) {
    const d=s.length-3;
    return {kind:'betaPower',base:one(),exponent:d===0?O.natural(1n):O.omegaPow(O.natural(BigInt(d)))};
  }
  if(s.length>=5 && sameWord(s.slice(0,3),[1n,2n,5n]) && (s.length-3)%2===0 &&
      s.slice(3).every((x,i)=>x===(i%2?5n:3n)))
    return {kind:'betaEpsilonPower',base:one(),degree:O.natural(BigInt((s.length-3)/2))};
  if(s.length>=6 && sameWord(s.slice(0,3),[1n,2n,5n]) && (s.length-3)%3===0 &&
      s.slice(3).every((x,i)=>x===[3n,5n,4n][i%3]))
    return {kind:'betaEpsilonPower',base:one(),degree:[{exponent:O.natural(1n),coefficient:BigInt((s.length-3)/3)}]};
  return {kind:'word',word:wordKey(s)};
}
function timesBeta(base,exponent,budget) {
  if (base.kind==='betaPower') return {kind:'betaPower',base:base.base,
    exponent:O.add(base.exponent,exponent,budget)};
  return {kind:'betaPower',base,exponent};
}
function timesForest(base,depths,word,budget) {
  if (word.every((x,i)=>i===0 || x<=word[i-1]+1n)) return {kind:'smooth',value:O.rank(word,budget)};
  const exponent=O.rank(depths.map(BigInt),budget);
  if(base.kind==='forestProduct') return {kind:'forestProduct',base:base.base,
    exponent:O.add(base.exponent,exponent,budget)};
  return {kind:'forestProduct',base,exponent};
}
function timesProtected(base,outer,word,budget) {
  const value=fromWord(outer,budget);
  if(isOne(base)) return value;
  if(value.kind==='betaPower' && isOne(value.base)) return timesBeta(base,value.exponent,budget);
  if(value.kind==='betaEpsilonPower' && isOne(value.base)) return {kind:'betaEpsilonPower',base,degree:value.degree};
  if(value.kind==='smooth' && value.value.length===1 && value.value[0].coefficient===1n) {
    const exponent=value.value[0].exponent;
    if(base.kind==='forestProduct') return {kind:'forestProduct',base:base.base,
      exponent:O.add(base.exponent,exponent,budget)};
    return {kind:'forestProduct',base,exponent};
  }
  return {kind:'protectedProduct',base,outer:value};
}

// Only positive evidence for <= is used. Incomparability here means unknown,
// not that the underlying ordinals are incomparable. Raw Y digit lex is absent.
function knownLE(a,b,budget,depth=0) {
  budget.tick(); if(depth>128) throw new R.BudgetError('comparison depth');
  if(dataKey(a)===dataKey(b)) return true;
  if(isOne(a)) return !(b.kind==='smooth' && b.value.length===0);
  if(a.kind==='smooth' && b.kind==='smooth') return O.compare(a.value,b.value,budget)<=0;
  if(a.kind==='seed' && b.kind==='seed') return a.index<=b.index;
  // g(m,l)=Y(1,m,m^2,...,m^(l-1))=Y(1,m+1)[l-1].
  // Thus a smaller ratio is below the next seed, hence below every
  // larger-ratio geometric word. Equal ratios compare by prefix length.
  if(a.kind==='geometric' && b.kind==='geometric')
    return a.ratio<b.ratio || a.ratio===b.ratio && a.length<=b.length;
  if(a.kind==='seed' && b.kind==='geometric')return a.index<=b.ratio;
  if(a.kind==='geometric' && b.kind==='seed')return a.ratio<b.index;
  if(a.kind==='smooth' && b.kind==='geometric')return true; // g(2,3)=epsilon_0.
  if(a.kind==='geometric' && a.ratio===2n && (b.kind==='betaPower'||b.kind==='betaEpsilonPower'))return true;
  if(a.kind==='betaPower' && isOne(a.base) && O.compare(a.exponent,O.natural(1n),budget)===0 &&
      b.kind==='geometric' && b.ratio>=3n)return true;
  // beta > epsilon_0: Y13[2]=Y124, and Y124[n]=Y(1,2,...,n+2).
  if(a.kind==='smooth' && (b.kind==='seed' && b.index>=3n || b.kind==='betaPower' || b.kind==='betaEpsilonPower')) return true;
  if(b.kind==='betaPower' || b.kind==='betaEpsilonPower' || b.kind==='forestProduct' || b.kind==='protectedProduct') {
    if(knownLE(a,b.base,budget,depth+1)) return true;
  }
  if(a.kind==='betaPower' && b.kind==='betaPower') return (
    knownLE(a.base,b.base,budget,depth+1) && O.compare(a.exponent,b.exponent,budget)<=0);
  if(a.kind==='forestProduct' && b.kind==='forestProduct') return (
    knownLE(a.base,b.base,budget,depth+1) && O.compare(a.exponent,b.exponent,budget)<=0);
  if(a.kind==='forestProduct' && b.kind==='betaPower') return knownLE(a.base,b.base,budget,depth+1);
  if(a.kind==='sum' && b.kind==='betaPower') return a.parts.every(p=>knownLE(p,b.base,budget,depth+1));
  if(a.kind==='protectedProduct' && b.kind==='protectedProduct') return (
    knownLE(a.base,b.base,budget,depth+1) && knownLE(a.outer,b.outer,budget,depth+1));
  if(a.kind==='betaEpsilonPower' && b.kind==='betaEpsilonPower') return (
    knownLE(a.base,b.base,budget,depth+1) && O.compare(a.degree,b.degree,budget)<=0);
  if((a.kind==='betaPower' || a.kind==='forestProduct') && b.kind==='betaEpsilonPower')
    return knownLE(a.base,b.base,budget,depth+1);
  if(a.kind==='sum' && b.kind==='betaEpsilonPower')return a.parts.every(p=>knownLE(p,b.base,budget,depth+1));
  if(a.kind==='betaPower' && isOne(a.base) &&
      O.compare(a.exponent,O.natural(1n),budget)===0 && b.kind==='seed' && b.index>=3n) return true;
  return false;
}

function heuristic(candidate) {
  // Used only to limit retained candidates. It never proves an inequality.
  function level(v) {
    if(v.kind==='seed') return Number(v.index>100n?100n:v.index)+10;
    if(v.kind==='geometric') return Number(v.ratio>100n?100n:v.ratio)+10;
    if(v.kind==='word') return 5;
    if(v.kind==='sum') return Math.max(0,...v.parts.map(level));
    if(v.kind==='betaPower') return Math.max(3,level(v.base));
    if(v.kind==='betaEpsilonPower') return Math.max(3,level(v.base));
    if(v.kind==='forestProduct') return Math.max(2,level(v.base));
    if(v.kind==='protectedProduct') return Math.max(level(v.base),level(v.outer));
    return isOne(v)?0:1;
  }
  const betaBonus=candidate.value.kind==='betaEpsilonPower'?2000:candidate.value.kind==='betaPower'?1000:0;
  return level(candidate.value)*10000+betaBonus+candidate.depth*10-candidate.word.length;
}

function recursiveLowerBounds(input,options={}) {
  const limits={...DEFAULTS,...options};
  for(const k of ['ms','maxWork','maxWidth','maxAtoms','maxCapDepth','maxStars','beamWidth','maxStates'])
    if(!Number.isSafeInteger(limits[k]) || limits[k]<1) throw new RangeError('Invalid limit '+k);
  if(limits.maxWidth>256 || limits.ms>30000 || limits.maxCapDepth>128 || limits.beamWidth>64)
    throw new RangeError('Research prototype outer limit');
  const started=Date.now(), budget=new R.Budget(limits); let graph;
  try {graph=R.normalize(input,budget);}
  catch(error) {
    if(error.name!=='BudgetError') throw error;
    return {status:'unknown',reason:'budget during input validation',bounds:[],
      stats:{budgetStopped:true,work:budget.work,elapsedMs:Date.now()-started}};
  }
  const Y=createYEngine({maxWidth:limits.maxWidth,maxLayers:limits.maxLayer+1,
    maxAtoms:limits.maxAtoms,timeoutMs:Math.min(150,limits.ms)});
  const stats={states:0,candidates:0,beamPruned:false,budgetStopped:false,canonicalAttempts:0,macroAttempts:0,candidateBudgetSkips:0};
  const result=[];
  function optionalAttempt(action) {
    try{return action();}
    catch(error) {
      if(error.name!=='BudgetError')throw error;
      // A speculative redraw can exceed its own layer/width budget while
      // the global search still has ample work/time. Skip only that guess.
      budget.tick();stats.candidateBudgetSkips++;return null;
    }
  }
  function candidate(rule,base,end,word,value,extra={},depth=0) {
    stats.candidates++; budget.tick();
    return {word,value,depth,certificate:{version:1,rule,base,end,word:word.slice(),...extra}};
  }
  function retain(list,c) {
    budget.tick();
    for(let i=0;i<list.length;i++) {
      const old=list[i];
      if(sameWord(c.word,old.word)) {
        if(old.value.kind==='word' && c.value.kind!=='word') list.splice(i--,1);
        else return;
      }
    }
    for(const old of list) {
      if((terminalPrefixLE(c.word,old.word) || knownLE(c.value,old.value,budget)) &&
          (!(terminalPrefixLE(old.word,c.word) || knownLE(old.value,c.value,budget)) || old.word.length<=c.word.length)) return;
    }
    for(let i=list.length-1;i>=0;i--) if(terminalPrefixLE(list[i].word,c.word) || knownLE(list[i].value,c.value,budget)) list.splice(i,1);
    list.push(c); list.sort((a,b)=>heuristic(b)-heuristic(a));
    if(list.length>limits.beamWidth) {
      stats.beamPruned=true;
      function anchor(v) {
        if(v.kind==='betaPower' || v.kind==='betaEpsilonPower' || v.kind==='forestProduct' || v.kind==='protectedProduct') return anchor(v.base);
        return dataKey(v);
      }
      const seen=new Set(),diverse=[],rest=[];
      for(const item of list) {
        const key=anchor(item.value);
        if(seen.has(key)) rest.push(item); else {seen.add(key);diverse.push(item);}
      }
      list.splice(0,list.length,...diverse.concat(rest).slice(0,limits.beamWidth));
    }
  }
  function finish() {
    return {status:'lower-bounds',relation:'each rho_Y(word) <= rho_RPD(input)',
      bounds:result.map(c=>({sequence:c.word,y:wordKey(c.word),algebra:c.value,certificate:c.certificate})),
      selectedBy:'bounded search heuristic after proved partial comparisons',
      mostTightNotClaimed:true,wholeConverterLeanFormalized:false,
      stats:{...stats,work:budget.work,elapsedMs:Date.now()-started}};
  }
  const finite=Array(graph.size).fill(1n);
  retain(result,candidate('globalFinite',0,graph.size,finite,{kind:'smooth',value:O.natural(BigInt(graph.size))}));
  try {
    const vf=R.checkVF(graph,budget);
    if(!vf.V || !vf.F) return {...finish(),limitation:'non-VF input; only finite deletion bound'};
    const reach=P.ancestry(graph,budget);
    const has=(k,q,p,j)=>{budget.tick();return Boolean((reach.get(`${k},${q}`)?.[j]??0n)&(1n<<BigInt(p)));};
    optionalAttempt(()=>{
    const raw=reconstructCandidate(graph,budget);
    if(raw && raw[0]===1n) {
      const q=Y.diagram(raw); budget.tick();
      if(R.includes(graph,q)) retain(result,candidate('globalCanonical',0,graph.size,raw,fromWord(raw,budget)));
    }
    });

    for(let base=1;base<graph.size;base++) {
      const dp=new Map(), macroAt=new Map();
      if(limits.macros) {
        stats.macroAttempts++;
        const macro=M.findBMSMacro(P.project(graph,base,graph.size,budget),budget);
        if(macro.status==='found') {
          const end=macro.certificate.prefixWidth;
          const cert={...macro.certificate,deletedSuffixColumns:0};
          if(cert.b<base) throw Error('Macro escaped the local interval');
          macroAt.set(end,candidate('macro',base,end,[1n,3n],timesBeta(one(),O.natural(1n),budget),{macro:cert}));
        }
      }
      for(let end=base+1;end<=graph.size;end++) {
        budget.tick(); if(++stats.states>limits.maxStates) throw new R.BudgetError('DP state limit');
        const list=end===base+1 ? [candidate('unitOne',base,end,[1n],one())] : dp.get(end-1).slice();
        if(macroAt.has(end)) retain(list,macroAt.get(end));
        const unit=P.project(graph,base,end,budget);
        for(const geometric of G.find(unit,base,end,budget))
          retain(list,candidate('dilatedGeometric',base,end,geometric.word,
            fromWord(geometric.word,budget),{level:geometric.level,positions:geometric.positions}));
        // Undo a full-coordinate offset only for generating a candidate.
        // Redrawing and checking the forward offset is the actual certificate.
        const relative=R.normalize({size:end-base,atoms:unit.atoms.filter(e=>e[1]>=base)
          .map(([k,q,p,j])=>[k,q-base,p-base,j-base])},budget);
        stats.canonicalAttempts++;
        optionalAttempt(()=>{
        const s=reconstructCandidate(relative,budget);
        if(s && singleRoot(s)) {
          const q=P.fixedOffset(Y.diagram(s),base,budget);
          if(R.includes(unit,q)) retain(list,candidate('canonical',base,end,s,fromWord(s,budget)));
        }
        });

        if(end>=base+4) {
          const split=end-3;
          if(has(0,0,base,split) && has(0,base,split,split+1) && has(0,0,base,split+2))
            for(const child of dp.get(split)) {
              const word=child.word.concat([2n,5n]);
              retain(list,candidate('finiteBeta',base,end,word,timesBeta(child.value,O.natural(1n),budget),
                {unitEnd:split,child:child.certificate},child.depth+1));
            }
          for(let d=1;d<=Math.min(limits.maxCapDepth,end-base-3);d++) {
            const cut=end-d-2;
            let fits=has(0,0,base,cut);
            for(let i=0;fits && i<=d;i++) fits=has(0,base+i,cut+i,cut+i+1);
            if(fits) for(const child of dp.get(cut)) {
              const word=child.word.concat([2n,5n],Array(d).fill(3n));
              retain(list,candidate('cap',base,end,word,timesBeta(child.value,O.omegaPow(O.natural(BigInt(d))),budget),
                {unitEnd:cut,capDepth:d,child:child.certificate},child.depth+1));
              {
                const stronger=child.word.concat([2n,5n],Array.from({length:d},()=>[3n,5n,4n]).flat());
                retain(list,candidate('capStar',base,end,stronger,
                  {kind:'betaEpsilonPower',base:child.value,degree:[{exponent:O.natural(1n),coefficient:BigInt(d)}]},
                  {unitEnd:cut,capDepth:d,child:child.certificate},child.depth+1));
              }
            }
          }
          for(let m=1;m<=Math.min(limits.maxStars,end-base-4);m++) {
            const cut=end-m-3;
            let fits=has(0,0,base,cut)&&has(0,base,cut,cut+1)&&has(0,0,base,cut+2);
            for(let j=cut+3;fits&&j<end;j++)fits=has(0,1,cut,j);
            if(fits)for(const child of dp.get(cut)) {
              const word=child.word.concat([2n,5n],Array.from({length:m},()=>[3n,5n]).flat());
              retain(list,candidate('starBeta',base,end,word,
                {kind:'betaEpsilonPower',base:child.value,degree:O.natural(BigInt(m))},
                {unitEnd:cut,starCount:m,child:child.certificate},child.depth+1));
            }
          }
        }

        if(limits.protectedY) for(let cut=base+1;cut<end;cut++) {
          const virtual=E.quotientCandidateGraph(unit,base,cut,budget);
          const outer=optionalAttempt(()=>reconstructCandidate(virtual,budget));
          if(!outer || !singleRoot(outer) || !E.protectedWord(outer)) continue;
          // Ordinary forests are already searched more cheaply below.
          if(outer.every((x,i)=>i===0 || x<=outer[i-1]+1n)) continue;
          const prefix=P.project(graph,base,cut,budget);
          const encoded=optionalAttempt(()=>E.embedding(outer,prefix,base,Y,budget).graph);
          if(!encoded)continue;
          if(!P.ancestorCover(unit,encoded,budget,reach)) continue;
          for(const child of dp.get(cut)) {
            const word=E.substitute(child.word,outer);
            retain(list,candidate('protectedY',base,end,word,timesProtected(child.value,outer,word,budget),
              {unitEnd:cut,outerWord:outer,child:child.certificate},child.depth+1));
          }
        }
        if(limits.forests) for(let cut=base+1;cut<end;cut++) {
          const depths=[],stack=[]; let fits=true;
          for(let j=cut;j<end;j++) {
            let parent=null,depth=0;
            if(has(0,0,base,j)) {parent=base;depth=1;}
            for(const item of stack) if(has(0,0,item.j,j)) {parent=item.j;depth=item.depth+1;}
            if(parent===null) {fits=false;break;}
            while(stack.length && stack.at(-1).depth>=depth) stack.pop();
            stack.push({j,depth}); depths.push(depth);
          }
          if(fits) for(const child of dp.get(cut)) {
            const word=child.word.concat(depths.map(d=>BigInt(d+1)));
            retain(list,candidate('forest',base,end,word,timesForest(child.value,depths,word,budget),
              {unitEnd:cut,depths,child:child.certificate},child.depth+1));
          }
        }
        dp.set(end,list);
        for(const c of list) retain(result,c);
      }
    }
  } catch(error) {
    if(error.name!=='BudgetError') throw error;
    stats.budgetStopped=true;
  }
  return finish();
}

// Independent of the search choices and algebra-ranking metadata.
function verifyRecursiveCertificate(input,certificate,options={}) {
  const limits={...DEFAULTS,...options}, budget=new R.Budget(limits);
  const graph=R.normalize(input,budget), vf=R.checkVF(graph,budget);
  const Y=createYEngine({maxWidth:limits.maxWidth,maxLayers:limits.maxLayer+1,
    timeoutMs:Math.min(150,limits.ms),maxAtoms:limits.maxAtoms});
  const memo=new Set();
  function check(c,depth=0) {
    budget.tick(); if(depth>256) throw new R.BudgetError('certificate depth');
    if(memo.has(c)) return true;
    if(!c || c.version!==1 || !Number.isSafeInteger(c.base) || !Number.isSafeInteger(c.end) ||
        c.end>graph.size || !Array.isArray(c.word)) return false;
    if(c.rule==='globalFinite') return c.base===0 && c.end>=0 && c.word.length===c.end && c.word.every(x=>x===1n);
    if(!vf.V || !vf.F) return false;
    if(c.rule==='globalCanonical') {
      if(c.base!==0 || c.word.length!==c.end || c.word.length && c.word[0]!==1n) return false;
      const target={size:c.end,atoms:graph.atoms.filter(e=>e[3]<c.end)};
      return R.includes(target,Y.diagram(c.word));
    }
    if(c.base<1 || c.end<=c.base || !singleRoot(c.word)) return false;
    const unit=P.project(graph,c.base,c.end,budget);
    let valid=false;
    if(c.rule==='unitOne') valid=c.end===c.base+1 && sameWord(c.word,[1n]);
    else if(c.rule==='canonical') valid=c.word.length===c.end-c.base &&
      R.includes(unit,P.fixedOffset(Y.diagram(c.word),c.base,budget));
    else if(c.rule==='dilatedGeometric') valid=G.verify(unit,c.base,c.end,c,budget);
    else if(c.rule==='macro') valid=sameWord(c.word,[1n,3n]) && c.macro?.b>=c.base &&
      M.verifyCertificate(unit,c.macro,budget).status==='valid';
    else if(['finiteBeta','cap','capStar','starBeta','forest','protectedY'].includes(c.rule)) {
      if(!c.child || c.child.base!==c.base || c.child.end>c.unitEnd ||
          !Number.isSafeInteger(c.unitEnd) || c.unitEnd<=c.base || c.unitEnd>=c.end || !check(c.child,depth+1)) return false;
      const prefix=P.project(graph,c.base,c.unitEnd,budget); let template,word;
      if(c.rule==='finiteBeta') {template=P.finiteBeta(prefix,c.base,budget);word=c.child.word.concat([2n,5n]);}
      else if(c.rule==='capStar') {
        if(!Number.isSafeInteger(c.capDepth)||c.capDepth<1||c.capDepth>limits.maxWidth)return false;
        template=P.cap(prefix,c.base,c.capDepth,budget);
        word=c.child.word.concat([2n,5n],Array.from({length:c.capDepth},()=>[3n,5n,4n]).flat());
      } else if(c.rule==='starBeta') {
        if(!Number.isSafeInteger(c.starCount)||c.starCount<1||c.starCount>limits.maxWidth)return false;
        template=S.starBeta(prefix,c.base,c.starCount,budget);
        word=c.child.word.concat([2n,5n],Array.from({length:c.starCount},()=>[3n,5n]).flat());
      }
      else if(c.rule==='cap') {
        if(!Number.isSafeInteger(c.capDepth) || c.capDepth<1 || c.capDepth>limits.maxWidth) return false;
        template=P.cap(prefix,c.base,c.capDepth,budget);word=c.child.word.concat([2n,5n],Array(c.capDepth).fill(3n));
      } else if(c.rule==='protectedY') {
        if(!Array.isArray(c.outerWord) || !singleRoot(c.outerWord) || !E.protectedWord(c.outerWord)) return false;
        template=E.embedding(c.outerWord,prefix,c.base,Y,budget).graph;
        word=E.substitute(c.child.word,c.outerWord);
      } else {
        if(!Array.isArray(c.depths) || c.depths.length>limits.maxWidth) return false;
        template=P.forest(prefix,c.base,c.depths,budget);word=c.child.word.concat(c.depths.map(d=>BigInt(d+1)));
      }
      valid=sameWord(word,c.word) && P.ancestorCover(unit,template,budget);
    }
    if(valid) memo.add(c); return valid;
  }
  try { return {status:check(certificate)?'valid':'invalid',structuralOnly:true,
    proofDependency:'PROTECTED-SUBSTITUTION.zh-CN.md, GENERAL-PROTECTED-Y-COMPILER.zh-CN.md, DILATION-AND-STAR-BOUNDS.zh-CN.md, DILATED-GEOMETRIC-Y.zh-CN.md, prior VF/cover lemmas'}; }
  catch(error) {
    if(error.name==='BudgetError') return {status:'unknown',reason:'budget'};
    if(error instanceof RangeError || error instanceof TypeError) return {status:'invalid',reason:error.message};
    throw error;
  }
}

module.exports={recursiveLowerBounds,verifyRecursiveCertificate,knownLE,DEFAULTS};

}};
  function load(name) {
    if(modules.has(name))return modules.get(name).exports;
    if(!Object.hasOwn(factories,name))throw Error('Unknown bundled math module');
    const module={exports:{}};modules.set(name,module);
    factories[name](load,module);return module.exports;
  }
  return load('./recursive-y-lower-bound.cjs');
})();
const createBoundBridge = function createBoundBridge(R, exact, forest, Y, reconstructCandidate, options = {}, recursive = null) {
  const limits = {maxWidth: 64, maxLayer: 31, maxAtoms: 16000,
    maxWork: 200000, ms: 75, ...options};
  const budget = () => new R.Budget(limits);
  const legal = s => Array.isArray(s) && s.length <= limits.maxWidth &&
    (!s.length || s[0] === 1n) && Array.from(s).every(x => typeof x === 'bigint' && x > 0n);

  function sequenceGraph(s, b) {
    if (!legal(s)) throw new R.BudgetError('Y input validity or annotation width limit');
    const graph = Y.diagram(s); b.tick();
    return graph;
  }

  function yToRPD(sequence) {
    const b = budget();
    if (!legal(sequence)) throw new R.BudgetError('Y input validity or annotation width limit');
    const tag = exact.recognizeY(sequence);
    let graph = tag ? exact.canonicalRPD(tag) : forest.encodeY(sequence);
    if (graph) return {status: 'exact', graph: R.normalize(graph, b),
      relation: 'rho_Y(source) = rho_RPD(target)', method: tag ? 'exact-fragment' : 'exact-forest'};
    const closed = R.saturateVF(sequenceGraph(sequence, b), b);
    return {status: 'upper-bound', graph: closed.graph,
      relation: 'rho_Y(source) <= rho_RPD(target)', method: 'V/F-cover',
      certificate: {V: true, F: true, addedAtoms: closed.added}};
  }

  function rpdToY(input) {
    const b = budget(), graph = R.normalize(input, b);
    const tag = exact.recognizeRPD(graph);
    let sequence = tag ? exact.canonicalY(tag) : forest.decodeRPD(graph);
    if (sequence) return {status: 'exact', sequence, graph: sequenceGraph(sequence, b),
      relation: 'rho_RPD(source) = rho_Y(target)', method: tag ? 'exact-fragment' : 'exact-forest'};
    const finite = () => ({status:'lower-bound',sequence:Array(graph.size).fill(1n),
      graph:{size:graph.size,atoms:[]},relation:'rho_Y(target) <= rho_RPD(source)',
      method:'finite-fallback'});
    if(recursive) {
      let search;
      try {
        b.tick();
        const remaining=()=>Math.max(1,b.deadline-Date.now());
        search=recursive.recursiveLowerBounds(graph,{...limits,
          ms:Math.max(1,remaining()-25),maxWork:120000,beamWidth:4,maxStates:500});
        for(const candidate of search.bounds.slice(0,4)) {
          if(Date.now()>=b.deadline-3)break;
          if(!legal(candidate.sequence))continue;
          const certifiedWord=candidate.certificate?.word;
          if(!Array.isArray(certifiedWord)||certifiedWord.length!==candidate.sequence.length||
              !candidate.sequence.every((value,i)=>value===certifiedWord[i]))continue;
          const checked=recursive.verifyRecursiveCertificate(graph,candidate.certificate,
            {...limits,ms:Math.max(1,Math.min(18,remaining()-3)),maxWork:60000});
          if(checked.status!=='valid')continue;
          try {
            const canonical=sequenceGraph(candidate.sequence,b);
            return {status:'lower-bound',sequence:candidate.sequence,graph:canonical,
              relation:'rho_Y(target) <= rho_RPD(source)',method:'recursive-certified-bound',
              certificate:candidate.certificate,certificateVerified:true,
              proofStatus:'paper-lemmas-not-end-to-end-Lean',mostTightNotClaimed:true,
              searchStats:search.stats};
          } catch(error) {
            if(error.name!=='BudgetError')throw error;
          }
        }
      } catch(error) {
        if(error.name!=='BudgetError')throw error;
      }
      return {...finite(),searchLimited:true,searchStats:search?.stats};
    }
    const invariant = R.checkVF(graph, b);
    sequence = reconstructCandidate(graph, b);
    if (sequence && invariant.V && invariant.F) {
      const canonical = sequenceGraph(sequence, b);
      if (R.includes(graph, canonical)) return {status: 'lower-bound', sequence, graph: canonical,
        relation: 'rho_Y(target) <= rho_RPD(source)', method: 'checked-V/F-cover'};
    }
    // m deletion steps give a certified finite lower bound on every graph.
    // This is not silently promoted to equality or advertised as tight.
    return finite();
  }

  return {yToRPD, rpdToY, limits: {...limits}};
};
const makeMountainDisplay = function createYMountainDisplay(options = {}) {
  const limits = {
    maxMs: options.maxMs ?? 30,
    maxWidth: options.maxWidth ?? 64,
    maxLayers: options.maxLayers ?? 32,
    maxNodes: options.maxNodes ?? 1600,
    maxAtoms: options.maxAtoms ?? 40000,
    maxWork: options.maxWork ?? 180000,
    maxSvgChars: options.maxSvgChars ?? 200000,
    maxTextChars: options.maxTextChars ?? 200000,
  };
  for (const value of Object.values(limits)) {
    if (!Number.isSafeInteger(value) || value < 1) throw new RangeError('Invalid Y mountain display budget');
  }
  const now = typeof options.now === 'function' ? options.now
    : typeof performance !== 'undefined' && typeof performance.now === 'function'
      ? () => performance.now() : () => Date.now();
  let lastFailure = null;

  function escapeText(value) {
    return String(value).replace(/[&<>"']/g, character =>
      ({'&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;'})[character]);
  }
  function fail(kind, reason) {
    const error = new Error(reason); error.displayKind = kind; throw error;
  }
  function budget() {
    const start = now(); let work = 0;
    return {tick(amount = 1) {
      work += amount;
      if (work > limits.maxWork) fail('budget', 'Y mountain work budget');
      if (now() - start > limits.maxMs) fail('budget', 'Y mountain time budget');
    }};
  }
  function guarded(action) {
    lastFailure = null;
    try { return action(budget()); }
    catch (error) {
      lastFailure = {kind: error.displayKind ?? 'unsupported', reason: error.message ?? String(error)};
      return null;
    }
  }

  function recover(graph, task) {
    if (!graph || !Number.isSafeInteger(graph.size) || graph.size < 0 || !Array.isArray(graph.atoms)) {
      fail('invalid', 'Expected a finite Y root graph');
    }
    if (graph.size > limits.maxWidth || graph.atoms.length > limits.maxAtoms) {
      fail('budget', 'Y mountain input size budget');
    }
    const unique = new Map(), rootGroups = new Map(), parentGroups = new Map();
    let maxLayer = 0;
    for (const atom of graph.atoms) {
      task.tick();
      if (!Array.isArray(atom) || atom.length !== 4) fail('invalid', 'Invalid Y graph atom');
      for (const value of atom) {
        if (!Number.isSafeInteger(value) || value < 0) fail('invalid', 'Invalid Y graph coordinate');
      }
      const [k, q, p, j] = atom;
      if (!(q <= p && p < j && j < graph.size)) fail('invalid', 'Y graph edge does not point left');
      if (k >= limits.maxLayers) fail('budget', 'Y mountain layer budget');
      maxLayer = Math.max(maxLayer, k);
      const key = atom.join(',');
      if (unique.has(key)) continue;
      unique.set(key, atom.slice());
      const rootKey = `${k},${p},${j}`;
      let roots = rootGroups.get(rootKey);
      if (!roots) { roots = {count: 0, maximum: -1}; rootGroups.set(rootKey, roots); }
      roots.count++; roots.maximum = Math.max(roots.maximum, q);
      const groupKey = `${k},${q}`;
      let group = parentGroups.get(groupKey);
      if (!group) { group = {k, q, parents: new Map()}; parentGroups.set(groupKey, group); }
      group.parents.set(j, Math.max(p, group.parents.get(j) ?? -1));
    }
    for (const roots of rootGroups.values()) {
      task.tick();
      if (roots.count !== roots.maximum + 1) fail('unsupported', 'Y graph is not root-downward-closed');
    }

    // Gen: for each (k,q), follow maximum-parent chains to their endpoint.
    const genuine = [], recoveredClosure = new Set();
    for (const {k, q, parents} of parentGroups.values()) {
      const endpoints = new Map();
      const ordered = [...parents].sort((a, b) => a[0] - b[0]);
      for (const [j, p] of ordered) {
        task.tick();
        const root = endpoints.get(p) ?? p;
        endpoints.set(j, root);
        if (root !== q) continue;
        genuine.push([k, q, p, j]);
        for (let smaller = 0; smaller <= q; smaller++) {
          task.tick(); recoveredClosure.add(`${k},${smaller},${p},${j}`);
        }
      }
    }
    if (recoveredClosure.size !== unique.size || [...unique.keys()].some(key => !recoveredClosure.has(key))) {
      fail('unsupported', 'Not a canonical genuine-row Y graph; refusing to draw weakened RPD edges as Y');
    }
    genuine.sort((a, b) => a[0] - b[0] || a[3] - b[3] || a[1] - b[1] || a[2] - b[2]);
    const layers = graph.size === 0 ? [] : Array.from({length: maxLayer + 1}, (_, k) => ({
      k, columns: Array.from({length: graph.size}, () => []),
    }));
    for (const atom of genuine) layers[atom[0]].columns[atom[3]].push(atom);

    let nodeCount = 0;
    for (const layer of layers) {
      const {columns} = layer;
      if (layer.k > 0 && columns.every(column => column.length === 0)) {
        fail('unsupported', 'Missing intermediate Y extraction layer');
      }
      const heights = columns.map(column => column.length), roots = [];
      nodeCount += heights.reduce((sum, height) => sum + height + 1, 0);
      if (nodeCount > limits.maxNodes) fail('budget', 'Complete Y mountain exceeds node budget');
      for (let j = 0; j < columns.length; j++) {
        roots[j] = [];
        for (let h = 0; h < columns[j].length; h++) {
          task.tick();
          const [, q, p] = columns[j][h];
          if (heights[p] < h) fail('unsupported', 'Y parent target row node does not exist');
          if (heights[q] !== h) fail('unsupported', 'Y component root does not have the recovered row height');
          const root = heights[p] === h ? p : roots[p][h];
          if (root !== q) fail('unsupported', 'Recovered Y row has inconsistent component roots');
          roots[j][h] = root;
          if (h > 0) {
            let ancestor = j;
            while (ancestor > p) {
              task.tick();
              if (heights[ancestor] <= h - 1) break;
              ancestor = columns[ancestor][h - 1][2];
            }
            if (ancestor !== p) fail('unsupported', 'Y higher-row parent is not a lower-row ancestor');
          }
        }
      }
      layer.heights = heights;
    }
    return {size: graph.size, genuine, layers, nodeCount};
  }

  function layout(graph, sequence, task) {
    const recovered = recover(graph, task);
    let labels = null;
    if (sequence !== undefined && sequence !== null) {
      if (!Array.isArray(sequence) || sequence.length !== graph.size) fail('invalid', 'Y sequence width mismatch');
      labels = [];
      let characters = 0;
      for (const value of sequence) {
        task.tick();
        if (typeof value !== 'bigint' || value < 1n) fail('invalid', 'Y labels must be positive BigInts');
        const text = value.toString(); characters += text.length;
        if (characters > limits.maxTextChars) fail('budget', 'Complete Y sequence label budget');
        labels.push(text);
      }
    }
    const labelWidth = labels?.reduce((maximum, text) => Math.max(maximum, text.length), 0) ?? 0;
    const columnGap = Math.max(14, labelWidth * 5 + 3), rowGap = 11;
    const left = Math.max(18, labelWidth * 2.5 + 3);
    const width = graph.size ? left + (graph.size - 1) * columnGap + Math.max(9, labelWidth * 2.5 + 3) : 20;
    let y = 4, edgeCount = 0;
    for (const layer of recovered.layers) {
      task.tick();
      const highest = Math.max(...layer.heights, 0), baseline = y + highest * rowGap + 3;
      layer.baseline = baseline;
      layer.layerLabel = {text: String(layer.k), x: 3, y: baseline - highest * rowGap / 2 + 2};
      layer.nodes = []; layer.edges = [];
      for (let j = 0; j < graph.size; j++) {
        for (let h = 0; h <= layer.heights[j]; h++) {
          task.tick();
          layer.nodes.push({id: `${layer.k}:${j}:${h}`, column: j, row: h,
            x: left + j * columnGap, y: baseline - h * rowGap});
        }
        for (let h = 0; h < layer.heights[j]; h++) {
          const [, root, parent] = layer.columns[j][h];
          layer.edges.push({column: j, row: h, root, parent,
            from: `${layer.k}:${j}:${h + 1}`, left: `${layer.k}:${parent}:${h}`, down: `${layer.k}:${j}:${h}`,
            x1: left + j * columnGap, y1: baseline - (h + 1) * rowGap,
            leftX: left + parent * columnGap, leftY: baseline - h * rowGap,
            downX: left + j * columnGap, downY: baseline - h * rowGap});
          edgeCount += 2;
        }
      }
      y = baseline + 10;
    }
    const bottomLabels = labels ? labels.map((text, column) => ({text, column,
      x: left + column * columnGap, y: y + 3})) : [];
    if (graph.size === 0) bottomLabels.push({text: '0', column: null, x: 10, y: 12});
    return {...recovered, width, height: graph.size === 0 ? 18 : y + (labels ? 8 : 0),
      edgeCount, bottomLabels};
  }

  function makeSvg(graph, sequence, task) {
    const model = layout(graph, sequence, task), output = [];
    let characters = 0;
    function add(text) {
      task.tick(); characters += text.length;
      if (characters > limits.maxSvgChars) fail('budget', 'Complete Y SVG exceeds text budget');
      output.push(text);
    }
    add(`<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 ${model.width} ${model.height}" width="${model.width}" height="${model.height}" role="img" aria-label="Y mountain" style="max-width:100%;height:auto;vertical-align:middle;color:inherit;font-family:inherit">`);
    for (const layer of model.layers) {
      add(`<g data-layer="${layer.k}">`);
      add('<g fill="none" stroke="currentColor" stroke-width="0.7" opacity="0.72">');
      for (const edge of layer.edges) {
        add(`<path d="M${edge.leftX} ${edge.leftY}L${edge.x1} ${edge.y1}L${edge.downX} ${edge.downY}"/>`);
      }
      add('</g><g fill="currentColor">');
      for (const node of layer.nodes) add(`<circle cx="${node.x}" cy="${node.y}" r="1.15"/>`);
      add('</g>');
      const label = layer.layerLabel;
      add(`<text x="${label.x}" y="${label.y}" fill="currentColor" font-family="inherit" font-size="8" opacity="0.7">${escapeText(label.text)}</text></g>`);
    }
    for (const label of model.bottomLabels) {
      add(`<text x="${label.x}" y="${label.y}" text-anchor="middle" fill="currentColor" font-family="inherit" font-size="9">${escapeText(label.text)}</text>`);
    }
    add('</svg>');
    return output.join('');
  }

  return {
    svg(graph, sequence) { return guarded(task => makeSvg(graph, sequence, task)); },
    model(graph, sequence) { return guarded(task => layout(graph, sequence, task)); },
    // Genuine roots only; format is [(k,parent,root),...] in column order.
    plain(graph) { return guarded(task => {
      const recovered = recover(graph, task);
      const columns = Array.from({length: graph.size}, () => []);
      for (const [k, q, p, j] of recovered.genuine) columns[j].push(`(${k},${p},${q})`);
      const result = columns.length ? columns.map(column => '[' + column.join(',') + ']').join('') : '∅';
      if (result.length > limits.maxTextChars) fail('budget', 'Complete Y graph list exceeds text budget');
      task.tick(); return result;
    }); },
    escapeText,
    get lastFailure() { return lastFailure; },
  };
};
const installBoundDisplays = function installBoundDisplays(kind, originalRPD, R, bridge, makeYEngine, makeMountainDisplay) {
  const LIMIT = 'Limit';
  const escape = s => String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;')
    .replace(/>/g, '&gt;').replace(/"/g, '&quot;').replace(/'/g, '&#39;');
  const strip = s => String(s).replace(/\s*(?:≥\s*Y|>=\s*Y|≤\s*RPD|<=\s*RPD)【[\s\S]*$/, '').trim();
  const mountainDisplay = makeMountainDisplay({maxWidth: 64, maxNodes: 1600, maxSvgChars: 200000, maxMs: 30});
  const cache = new Map();
  let cacheChars = 0, hits = 0, misses = 0;
  const cacheLimits = {entries: 64, chars: 1500000};

  function memo(key, compute) {
    if (cache.has(key)) { hits++; return cache.get(key); }
    misses++; const value = compute();
    const chars = JSON.stringify(value, (_, v) => typeof v === 'bigint' ? String(v) : v).length;
    if (chars <= cacheLimits.chars) {
      while (cache.size && (cache.size >= cacheLimits.entries || cacheChars + chars > cacheLimits.chars)) {
        const first = cache.keys().next().value;
        cacheChars -= cache.get(first).__chars; cache.delete(first);
      }
      value.__chars = chars; cache.set(key, value); cacheChars += chars;
    }
    return value;
  }

  const explanation = result => result.status === 'exact' ? '此片段已建立等值；仍按所选不等号显示。'
    : result.method === 'recursive-certified-bound' ? '依据纸面比较引理，有限结构证书已复验；新增引理未端到端 Lean 形式化。不保证附注标准或下界最紧。'
    : result.method === 'finite-fallback' ? '仅得到删尾链给出的有限下界，不是等值或紧下界。'
    : '展开秩的已建立界；不保证附注是从顶端可达的标准式，不宣称等值。';

  function unknown(error) {
    const budget = error?.name === 'BudgetError' || error?.code === 'Y_BUDGET';
    return {status: 'unknown', text: budget ? '未算出：附注超限' : '未算出：转换失败',
      detail: String(error?.message ?? error)};
  }

  function describeBound(raw) {
    return memo(String(raw), () => {
      if (raw === LIMIT) return {status: 'limit-bound', text: LIMIT,
        method: 'whole-limit-Y-le-RPD', detail: '沿用已建立的 Y 极限 ≤ RPD 极限；没有把顶端画成有限山脉。'};
      try {
        if (kind === 'rpd') {
          const input = originalRPD.debug.graph(raw);
          if (!input || typeof input !== 'object' || !Array.isArray(input.atoms)) throw Error('Missing RPD graph');
          const number = s => {
            const n = Number(s);
            if (!Number.isSafeInteger(n) || n < 0) throw new R.BudgetError('coordinate exceeds exact annotation range');
            return n;
          };
          const graph = {size: number(input.size), atoms: input.atoms.map(a => a.map(number))};
          const result = bridge.rpdToY(graph);
          const text = mountainDisplay.plain(result.graph);
          const svg = mountainDisplay.svg(result.graph, result.sequence);
          if (text === null || svg === null) return {status: 'unknown', text: '未算出：山脉显示超限或不支持',
            detail: '没有返回局部山脉图。'};
          return {...result, text, svg, detail: explanation(result)};
        }
        const result = bridge.yToRPD(parseY(raw));
        return {...result, text: R.toList(result.graph), detail: explanation(result)};
      } catch (error) { return unknown(error); }
    });
  }

  function suffixPlain(raw) {
    const result = describeBound(raw);
    return (kind === 'rpd' ? ' ≥ Y【' : ' ≤ RPD【') + result.text + '】';
  }
  function suffixHTML(raw) {
    const result = describeBound(raw), label = kind === 'rpd' ? ' ≥ Y【' : ' ≤ RPD【';
    const content = result.svg ?? escape(result.text);
    return '<span class="ordinal-bound-note" title="' + escape(result.detail) +
      '" style="display:inline;white-space:normal;font-family:inherit">' + escape(label) +
      content + '】</span>';
  }
  function suffixLatex(raw) {
    const result = describeBound(raw);
    const text = result.text.replace(/[\\{}_%#$&^~]/g, c => '\\' + c);
    return (kind === 'rpd' ? '\\;\\ge\\;\\mathrm{Y}' : '\\;\\le\\;\\mathrm{RPD}') +
      '\\bigl[\\text{' + text + '}\\bigr]';
  }

  function decorate(spec) {
    const old = typeof spec === 'function' ? {plain: spec} : spec;
    const out = {...old,
      plain: raw => old.plain(raw) + suffixPlain(raw),
      html: raw => (old.html ? old.html(raw) : escape(old.plain(raw))) + suffixHTML(raw),
      latex: raw => (old.latex ? old.latex(raw) : '\\text{' + old.plain(raw) + '}') + suffixLatex(raw),
    };
    if (old.from_display) out.from_display = text => old.from_display(strip(text));
    return out;
  }

  function parseY(raw) {
    const text = strip(raw);
    if (text.length > 200000) throw new R.BudgetError('Y input text limit');
    if (['', '0', '∅', '[]'].includes(text)) return [];
    const tokens = text.replace(/^\[|\]$/g, '').split(/[\s,]+/);
    if (tokens.length > 128 || tokens.some(t => !/^\d+$/.test(t) || t.length > 2000))
      throw new R.BudgetError('Y input width, digits or syntax');
    const sequence = tokens.map(BigInt);
    if (sequence[0] !== 1n || sequence.some(x => x < 1n)) throw Error('Y 输入须首项为 1 且所有项为正整数。');
    return sequence;
  }
  const stringifyY = sequence => sequence.length ? sequence.join(',') : '0';

  let notation;
  if (kind === 'rpd') {
    notation = {...originalRPD, id: 'rpd-with-y-lower-bound-v1',
      name: 'RPD（附 Y 山脉下界）', simple_name: 'RPD ≥ Y',
      display: decorate(originalRPD.display),
      display_equiv: Object.fromEntries(Object.entries(originalRPD.display_equiv ?? {}).map(([key, value]) => [key, decorate(value)])),
    };
  } else {
    const engine = makeYEngine({maxWidth: 128, maxLayers: 48, timeoutMs: 150,
      maxAtoms: 40000, maxDigits: 2000, maxWork: 500000});
    const sourceDisplay = {name: '数列', plain: raw => raw,
      from_display: text => strip(text) === LIMIT ? LIMIT : stringifyY(parseY(text))};
    notation = {
      id: 'classic-y-with-rpd-upper-bound-v1', name: 'Y 序列（附 RPD 上界）', simple_name: 'Y ≤ RPD',
      display: decorate(sourceDisplay),
      is_limit: raw => raw === LIMIT || parseY(raw).at(-1) > 1n,
      compare: (left, right) => {
        if (left === LIMIT || right === LIMIT) return Number(left === LIMIT) - Number(right === LIMIT);
        return R.lex(parseY(left), parseY(right));
      },
      FS: (raw, n) => {
        if (!Number.isSafeInteger(n) || n < 0) throw Error('基本列指标须为非负安全整数。');
        if (raw === LIMIT) return '1,' + String(BigInt(n) + 1n);
        return stringifyY(engine.fs(parseY(raw), n));
      },
      init: () => [LIMIT, '1', '0'],
      description: ['经典 Y 规则；数值使用 BigInt。附注是独立 RPD 上界，不参与展开、比较或表达式标识。'],
    };
  }
  notation.description = [...(Array.isArray(notation.description) ? notation.description : [notation.description].filter(Boolean)),
    '主表达式从顶端正常展开仍属于原标准域；附注不保证标准，只承诺所显示的展开秩不等式。',
    '不等式附注不是等价表示，也不是另一个基本列定义。精确片段与有限回退可在悬停提示中区分。',
    'HTML 模式下 RPD 的 Y 附注显示完整山脉；纯文本模式显示完整山脉父关系列表。',
    '附注宽度、层数、边数、时间与缓存均有限制。未算出时不返回截断或伪造的界，原表达式仍可继续展开。',
  ];
  notation.debug = {...notation.debug, annotation: describeBound,
    annotation_cache_stats: () => ({entries: cache.size, chars: cacheChars, hits, misses,
      maxEntries: cacheLimits.entries, maxChars: cacheLimits.chars}),
    annotation_limits: {...bridge.limits},
  };
  return notation;
};
const bridge = createBoundBridge(R, exact, forest,
  createBrowserYEngine({maxWidth:64,maxLayers:32,timeoutMs:25,maxWork:150000,maxAtoms:16000}),
  reconstructCandidate, {}, recursiveBound);
let originalRPD = null;
(function (register_notation) {
// Standalone RPD adjacency-view trial; published mathematical core is embedded unchanged.
(function (register) {
'use strict';
let definition;
(function (register_notation) {
// RPD mountain view v1.2.2; four explicit menu choices, compact roots, native NER diagram.
// Parent-first column comparison; no KB path semantics. No imports or network.
// Proof status: step descent proved; global standard well-order conditional on
// the graph-termination lemma; >=Y / equality with old path RPD not established.
(function(){
"use strict";
if(typeof register_notation!=="function")throw Error("请在 ne-rewritten 自定义记号中导入。");
'use strict';
// Root-reflection Path Diagrams (RPD), 2026-09-12.
// Independent finite rules; no Y evaluator is used by this module.
// All mathematical integers use BigInt. Resource guards throw, never truncate.
const DEFAULT = {maxWidth: 128n, maxAtoms: 40000, maxCopies: 32n,
  maxSeed: 32n, maxPath: 1000, maxOps: 5000000, ms: 5000};
function budget(options={}) {
  const b={...DEFAULT,...options,ops:0,start:Date.now()};
  b.tick=()=>{if(++b.ops>b.maxOps || Date.now()-b.start>b.ms) throw Error('resource budget');};
  return b;
}
function nat(n) {
  if(typeof n==='number' && !Number.isSafeInteger(n)) throw Error('unsafe integer');
  if(typeof n!=='number' && typeof n!=='bigint') throw Error('integer required');
  const v=BigInt(n); if(v<0n) throw Error('negative integer'); return v;
}
function cmp(a,b) {
  for(let i=0;i<Math.min(a.length,b.length);i++) if(a[i]!==b[i]) return a[i]<b[i]?-1:1;
  return Math.sign(a.length-b.length);
}
function close(g,b=budget()) {
  const size=nat(g.size); if(size>b.maxWidth) throw Error('width guard');
  const atoms=new Map();
  for(const raw of g.atoms) {
    if(raw.length!==4) throw Error('four fields required');
    const [k,r,p,c]=raw.map(nat);
    if(!(r<=p && p<c && c<size)) throw Error('invalid edge');
    for(let q=0n;q<=r;q++) {
      b.tick(); const e=[k,q,p,c]; atoms.set(e.join(','),e);
      if(atoms.size>b.maxAtoms) throw Error('atom guard');
    }
  }
  return {size,atoms:[...atoms.values()].sort(cmp)};
}
function seed(k,b=budget()) {
  k=nat(k); if(k>b.maxSeed) throw Error('seed guard');
  const atoms=[]; for(let j=0n;j<=k;j++) atoms.push([j,0n,0n,1n]);
  return {size:2n,atoms};
}
function end(g) {return g.atoms.filter(e=>e[3]===g.size-1n);}
function drop(g) {
  if(g.size===0n) throw Error('terminal diagram has no moves');
  return {size:g.size-1n,atoms:g.atoms.filter(e=>e[3]<g.size-1n)};
}
// Finite-iteration implementation of the displayed closed-form rule.
function copy(g,controller,n,b=budget()) {
  n=nat(n); if(n===0n) return drop(g);
  if(n>b.maxCopies) throw Error('copy guard');
  const e=controller.map(nat), last=g.size-1n;
  if(e[3]!==last || !g.atoms.some(a=>cmp(a,e)===0)) throw Error('controller absent');
  const [K,r,c]=e;
  if(last+n*(last-c)>b.maxWidth) throw Error('width guard');
  let out=drop(g),cut=c,root=r,facts=out.atoms,templates=end(g).map(a=>a.slice(0,3));
  for(let j=0n;j<n;j++) {
    b.tick(); const len=out.size,move=i=>i<cut?i:len+i-cut;
    const moved=facts.map(([k,q,p,v])=>[k,move(q),move(p),move(v)]),needs=[];
    for(const [k,q,p] of templates) for(let h=0n;h<=q;h++) {
      b.tick(); if(k<K || k===K && h<root) needs.push([k,h,p,len]);
    }
    out=close({size:len+(len-cut),atoms:[...out.atoms,...moved,...needs]},b);
    facts=moved; templates=templates.map(([k,q,p])=>[k,move(q),move(p)]);
    root=move(root); cut=len;
  }
  return out;
}
// Independent implementation directly from the mathematical formula.
function copyFormula(g,controller,n,b=budget()) {
  n=nat(n); if(n===0n) return drop(g);
  if(n>b.maxCopies) throw Error('copy guard');
  const e=controller.map(nat),x=g.size-1n,[K,r,c]=e,L=x-c;
  if(e[3]!==x || !g.atoms.some(a=>cmp(a,e)===0)) throw Error('controller absent');
  if(x+n*L>b.maxWidth) throw Error('width guard');
  const base=drop(g).atoms,top=end(g),atoms=[];
  for(let j=0n;j<=n;j++) {
    const f=i=>i<c?i:i+j*L;
    for(const [k,q,p,v] of base) {b.tick();atoms.push([k,f(q),f(p),f(v)]);}
    if(j===n) continue;
    for(const [k,q,p] of top) for(let h=0n;h<=f(q);h++) {
      b.tick();if(k<K || k===K && h<f(r)) atoms.push([k,h,f(p),x+j*L]);
    }
  }
  return close({size:x+n*L,atoms},b);
}

// The public expression is the COLUMN LIST itself, never an operation path.
const NE_LIMITS=Object.freeze({maxWidth:256n,maxAtoms:12000,maxCopies:128n,
  maxSeed:256n,maxPath:512,maxOps:500000,ms:400});
const NE_TEXT_LIMIT=400000,NE_CACHE_ENTRIES=64,NE_CACHE_ATOMS=48000;
const neCache=new Map(),neTraces=new Map();
let neCachedAtoms=0;
function neGuard(action){
  try{return action();}
  catch(error){
    if(/guard|resource budget/.test(String(error.message)))
      throw Error("RPD：达到计算保护上限；未返回截断或近似结果。("+error.message+")");
    throw error;
  }
}
// Display triples are (layer k, parent p, root q). Comparison priority is p,k,q.
function edgeCompare(a,b){return cmp([a[1],a[0],a[2]],[b[1],b[0],b[2]]);}
function graphColumns(g){
  if(g===null)return null;
  const result=Array.from({length:Number(g.size)},()=>[]);
  for(const [k,q,p,j] of g.atoms)result[Number(j)].push([k,p,q]);
  for(const column of result)column.sort((a,b)=>-edgeCompare(a,b));
  return result;
}
function columnCompare(a,b){
  for(let i=0;i<Math.min(a.length,b.length);i++){
    const c=edgeCompare(a[i],b[i]);if(c)return c;
  }
  return Math.sign(a.length-b.length);
}
function columnsCompare(a,b){
  if(a===null)return b===null?0:1;
  if(b===null)return -1;
  for(let j=0;j<Math.min(a.length,b.length);j++){
    const c=columnCompare(a[j],b[j]);if(c)return c;
  }
  return Math.sign(a.length-b.length);
}
function columnsText(columns){
  if(columns===null)return "Limit";
  if(!columns.length)return "∅";
  return columns.map(c=>"["+c.map(e=>"("+e.join(",")+")").join(",")+"]").join("");
}
function neRemember(g,trace){
  const columns=graphColumns(g),key=columnsText(columns);
  if(trace&&trace.length<=8192){
    const old=neTraces.get(key);
    if(!old||trace.length<old.length)neTraces.set(key,trace);
    while(neTraces.size>128)neTraces.delete(neTraces.keys().next().value);
  }
  const old=neCache.get(key);
  if(old){neCache.delete(key);neCache.set(key,old);return old;}
  const atoms=g===null?0:g.atoms.length;
  while(neCache.size>=NE_CACHE_ENTRIES||neCachedAtoms+atoms>NE_CACHE_ATOMS){
    const first=neCache.keys().next().value;if(first===undefined)break;
    const item=neCache.get(first);neCachedAtoms-=item.graph===null?0:item.graph.atoms.length;
    neCache.delete(first);
  }
  const kind=g===null?"limit":g.size===0n?"zero":end(g).length?"limit":"successor";
  const result={graph:g,columns,key,kind};
  neCache.set(key,result);neCachedAtoms+=atoms;return result;
}
function graphStep(g,n,b){
  n=nat(n);b.tick();
  if(g===null)return seed(n,b);
  if(g.size===0n)return g;
  const controls=end(g);
  if(n===0n||!controls.length)return drop(g);
  return copy(g,controls[controls.length-1],n,b);
}
function neInspect(raw){
  if(typeof raw!=="string")throw TypeError("请输入列列表文本。");
  if(raw.length>NE_TEXT_LIMIT)throw Error("列列表超过输入保护上限。");
  const input=raw.trim(),cached=neCache.get(input);
  if(cached){neCache.delete(input);neCache.set(input,cached);return cached;}
  if(/^(Limit|Omega|Ω)$/i.test(input))return neRemember(null,"Ω");
  if(input==="∅"||input==="0")return neRemember({size:0n,atoms:[]});
  if(input==="1")return neRemember({size:1n,atoms:[]});
  const trace=input.match(/^(?:Ω|Limit|Omega)((?:\s*\[\s*\d+\s*\])+)\s*$/i);
  if(trace){
    const indices=[...trace[1].matchAll(/\d+/g)].map(m=>BigInt(m[0]));
    if(indices.length>NE_LIMITS.maxPath)throw Error("操作记录超过长度保护上限。");
    const b=budget(NE_LIMITS);let g=null;
    for(const n of indices)g=graphStep(g,n,b);
    return neRemember(g,"Ω"+indices.map(n=>"["+n+"]").join(""));
  }
  // Only structural validity is checked here, not standard reachability from Ω.
  const tokens=input.match(/\d+|[\[\](),]/g)||[];
  if(!tokens.length||tokens.join("")!==input.replace(/\s/g,""))
    throw TypeError("格式应为 [列0关系][列1关系]…；关系写 (k,p,q)，空图写 ∅。");
  let i=0,j=0;const atoms=[];
  const take=s=>{if(tokens[i++]!==s)throw TypeError("列列表格式错误：期待 "+s+"。");};
  const integer=()=>{const t=tokens[i++];if(!t||!/^\d+$/.test(t))throw TypeError("关系字段必须是自然数。");return BigInt(t);};
  while(i<tokens.length){
    if(BigInt(j)>=NE_LIMITS.maxWidth)throw Error("width guard");
    take("[");
    if(tokens[i]!=="]"){
      for(;;){
        take("(");const k=integer();take(",");const p=integer();take(",");const q=integer();take(")");
        atoms.push([k,q,p,BigInt(j)]);
        if(atoms.length>NE_LIMITS.maxAtoms)throw Error("atom guard");
        if(tokens[i]!==",")break;take(",");
      }
    }
    take("]");j++;
  }
  return neRemember(close({size:BigInt(j),atoms},budget(NE_LIMITS)));
}
function neCompare(a,b){return neGuard(()=>columnsCompare(neInspect(a).columns,neInspect(b).columns));}
function neFS(raw,index){
  return neGuard(()=>{
    const n=nat(index),before=neInspect(raw),g=graphStep(before.graph,n,budget(NE_LIMITS));
    const trace=neTraces.get(before.key);
    const after=neRemember(g,trace?trace+"["+n+"]":undefined);
    if(before.kind!=="zero"&&columnsCompare(after.columns,before.columns)>=0)
      throw Error("内部一致性检查失败：候选展开没有在列字典序下严格下降。");
    return after.key;
  });
}
function viewEscape(s){return String(s).replace(/&/g,"&amp;").replace(/</g,"&lt;").replace(/>/g,"&gt;").replace(/"/g,"&quot;");}
function viewPlain(raw){return neGuard(()=>neInspect(raw).key);}
function viewParse(raw){return viewPlain(raw);}
function viewListHTML(raw){
  const state=neInspect(raw);
  if(state.columns===null)return "Ω";
  return '<span style="white-space:nowrap">'+viewEscape(state.key)+'</span>';
}
function viewLatex(raw){
  const c=neInspect(raw).columns;if(c===null)return "\\Omega";if(!c.length)return "\\varnothing";
  return c.map(col=>"\\left["+col.map(e=>"("+e.join(",")+")").join(",")+"\\right]").join("");
}
const VIEW_MAX_EDGES=3000,VIEW_MAX_SVG_CHARS=2000000;

function viewSVG(raw) {
  return neGuard(()=>{
    const state=neInspect(raw),g=state.graph;
    const textColor="currentColor",rootColor="var(--color-danger,currentColor)",
      guide="var(--color-border-light,currentColor)",background="var(--color-bg,transparent)";
    const svgStart=(w,h,description)=>'<svg xmlns="http://www.w3.org/2000/svg" role="img" aria-label="'+
      viewEscape(description)+'" width="'+w+'" height="'+h+'" viewBox="0 0 '+w+' '+h+
      '" style="display:block;max-width:none;font-family:monospace"><title>'+viewEscape('RPD 列图')+'</title>';
    const text=(x,y,s,size=12,anchor="start",color=textColor)=>
      '<text x="'+x+'" y="'+y+'" font-size="'+size+'" dominant-baseline="middle" text-anchor="'+anchor+
      '" fill="'+color+'">'+viewEscape(s)+'</text>';
    const line=(x1,y1,x2,y2,color=textColor,width=1,dash="")=>
      '<line x1="'+x1+'" y1="'+y1+'" x2="'+x2+'" y2="'+y2+'" stroke="'+color+
      '" stroke-width="'+width+'"'+(dash?' stroke-dasharray="'+dash+'"':"")+'/>';
    const circle=(x,y,r,color=textColor,fill=false)=>
      '<circle cx="'+x+'" cy="'+y+'" r="'+r+'" stroke="'+color+'" stroke-width="1.4" fill="'+
      (fill?color:background)+'"/>';
    if(g===null)return svgStart(300,60,"RPD 顶端")+
      text(10,18,"Ω · RPD 顶端",18)+text(10,44,"展开后进入有限种子图。")+"</svg>";
    const m=Number(g.size);
    if(g.atoms.length>VIEW_MAX_EDGES)throw Error("全图有 "+g.atoms.length+
      " 条边，超过绘图保护上限 "+VIEW_MAX_EDGES+"；未绘制任何局部图。邻接列表仍然完整。");
    const edges=[...g.atoms].sort((a,b)=>cmp([a[0],a[3],a[2],a[1]],[b[0],b[3],b[2],b[1]]));
    const left=116,dx=46,rowHeight=34,y0=100;
    const width=Math.max(370,left+Math.max(1,m)*dx+18);
    const height=edges.length?y0+edges.length*rowHeight+40:132;
    const x=j=>left+Number(j)*dx;
    let out=svgStart(width,height,m+" 列、"+edges.length+" 条边的完整 RPD 图；实线 j→p，红色标记根 q。");
    out+=text(10,16,"完整图 · "+m+" 列 · "+edges.length+" 条边",14);
    out+=text(10,40,"实线 j→p；红圈/虚线标记根 q。k 为关系层。",12);
    if(!m)out+=text(12,81,"∅  空图",19)+text(12,110,
      "空列表为 0；没有历史回退。");
    for(let j=0;j<m;j++){
      out+='<g data-rpd-column="'+j+'">'+text(x(j),65,j,12,"middle")+circle(x(j),80,3,textColor,true);
      if(edges.length)out+=line(x(j),89,x(j),height-37,guide);
      out+='</g>';
    }
    if(m&&!edges.length)out+=text(10,110,"只有列节点，没有边。");
    edges.forEach(([k,q,p,j],i)=>{
      const y=y0+i*rowHeight,xp=x(p),xj=x(j),xq=x(q);
      out+='<g data-rpd-edge="'+i+'" data-relation="'+[k,q,p,j].join(',')+'">'+text(8,y,"k="+k+"  q="+q,12);
      out+=line(xp+5,y,xj-5,y,textColor,1.6)+
        line(xp+5,y,xp+12,y-4,textColor,1.6)+line(xp+5,y,xp+12,y+4,textColor,1.6);
      out+=circle(xp,y,3.5,textColor,true)+circle(xj,y,3.5);
      out+=line(xq,y+11,xp,y+11,rootColor,1,"3 3")+
        circle(xq,y+11,2.8,rootColor)+line(xp,y+7,xp,y+3,rootColor)+'</g>';
    });
    if(edges.length)out+=text(10,height-17,"全部 "+edges.length+" 条边均已绘制；小根边也逐条保留。");
    out+="</svg>";
    if(out.length>VIEW_MAX_SVG_CHARS)throw Error("完整 SVG 超过绘制大小保护上限；未返回局部图。");
    return out;
  });
}


function viewGraphHTML(raw){
  try{return viewSVG(raw);}
  catch(error){
    if(!/绘图保护|绘制大小保护/.test(String(error.message)))throw error;
    return '<span style="color:var(--color-danger,currentColor)">'+viewEscape(error.message)+'</span>';
  }
}
function tracePlain(raw){const state=neInspect(raw);return neTraces.get(state.key)||state.key;}
function traceHTML(raw){
  const state=neInspect(raw),trace=neTraces.get(state.key);
  return trace?viewEscape(trace):"（无操作记录；记号由列列表确定）";
}
// Inspect the first different column IN its shared left context.
// One local step = FS[1], then delete copied columns to the original width.
function trimGraph(g,m){return {size:m,atoms:g.atoms.filter(e=>e[3]<m)};}
function lowerLastColumn(g,b){
  const edges=end(g),e=edges[edges.length-1];if(!e)return null;
  const [K,r,c,x]=e;
  return close({size:g.size,atoms:[
    ...g.atoms.filter(f=>f[3]<x),
    ...g.atoms.filter(f=>f[3]===c).map(([k,q,p])=>[k,q,p,x]),
    ...edges.filter(([k,q])=>k<K||k===K&&q<r)
  ]},b);
}
function firstDifferenceCheck(rawA,rawB,maxSteps=256){
  if(!Number.isSafeInteger(maxSteps)||maxSteps<1||maxSteps>10000)
    throw Error("可达性核验步数必须为 1..10000。");
  return neGuard(()=>{
    const a=neInspect(rawA),b=neInspect(rawB),order=columnsCompare(a.columns,b.columns);
    if(!order)return {status:"equal",steps:0};
    if(a.graph===null||b.graph===null)return {status:"not-checked",reason:"顶端不做首差列核验"};
    let j=0;
    while(j<Math.min(a.columns.length,b.columns.length)&&!columnCompare(a.columns[j],b.columns[j]))j++;
    if(j===Math.min(a.columns.length,b.columns.length))
      return {status:"reachable",via:"delete suffix",steps:Math.abs(a.columns.length-b.columns.length),direction:order>0?"a-to-b":"b-to-a"};
    let current=trimGraph(order>0?a.graph:b.graph,BigInt(j+1));
    const target=trimGraph(order>0?b.graph:a.graph,BigInt(j+1)),targetColumns=graphColumns(target);
    const work=budget(NE_LIMITS);
    let steps=0;
    try{
      for(;steps<maxSteps;steps++){
        work.tick();
        const next=lowerLastColumn(current,work);
        if(next===null)return {status:"incomparable",column:j,steps,reason:"无可用的同宽下降步"};
        const c=columnsCompare(graphColumns(next),targetColumns);
        if(!c)return {status:"reachable",column:j,steps:steps+1,direction:order>0?"a-to-b":"b-to-a",
          scope:"共同前缀加首个不同列",via:"FS[1] then delete copied suffix"};
        if(c<0)return {status:"incomparable",column:j,steps:steps+1,
          reason:"所有下一项在首差列处都已小于目标；后续展开也严格下降",
          from:columnsText(graphColumns(current)),next:columnsText(graphColumns(next)),target:columnsText(targetColumns)};
        current=next;
      }
      return {status:"unknown",column:j,steps,reason:"达到迭代上限，不代表不可达"};
    }catch(error){
      if(/guard|resource budget/.test(String(error.message)))
        return {status:"unknown",column:j,steps,reason:"达到资源保护上限，不代表不可达"};
      throw error;
    }
  });
}

// Local-column height: 1 for an empty relation column; otherwise 1+h(T(C)).
// T is FS[1] restricted to the original width. Counts are BigInt throughout.
const NUMBER_LIMITS=Object.freeze({maxWork:8000000,maxMemo:8192,maxCells:250000,
  maxMs:400,maxText:100000,maxCacheEntries:32,maxCacheChars:600000});
const numberCache=new Map();
let numberCacheChars=0;
function numberLimit(reason){
  const error=Error("数字序列计算达到保护上限（"+reason+"）；请使用列表或图。未返回近似数字。");
  error.name="RPDNumberLimit";return error;
}
function calculateColumnNumbers(g,requested={}){
  const bounds={...NUMBER_LIMITS};
  for(const name of ["maxWork","maxMemo","maxCells","maxMs"]){
    if(requested[name]===undefined)continue;
    const value=requested[name];
    if(!Number.isSafeInteger(value)||value<1||value>bounds[name])throw Error("数字核验限额无效："+name);
    bounds[name]=value;
  }
  const start=Date.now();
  let work=0,cells=0,maxDepth=0;
  function tick(){
    if(++work>bounds.maxWork)throw numberLimit("操作次数");
    if((work&1023)===0&&Date.now()-start>bounds.maxMs)throw numberLimit("时间");
  }
  if(g===null)return {values:null,stats:{work:0,memoEntries:0,memoCells:0,pairs:0,maxDepth:0}};
  const labels=new Map();
  for(const [k,q]of g.atoms){tick();labels.set(k+","+q,[k,q]);}
  const pairs=[...labels.values()].sort((a,b)=>{tick();return cmp(a,b);});
  const ids=new Map(pairs.map((pair,i)=>[pair.join(","),i]));
  const rows=Array.from({length:Number(g.size)},()=>new Map());
  const highest=Array(rows.length).fill(-1);
  for(const [k,q,p,j]of g.atoms){
    tick();const c=Number(j),id=ids.get(k+","+q),parent=Number(p),row=rows[c];
    row.set(id,Math.max(row.get(id)??-1,parent));highest[c]=Math.max(highest[c],id);
  }
  // At a fixed (k,q), only its maximum parent can ever be selected; the entire
  // group is removed together. Thus this profile retains EXACT counting data.
  const memo=new Map();
  function normalise(c,cut,depth){
    tick();maxDepth=Math.max(maxDepth,depth);
    if(highest[c]<cut)return {steps:0n,rest:rows[c]};
    const key=c+":"+cut,saved=memo.get(key);if(saved)return saved;
    const active=new Map(rows[c]);let steps=0n;
    for(let i=highest[c];i>=cut;i--){
      tick();const parent=active.get(i);if(parent===undefined)continue;
      if(!(parent<c))throw Error("数字计数内部错误：父列没有向左严格减小。");
      active.delete(i);
      // Remaining active groups all have lower priority than i. Evaluate the
      // source column's >=i groups once, independently of that lower remainder.
      const sub=normalise(parent,i,depth+1);steps+=1n+sub.steps;
      for(const [id,p]of sub.rest){
        tick();if(id>=i)throw Error("数字计数内部错误：阈值化简未完成。");
        active.set(id,Math.max(active.get(id)??-1,p));
      }
    }
    if(memo.size>=bounds.maxMemo)throw numberLimit("子问题个数");
    cells+=active.size;if(cells>bounds.maxCells)throw numberLimit("缓存关系数");
    const result={steps,rest:active};memo.set(key,result);return result;
  }
  const values=rows.map((_,j)=>normalise(j,0,1).steps+1n);
  if(Date.now()-start>bounds.maxMs)throw numberLimit("时间");
  return {values,stats:{work,memoEntries:memo.size,memoCells:cells,
    pairs:pairs.length,maxDepth,elapsedMs:Date.now()-start}};
}
function numberInspect(raw){
  return neGuard(()=>{
    const state=neInspect(raw),saved=numberCache.get(state.key);
    if(saved){numberCache.delete(state.key);numberCache.set(state.key,saved);return saved;}
    const result=calculateColumnNumbers(state.graph);
    const text=result.values===null?"Limit":result.values.length?result.values.join(","):"0";
    if(text.length>NUMBER_LIMITS.maxText)throw numberLimit("完整数字文本长度");
    const chars=state.key.length+text.length;
    if(chars<=NUMBER_LIMITS.maxCacheChars){
      while(numberCache.size>=NUMBER_LIMITS.maxCacheEntries||numberCacheChars+chars>NUMBER_LIMITS.maxCacheChars){
        const first=numberCache.keys().next().value;if(first===undefined)break;
        numberCacheChars-=numberCache.get(first).chars;numberCache.delete(first);
      }
      const item={...result,text,chars};numberCache.set(state.key,item);numberCacheChars+=chars;return item;
    }
    return {...result,text,chars:0};
  });
}
function numberPlain(raw){
  try{return numberInspect(raw).text;}
  catch(error){if(error.name!=="RPDNumberLimit")throw error;return "（数字序列未计算：达到保护上限；请查看列表）";}
}
function numberHTML(raw){
  try{
    const result=numberInspect(raw),values=result.values;
    if(values===null)return "Ω";
    if(!values.length)return "0";
    return '<span style="white-space:nowrap">'+values.map((value,j)=>
      '<span data-rpd-number-column="'+j+'" title="列 '+j+'；包含最后一次删列">'+value+'</span>').join(",")+'</span>';
  }catch(error){
    if(error.name!=="RPDNumberLimit")throw error;
    return '<span style="color:var(--color-danger,currentColor)">'+viewEscape(error.message)+'</span>';
  }
}
function numberLatex(raw){
  try{const values=numberInspect(raw).values;return values===null?"\\Omega":values.length?"\\left("+values.join(",")+"\\right)":"0";}
  catch(error){if(error.name!=="RPDNumberLimit")throw error;return "\\text{Numeric view resource limit; use list view}";}
}

// RPD mountain presentation. No changes to graph identity, FS, or comparison.
// One node represents (k,p,j) with all roots 0..q_max; this is lossless because
// neInspect returns root-down-closed graphs. No parent/transitive edge is removed.
const MOUNTAIN_LIMITS=Object.freeze({maxGroups:2000,maxLayers:128,maxTracks:900,
  maxDimension:16000,maxPixels:12000000,maxLabel:160,maxWork:300000,
  maxMs:400,maxSvgChars:2500000});
function mountainLimit(reason){
  const error=Error("RPD 山脉图："+reason+"，达到完整绘图保护上限；未绘制局部图，请查看列表。");
  error.name="RPDMountainLimit";return error;
}
function mountainTextWidth(text,size){
  // Conservative estimate, with inherited font and no browser DOM dependency.
  let units=0;for(const char of String(text))units+=char.codePointAt(0)>255?1.12:.72;
  return Math.ceil(units*size);
}
function mountainModel(raw){
  const g=neInspect(raw).graph;
  if(g===null)return {kind:"top",columns:[],layers:[],groups:[],atomCount:0};
  const started=Date.now();let work=0;
  function tick(){
    if(++work>MOUNTAIN_LIMITS.maxWork||(work%512===0&&Date.now()-started>MOUNTAIN_LIMITS.maxMs))
      throw mountainLimit("布局计算量");
  }
  const groups=new Map();
  for(const [k,q,p,j]of g.atoms){
    tick();const key=[k,p,j].join(","),old=groups.get(key);
    if(old){if(q>old.q)old.q=q;}
    else{
      if(groups.size>=MOUNTAIN_LIMITS.maxGroups)throw mountainLimit("关系组个数");
      const layer=String(k);if(layer.length>MOUNTAIN_LIMITS.maxLabel)throw mountainLimit("层标记长度");
      groups.set(key,{k,q,p:Number(p),j:Number(j)});
    }
  }
  const ordered=[...groups.values()].sort((a,b)=>{
    tick();return cmp([a.k,BigInt(a.j),BigInt(a.p)],[b.k,BigInt(b.j),BigInt(b.p)]);
  });
  const width=Number(g.size),layers=[];let band,trackCount=0;
  ordered.forEach((group,id)=>{
    tick();
    if(!band||band.k!==String(group.k)){
      if(layers.length>=MOUNTAIN_LIMITS.maxLayers)throw mountainLimit("层数");
      band={k:String(group.k),top:Array(width).fill(0),nodes:[],used:new Set(),tracks:0};layers.push(band);
    }
    const targetTrack=band.top[group.p],track=Math.max(band.top[group.j]+1,targetTrack+1);
    trackCount+=Math.max(0,track-band.tracks);
    if(trackCount>MOUNTAIN_LIMITS.maxTracks)throw mountainLimit("纵向排版轨道数");
    band.tracks=Math.max(band.tracks,track);band.top[group.j]=track;
    band.used.add(group.p);band.used.add(group.j);
    // Track numbers position the drawing only; they are NOT new RPD layers.
    band.nodes.push({id,k:String(group.k),q:String(group.q),p:group.p,j:group.j,track,targetTrack});
  });
  let numberValues,numberWarning;
  try{numberValues=numberInspect(raw).values.map(String);}
  catch(error){
    if(error.name!=="RPDNumberLimit")throw error;
    numberValues=null;numberWarning="数字计数超限：底部改标列号；全部关系仍完整。";
  }
  if(numberValues?.some(value=>value.length>MOUNTAIN_LIMITS.maxLabel)){
    numberValues=null;numberWarning="数字文本过长：底部改标列号；全部关系仍完整。";
  }
  if(Date.now()-started>MOUNTAIN_LIMITS.maxMs+NUMBER_LIMITS.maxMs)throw mountainLimit("布局时间");
  const columns=Array.from({length:width},(_,j)=>({j,number:numberValues?.[j]??null}));
  const cleanLayers=layers.map(layer=>({...layer,used:[...layer.used].sort((a,b)=>a-b)}));
  return {kind:width?"finite":"zero",columns,layers:cleanLayers,
    groups:cleanLayers.flatMap(layer=>layer.nodes),atomCount:g.atoms.length,numberWarning};
}
function mountainMessage(lines,isWarning=false){
  const width=Math.max(260,...lines.map(text=>mountainTextWidth(text,13)+32));
  return {width,height:24+lines.length*25,elements:[],extra_text:lines.map((text,i)=>({
    text,x:16,y:18+i*25,size:13,align:"left",color:{type:isWarning?"red":"text"}
  })),_rpd:{complete:!isWarning,warning:isWarning}};
}
function mountainDiagram(raw,data={}){
  const model=mountainModel(raw),invert=!!data.invert_vertical,fullRoots=!!data.full_root_labels;
  if(model.kind==="top")return mountainMessage(["Ω · RPD 顶端","展开后显示有限种子的山脉图。"]);
  if(model.kind==="zero")return mountainMessage(["0 · 空图（没有列，也没有关系）"]);
  const black={type:"text"},gray={type:"gray"},red={type:"red"};
  const colGap=Number.isFinite(data.column_gap)?Math.max(32,Math.min(160,data.column_gap)):48;
  const rowGap=36,padding=24;
  const labelWidth=Math.max(30,...model.layers.map(layer=>mountainTextWidth("k="+layer.k,12)));
  const left=labelWidth+32,xs=[],columnWidths=[],rootWidths=Array(model.columns.length).fill(0);let cursor=left;
  const rootLabel=node=>fullRoots?"q="+node.q:node.q==="0"?"":node.q;
  for(const node of model.groups){
    const label=rootLabel(node);
    if(label)rootWidths[node.j]=Math.max(rootWidths[node.j],mountainTextWidth(label,12));
  }
  for(const col of model.columns){
    const cell=Math.max(colGap,mountainTextWidth(col.number??"j="+col.j,16)+20,
      mountainTextWidth("j="+col.j,10)+12,rootWidths[col.j]?rootWidths[col.j]*2+18:0);
    columnWidths.push(cell);xs.push(cursor+cell/2);cursor+=cell;
  }
  let offset=64;
  for(const layer of model.layers){layer.offset=offset;offset+=rowGap*layer.tracks+44;}
  const extent=model.layers.length?offset-24:72;
  const footer=[fullRoots?"q=t：包含根 0…t。":"红字 t：根 0…t；未标：根 0。",
    "斜线→父列；灰线／层内高度仅排版。"];
  if(model.numberWarning)footer.push(model.numberWarning);
  const width=Math.ceil(Math.max(cursor+padding,...footer.map(text=>mountainTextWidth(text,12)+32)));
  const plotHeight=extent+2*padding,height=Math.ceil(plotHeight+footer.length*22+18);
  if(width>MOUNTAIN_LIMITS.maxDimension||height>MOUNTAIN_LIMITS.maxDimension||width*height>MOUNTAIN_LIMITS.maxPixels)
    throw mountainLimit("画布尺寸／像素数");
  const y=d=>invert?padding+d:padding+extent-d;
  const elements=[],extra_text=[];
  const line=(x1,y1,x2,y2,color=black,weight=1,meta)=>elements.push({type:"line",x1,y1,x2,y2,
    stroke:true,stroke_color:color,width:weight,...(meta?{_rpd:meta}:{})});
  const dot=(x,y,color=black,r=2.7,meta)=>elements.push({type:"circle",x,y,r,stroke:false,
    fill:true,fill_color:color,...(meta?{_rpd:meta}:{})});
  const text=(label,x,y,size=12,color=black,align="left",meta)=>extra_text.push({
    text:String(label),x,y,size,color,align,...(meta?{_rpd:meta}:{})});
  // Light spines are alignment guides, not additional directed graph edges.
  for(const col of model.columns){
    line(xs[col.j],y(30),xs[col.j],y(extent),gray,.65,{kind:"column-guide",j:col.j});
    text(col.number??"j="+col.j,xs[col.j],y(22),16,black,"center",{kind:"column",j:col.j});
    if(col.number!==null)text("j="+col.j,xs[col.j],y(0),10,gray,"center");
  }
  for(const layer of model.layers){
    const base=layer.offset;
    line(left-8,y(base),width-padding,y(base),gray,.65,{kind:"layer-guide",k:layer.k});
    text("k="+layer.k,left-16,y(base+layer.tracks*rowGap/2),12,black,"right",{kind:"layer",k:layer.k});
    for(const j of layer.used)if(layer.top[j]===0)
      dot(xs[j],y(base),gray,2,{kind:"anchor",j,k:layer.k});
    for(const node of layer.nodes){
      const xj=xs[node.j],xp=xs[node.p],yj=y(base+node.track*rowGap),yp=y(base+node.targetTrack*rowGap);
      const dx=xp-xj,dy=yp-yj,length=Math.hypot(dx,dy),ux=dx/length,uy=dy/length;
      line(xj+ux*4,yj+uy*4,xp-ux*4,yp-uy*4,black,1.2,{kind:"relation",...node});
    }
  }
  // Place all node labels after all lines, using host extra_text (inherited font).
  for(const layer of model.layers)for(const node of layer.nodes){
    const cx=xs[node.j],cy=y(layer.offset+node.track*rowGap);
    dot(cx,cy,black,2.7,{kind:"node",...node});
    // Left/up is away from both the left/down parent leg and right/up children.
    const label=rootLabel(node);
    if(label)text(label,cx-7,cy+(invert?10:-10),12,red,"right",{kind:"root",...node});
  }
  footer.forEach((label,i)=>text(label,16,plotHeight+10+i*22,12,
    model.numberWarning&&i===footer.length-1?red:gray));
  return {width,height,elements,extra_text,_rpd:{complete:true,kind:model.kind,
    columns:model.columns.length,groups:model.groups.length,atoms:model.atomCount,
    invert_vertical:invert,full_root_labels:fullRoots,plotHeight,extent,padding,columnWidths,numberWarning:model.numberWarning??null}};
}
function mountainSafeDiagram(raw,data={}){
  try{return mountainDiagram(raw,data);}
  catch(error){
    if(error.name!=="RPDMountainLimit")throw error;
    return mountainMessage(["完整山脉图超过保护上限。",error.message],true);
  }
}
function mountainColor(color){
  if(color?.type==="gray")return "var(--color-text-muted,#85858c)";
  if(color?.type==="red")return "var(--color-danger,#b84a40)";
  return "currentColor";
}
function mountainSvg(raw,data={}){
  const diagram=mountainDiagram(raw,data),{width,height}=diagram;
  let out='<svg xmlns="http://www.w3.org/2000/svg" role="img" width="'+width+'" height="'+height+
    '" viewBox="0 0 '+width+' '+height+'" style="display:block;max-width:none;font-family:inherit" aria-label="RPD 完整山脉图">'+
    '<title>RPD 完整山脉图</title><desc>横向按列，纵向按层 k；红字 t 或 q=t 表示根 0 到 t 全部保留，未标根值的黑点表示根 0。灰线仅为对齐辅助线。</desc>';
  function metadata(meta){
    if(!meta)return "";
    if(meta.kind==="column")return ' data-rpd-column="'+meta.j+'"';
    if(meta.kind==="relation")return ' data-rpd-group="'+meta.id+'" data-relation="'+
      [meta.k,meta.q,meta.p,meta.j].join(',')+'"';
    return ' data-rpd-kind="'+meta.kind+'"';
  }
  for(const el of diagram.elements){
    const meta=metadata(el._rpd);
    if(el.type==="line")out+='<line x1="'+el.x1+'" y1="'+el.y1+'" x2="'+el.x2+'" y2="'+el.y2+
      '" stroke="'+mountainColor(el.stroke_color)+'" stroke-width="'+el.width+'"'+meta+'/>';
    else if(el.type==="circle")out+='<circle cx="'+el.x+'" cy="'+el.y+'" r="'+el.r+'" fill="'+
      mountainColor(el.fill_color)+'"'+meta+'/>';
  }
  for(const t of diagram.extra_text)out+='<text x="'+t.x+'" y="'+t.y+'" font-size="'+t.size+
    '" dominant-baseline="middle" text-anchor="'+({left:"start",center:"middle",right:"end"}[t.align])+
    '" fill="'+mountainColor(t.color)+'"'+metadata(t._rpd)+'>'+viewEscape(t.text)+'</text>';
  out+='</svg>';
  if(out.length>MOUNTAIN_LIMITS.maxSvgChars)throw mountainLimit("完整 SVG 文本长度");
  return out;
}
function mountainHTML(raw){
  try{return mountainSvg(raw);}
  catch(error){
    if(error.name!=="RPDMountainLimit")throw error;
    return '<span style="color:var(--color-danger,currentColor)">'+viewEscape(error.message)+'</span>';
  }
}
const mountainControl={
  default_data:{invert_vertical:false,column_gap:48,full_root_labels:false},
  settings:[
    {type:"boolean",name:"上下翻转",field_name:"invert_vertical"},
    {type:"number",name:"最小列间距",min:32,max:160,field_name:"column_gap"},
    {type:"boolean",name:"完整根标记（含 q=0）",field_name:"full_root_labels"},
    {type:"info",name:"简写：红字 t 含根 0…t，无红字即根 0。所有父列关系均保留。"}
  ],
  draw_diagram:mountainSafeDiagram,
  handle_action:(data,action)=>action.type==="scroll"&&["up","down"].includes(action.direction)?
    {...data,invert_vertical:action.direction==="down"}:null
};

register_notation({
  id:"rpd-column-mountain-v1",
  name:"RPD（山脉图·四视图）",simple_name:"RPD·山脉",
  description:[
    "记号本身是列列表；同图相等，空列表 ∅ 为 0，不再按历史路径赋值或回退。",
    "每个方括号是一列；三元组 (k,p,q) 表示层、父列、根列。所有列从 0 编号。",
    "比较：列内按父列 p→层 k→根 q 降序排列，再从左到右逐列、逐项按数值比较；真前缀较小。",
    "非空极限项 [0] 删末列；[n] 固定按 (k,q,p) 最大的控制边新增 n 份副本，源块保留。顶端 Ω[n] 仍为种子 S_n。",
    "非空无控制边时各指标都删末列；空图各指标仍为空图。非顶端基本列保持逐列前缀递增。",
    "输入可用列列表，或构造记录 Ω[种子][指标]…。纯列表自动去重并补全小根关系。",
    "标准式仅指从顶端经这些展开可达的图；手工输入只校验有限图条件，不判定标准可达性。",
    "操作序列是辅助记录，不参与比较；相同图的不同历史合并。记录只缓存在当前会话，刷新或缓存淘汰后可能不显示。",
    "在等价表示菜单中直接选择：列表、数字序列、操作序列、画图；(None) 也显示默认列表。显示模式的纯文本／HTML／LaTeX 是另一组选项。画图视图需 HTML，亦可使用原生显示图表。超限拒绝，不返回局部图。",
    "山脉图横向按列，纵向按真实层 k 分区；区内错层只是排版。斜线指向父列，灰线仅对齐；红字 t 含根 0…t，不标即根 0。不删除任何父列捷径，图表设置可恢复完整 q= 标记。",
    "数字表示每列局部清空的次数，包含最后一次删列；空关系列为 1。末列数字大于 1 时，正指标展开使旧末列位置的数字恰好减 1，然后追加新列。指标 0 或末列数字为 1 时直接删末列。",
    "数字用 BigInt 精确递归计数，不逐次执行可能极长的下降链。数列仅作显示；独立输入仍用列表或 Ω[...] 构造记录。",
    "父列优先的一步下降可直接证明。标准式良序性依赖原图终止引理的条件性证明；与 Y 或旧路径系统等强尚未证明。"
  ],
  display:{name:"列表",plain:viewPlain,html:viewListHTML,latex:viewLatex,from_display:viewParse},
  display_equiv:{
    "列表":{name:"列表",plain:viewPlain,html:viewListHTML,latex:viewLatex,from_display:viewParse},
    "数字序列":{name:"数字序列",plain:numberPlain,html:numberHTML,latex:numberLatex},
    "操作序列":{name:"操作序列",plain:tracePlain,html:traceHTML,from_display:viewParse},
    "画图":{name:"画图",plain:viewPlain,html:mountainHTML,latex:viewLatex,from_display:viewParse}
  },
  draw_diagram:mountainControl,
  compare:neCompare,is_limit:raw=>neGuard(()=>neInspect(raw).kind==="limit"),
  FS:neFS,FS_alter:neFS,FS_short:neFS,
  init:()=>["Limit",neRemember({size:1n,atoms:[]},"Ω[0][0]").key,
    neRemember({size:0n,atoms:[]},"Ω[0][0][0]").key],
  debug:{
    version:"1.2.2-four-explicit-menu-choices",
    column_numbers:raw=>{const values=numberInspect(raw).values;return values===null?null:values.map(String);},
    number_audit:(raw,limits)=>{const result=calculateColumnNumbers(neInspect(raw).graph,limits);return {values:result.values===null?null:result.values.map(String),stats:result.stats};},
    number_cache_stats:()=>({entries:numberCache.size,chars:numberCacheChars,maxEntries:NUMBER_LIMITS.maxCacheEntries,maxChars:NUMBER_LIMITS.maxCacheChars}),
    graph:raw=>neGuard(()=>{const g=neInspect(raw).graph;return g===null?null:{size:String(g.size),atoms:g.atoms.map(e=>e.map(String))};}),
    type:raw=>neGuard(()=>neInspect(raw).kind),
    adjacency:raw=>neGuard(()=>{const c=neInspect(raw).columns;return c===null?null:c.map(col=>col.map(e=>e.map(String)));}),
    full_svg:mountainSvg,raw_relation_svg:viewSVG,
    mountain_model:mountainModel,mountain_diagram:mountainDiagram,mountain_limits:{...MOUNTAIN_LIMITS},
    first_difference_reachability:firstDifferenceCheck,
    first_column_step:raw=>neGuard(()=>{const g=neInspect(raw).graph;if(g===null||!end(g).length)return null;
      return neRemember(lowerLastColumn(g,budget(NE_LIMITS))).key;}),
    cache_stats:()=>({entries:neCache.size,atoms:neCachedAtoms,traces:neTraces.size,
      maxEntries:NE_CACHE_ENTRIES,maxAtoms:NE_CACHE_ATOMS,maxTraces:128})
  }
});
})();
})(value => { if (definition) throw Error('Duplicate notation registration'); definition = value; });

// Shared presentation-only source. The two delivered scripts inline this file.
// It never changes an expression, expansion rule, comparison, or existing view.
function addAdjacencyDisplays(notation, config) {
  'use strict';
  const TEXT = '邻接表（文字）', TABLE = '邻接表（图）';
  const limits = Object.freeze({ ms: config.ms, work: 1000000,
    text: 1000000, slots: 500000, layers: 256, cells: 250000,
    dimension: 32768, pixels: 30000000, svg: 2500000, label: 160 });
  const escape = value => String(value).replace(/&/g, '&amp;').replace(/</g, '&lt;')
    .replace(/>/g, '&gt;').replace(/"/g, '&quot;');
  function fail(reason) {
    const error = Error(config.label + ' 邻接表：' + reason + '超限；未返回截断结果，请查看原列表。');
    error.name = 'AdjacencyViewLimit'; throw error;
  }
  function budget() {
    const started = Date.now(); let work = 0;
    return () => {
      if (++work > limits.work || ((work & 255) === 0 && Date.now() - started > limits.ms))
        fail('计算预算');
    };
  }
  function inspect(raw, tick) {
    const input = config.read(raw);
    if (input === null) return null;
    const columns = [], layers = new Map(); let groups = 0;
    for (let j = 0; j < input.length; j++) {
      tick(); const column = new Map(); columns.push(column);
      for (const [rawK, rawP, rawQ] of input[j]) {
        tick(); const k = BigInt(rawK).toString(), p = Number(rawP), q = BigInt(rawQ);
        if (k.length > limits.label) fail('层标文字');
        if (!column.has(k)) column.set(k, new Map());
        const row = column.get(k), old = row.get(p);
        if (old === undefined) groups++;
        if (old === undefined || q > old) row.set(p, q);
      }
      for (const [k, parents] of column) {
        tick(); if (!layers.has(k)) layers.set(k, { k, entries: [] });
        for (const [p, q] of parents) layers.get(k).entries.push({ k, p, q: String(q), j });
      }
    }
    return { columns, layers: [...layers.values()].sort((a, b) =>
      BigInt(a.k) < BigInt(b.k) ? -1 : BigInt(a.k) > BigInt(b.k) ? 1 : 0), groups };
  }
  function plain(raw) {
    const tick = budget(), graph = inspect(raw, tick);
    if (graph === null) return config.top;
    if (!graph.columns.length) return '∅';
    const output = []; let slots = 0, chars = 0;
    for (const column of graph.columns) {
      tick(); let highest = -1n;
      for (const k of column.keys()) if (BigInt(k) > highest) highest = BigInt(k);
      if (highest >= BigInt(limits.slots)) fail('文字空层数');
      slots += Number(highest + 1n); if (slots > limits.slots) fail('文字格位数');
      const rows = Array(Number(highest + 1n)).fill('');
      for (const [k, parents] of column) {
        tick(); let end = -1;
        for (const p of parents.keys()) end = Math.max(end, p);
        slots += end + 1; if (slots > limits.slots) fail('文字格位数');
        const cells = Array(end + 1).fill('');
        for (const [p, q] of parents) { tick(); cells[p] = String(q); }
        rows[Number(k)] = cells.join(',');
      }
      const text = '[' + rows.join(';') + ']'; chars += text.length;
      if (chars > limits.text) fail('文字长度');
      output.push(text);
    }
    return output.join('');
  }
  function fromDisplay(raw) {
    if (typeof raw !== 'string') throw TypeError('请输入邻接表文字。');
    if (raw.length > limits.text) fail('输入文字');
    const tick = budget(), text = raw.replace(/\s/g, '');
    if (!text || text === '0' || text === '∅') return notation.display.plain('∅');
    if (text === config.top.replace(/\s/g, '')) return notation.display.plain(config.top);
    let cursor = 0, j = 0, slots = 0; const columns = [];
    for (const match of text.matchAll(/\[([^\[\]]*)\]/g)) {
      tick();
      if (match.index !== cursor) throw TypeError('邻接表应为连续的 [列][列]。');
      if (j >= config.width) fail('输入列数');
      cursor += match[0].length;
      if (!/^[\d,;]*$/.test(match[1])) throw TypeError('邻接表内只允许自然数、逗号和分号。');
      const rows = match[1].split(';'), triples = [];
      slots += rows.length;
      for (let k = 0; k < rows.length; k++) {
        tick(); if (!rows[k]) continue;
        const cells = rows[k].split(','); slots += cells.length;
        if (slots > limits.slots) fail('输入格位数');
        if (cells.length > j) throw TypeError('第 ' + j + ' 列只能引用此前的父列。');
        for (let p = 0; p < cells.length; p++) {
          tick(); if (cells[p] === '') continue;
          if (cells[p].length > limits.label) fail('根数值文字');
          const q = BigInt(cells[p]);
          if (q > BigInt(p)) throw TypeError('最大根不能超过父列。');
          if (config.anchored && k >= j) throw TypeError('ARD 行锚必须在子列之前。');
          triples.push('(' + k + ',' + p + ',' + q + ')');
        }
      }
      if (slots > limits.slots) fail('输入空层数');
      columns.push('[' + triples.join(',') + ']'); j++;
    }
    if (!j || cursor !== text.length) throw TypeError('邻接表应为连续的 [列][列]。');
    return notation.display.plain(columns.join(''));
  }
  function textHTML(raw) {
    return '<span style="font-family:inherit;white-space:nowrap">' + escape(plain(raw)) + '</span>';
  }
  function latex(raw) {
    const text = plain(raw);
    return text === '∅' ? '\\varnothing' : '\\text{' + text + '}';
  }
  function message(text, warning = false) {
    return { width: Math.max(160, Array.from(text).length * 14 + 24), height: 48,
      elements: [], extra_text: [{ text, x: 12, y: 24, size: 13, align: 'left',
        color: { type: warning ? 'red' : 'text' } }],
      _adjacency: { complete: !warning, warning, layers: [], entries: [] } };
  }
  function diagram(raw, data = {}) {
    const tick = budget(), graph = inspect(raw, tick);
    if (graph === null) return message(config.top);
    const size = graph.columns.length;
    const layers = data.invert_vertical ? graph.layers.slice().reverse() : graph.layers;
    if (layers.length > limits.layers || layers.length * size * (size + 1) / 2 > limits.cells)
      fail('完整三角表格数');
    let digits = String(Math.max(0, size - 1)).length;
    for (const layer of layers) for (const entry of layer.entries) {
      tick(); digits = Math.max(digits, entry.q.length);
    }
    // Uniform compact cells align all layers, including diagonal index cells.
    // Counts are a separate line, not column headings or coordinate labels.
    const cell = Math.ceil(digits * 7.4 + 3), rowHeight = 14, padding = 4, gap = 8;
    const layerWidth = Math.max(8, ...layers.map(layer => layer.k.length * 7.4));
    const left = padding + layerWidth + 6, firstTableY = 28;
    const tableWidth = size * cell, tableHeight = size * rowHeight;
    const columnWidths = Array(size).fill(cell);
    const columnXs = Array.from({ length: size }, (_, j) => left + (j + 0.5) * cell);
    const minimumWidth = layers.length ? Math.ceil(left + tableWidth + padding) : 16;
    const height = layers.length ? firstTableY + layers.length * (tableHeight + gap) - gap + padding : 24;
    if (minimumWidth > limits.dimension || height > limits.dimension || minimumWidth * height > limits.pixels)
      fail('完整表格画布');
    const elements = [], extra_text = [], entries = [], tables = [];
    function line(x1, y1, x2, y2, kind, k, weight = 0.65) {
      tick(); elements.push({ type: 'line', x1, y1, x2, y2, stroke: true,
        stroke_color: { type: 'gray' }, width: weight, _adjacency: { kind, k } });
    }
    function label(text, x, y, kind, fields = {}, color = 'text', align = 'center') {
      tick(); extra_text.push({ text: String(text), x, y, size: 12, align,
        color: { type: color }, _adjacency: { kind, ...fields } });
    }
    for (let index = 0; index < layers.length; index++) {
      tick(); const layer = layers[index], y = firstTableY + index * (tableHeight + gap);
      label(layer.k, left - 6, y + tableHeight / 2, 'layer', { k: layer.k }, 'text', 'right');
      // Keep p<=j. The shaded p=j cells carry both coordinate labels; only
      // actual relations (p<j) contain q. NER supports lines but not rectangles,
      // so a butt-capped line one row thick fills each whole diagonal cell.
      for (let j = 0; j < size; j++) {
        tick(); const cy = y + (j + 0.5) * rowHeight;
        elements.push({ type: 'line', x1: left + j * cell, y1: cy,
          x2: left + (j + 1) * cell, y2: cy, stroke: true, width: rowHeight,
          stroke_color: { color: { r: 93, g: 155, b: 217, a: 0.24 } },
          _adjacency: { kind: 'diagonal-background', k: layer.k, j } });
        label(j, columnXs[j], cy, 'diagonal-index', { k: layer.k, j });
      }
      for (let p = 0; p <= size; p++) {
        line(left + Math.max(0, p - 1) * cell, y + p * rowHeight, left + tableWidth, y + p * rowHeight,
          'grid-horizontal', layer.k);
      }
      for (let j = 0; j <= size; j++) {
        line(left + j * cell, y, left + j * cell, y + Math.min(size, j + 1) * rowHeight,
          'grid-vertical', layer.k);
      }
      for (const entry of layer.entries) {
        const x = columnXs[entry.j], cy = y + (entry.p + 0.5) * rowHeight;
        label(entry.q, x, cy, 'cell', entry); entries.push({ ...entry, x, y: cy });
      }
      tables.push({ k: layer.k, x: left, y, width: tableWidth, height: tableHeight });
    }
    // Reuse the existing exact counter, including its existing error handling.
    // Do this after geometry so an exhausted counter does not suppress the graph.
    let countText = config.countText(raw), countComplete = /^\d+(?:,\d+)*$/.test(countText);
    const countWidth = text => Array.from(text).reduce((sum, ch) => sum +
      (ch.charCodeAt(0) > 127 ? 14 : 8.5), 2 * padding);
    const maximumCountWidth = Math.min(limits.dimension, Math.floor(limits.pixels / height));
    if (countWidth(countText) > maximumCountWidth) {
      countText = '计数序列文字过长；未截断显示'; countComplete = false;
    }
    const width = Math.ceil(Math.max(minimumWidth, countWidth(countText)));
    if (width > limits.dimension || width * height > limits.pixels) fail('完整表格画布');
    extra_text.unshift({ text: countText, x: padding, y: 11, size: 14, align: 'left',
      color: { type: countComplete ? 'text' : 'red' }, _adjacency: { kind: 'counts' } });
    return { width, height, elements, extra_text, _adjacency: { complete: true,
      columns: size, groups: graph.groups, layers: tables, entries, cell, columnWidths, columnXs, rowHeight,
      countText, countComplete, triangular: true } };
  }
  function safeDiagram(raw, data) {
    try { return diagram(raw, data); }
    catch (error) {
      if (error.name !== 'AdjacencyViewLimit') throw error;
      return message(error.message, true);
    }
  }
  const color = spec => spec.color ? 'rgba(' + [spec.color.r, spec.color.g, spec.color.b,
    spec.color.a ?? 1].join(',') + ')' : spec.type === 'gray' ? 'var(--color-text-muted,#999999)' :
    spec.type === 'red' ? 'var(--color-danger,#bb5147)' : 'currentColor';
  function svg(raw) {
    const value = safeDiagram(raw), tick = budget(), parts = [
      '<svg xmlns="http://www.w3.org/2000/svg" role="img" width="' + value.width +
      '" height="' + value.height + '" viewBox="0 0 ' + value.width + ' ' + value.height +
      '" style="display:block;max-width:none;font-family:inherit" aria-label="' + config.label + ' 分层邻接表">',
      '<title>' + config.label + ' 分层邻接表</title>',
      '<desc>最上方是计数序列，随后每层一张上三角邻接表；完整对角格用淡色背景填入列号，同时充当行列标。左侧裸数字为层号，其余格内数字为最大根 q。无外侧行列号。</desc>'
    ];
    for (const line of value.elements) {
      tick(); parts.push('<line x1="' + line.x1 + '" y1="' + line.y1 + '" x2="' + line.x2 +
        '" y2="' + line.y2 + '" stroke="' + color(line.stroke_color) + '" stroke-width="' + line.width +
        '" stroke-linecap="butt"/>');
    }
    for (const text of value.extra_text) {
      tick(); const meta = text._adjacency;
      const cell = meta?.kind === 'cell' ? ' data-adjacency="' + [meta.k, meta.p, meta.q, meta.j].join(',') + '"' : '';
      parts.push('<text x="' + text.x + '" y="' + text.y + '" font-size="' + text.size +
        '" dominant-baseline="middle" text-anchor="' + ({ left: 'start', center: 'middle', right: 'end' }[text.align]) +
        '" fill="' + color(text.color) + '"' + cell + '>' + escape(text.text) + '</text>');
    }
    parts.push('</svg>'); const result = parts.join('');
    if (result.length > limits.svg) fail('完整 SVG 文字');
    return result;
  }
  const oldControl = notation.draw_diagram;
  notation.id = config.id;
  notation.name = config.displayName || config.label + '（邻接表试用版）';
  if (config.displayName) notation.simple_name = config.displayName;
  notation.description = [...notation.description,
    '本试用版新增邻接表（文字）和邻接表（图），原有显示、展开及比较不变。',
    '文字：每列一对 []；分号从层 0 起分层，逗号从父列 0 起定位，格内填最大根 q。内部空位保留，尾部空位省略；0 不是空位。',
    '图：最上方是计数序列，其下每层一张上三角表；只裁去必空的下三角，不删任何关系。完整对角格用淡色背景填列号，同时标识该行和该列。层号在左侧，不加 k=，不画外侧行列号。',
    '两种新视图均可由纯文本导回列表。计数复用原精确算法；超限明确提示，不代填近似数字。表格完整显示全部关系。'
  ];
  notation.display_equiv = { ...notation.display_equiv,
    [TEXT]: { name: TEXT, plain, html: textHTML, latex, from_display: fromDisplay },
    [TABLE]: { name: TABLE, plain, html: svg, latex, from_display: fromDisplay }
  };
  notation.draw_diagram = { ...oldControl,
    default_data: { ...oldControl.default_data, current_equiv: undefined },
    draw_diagram: (raw, data = {}) => data.current_equiv === TABLE || data.current_equiv === TEXT ?
      safeDiagram(raw, data) : oldControl.draw_diagram(raw, data)
  };
  notation.debug = { ...notation.debug, adjacency_text: plain, adjacency_from_text: fromDisplay,
    adjacency_diagram: diagram, adjacency_svg: svg, adjacency_limits: limits };
}
addAdjacencyDisplays(definition, {label:'RPD',displayName:'RDP',top:'Limit',id:'rpd-column-adjacency-v1',width:256,ms:400,anchored:false,countText:raw=>definition.display_equiv['数字序列'].plain(raw),read:raw=>definition.debug.adjacency(raw)});
register(definition);
})(register_notation);

})(definition => { originalRPD = definition; });
register(installBoundDisplays("rpd", originalRPD, R, bridge,
  createBrowserYEngine, makeMountainDisplay));
})(register_notation);
