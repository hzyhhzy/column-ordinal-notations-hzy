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
