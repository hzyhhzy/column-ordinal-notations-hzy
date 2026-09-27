'use strict';

// Research implementation of the padded omega-star cover. This is a
// simulation, not an alternative definition of either notation.
const assert = require('node:assert/strict');
const fs = require('node:fs'), path = require('node:path');
const R = require('../rpd-y-converter-20260914/rpd-engine.cjs');
const G = require('../rpd-y-converter-20260914/y-mountain.cjs');
const {model} = require('../y139-e0mn-target-20260917/mn-omega-trace.cjs');
let M;
new Function('register_notation', fs.readFileSync(path.join(__dirname,
  '../e0mn-counting-20260917/e0MN计数序列优化加速版.ne-rewritten.js'), 'utf8'))(v => M = v);
const nat = n => n ? [{exp: [], coeff: n}] : [];
const omega = [{exp: nat(1), coeff: 1}];
const budget = () => new R.Budget({maxWidth: 200, maxAtoms: 500000,
  maxWork: 30000000, ms: 2000});

function ocmp(a, b) {
  for (let i = 0; i < Math.min(a.length, b.length); i++) {
    const c = ocmp(a[i].exp, b[i].exp);
    if (c) return c;
    if (a[i].coeff !== b[i].coeff) return Math.sign(a[i].coeff - b[i].coeff);
  }
  return Math.sign(a.length - b.length);
}
function positions(flags) {
  let a = 0;
  return flags.map(root => { const old = a; a += root ? 2 : 1; return old; });
}
function ancestry(h, threshold) {
  const sets = [];
  for (const col of h) {
    const own = new Set();
    for (const {a, x} of col) if (ocmp(x, threshold) >= 0) {
      own.add(a - 1);
      for (const p of sets[a - 1]) own.add(p);
    }
    sets.push(own);
  }
  return sets;
}
function check(state, forests = false) {
  const {source, flags, target} = state, a = positions(flags);
  assert.equal(flags.length, source.size);
  assert.equal(target.length, source.size ? a.at(-1) + 1 : 0);
  assert(M.debug.isLegalExpr(target), 'target legality');
  for (let j = 0; j < target.length; j++) for (const e of target[j]) {
    assert(ocmp(e.x, omega) <= 0, 'rows at most omega');
    assert(ocmp(e.x, omega) === 0 || e.x[0].coeff <= j, 'local coefficient bound');
  }
  const edges = G.realEdges(source, budget()), cache = new Map(), high = new Map();
  for (const [k, q, p, j] of edges) {
    assert(k === 0 || k === 1, 'two extraction layers');
    assert(flags[q], 'every genuine root has a spare column');
    if (k) { assert.equal(p, q); assert(!high.has(j)); high.set(j, p); }
    const key = k ? 'omega' : q, threshold = k ? omega : nat(a[q] + 2);
    assert(k || a[q] + 2 <= a[j], 'finite threshold regularity');
    if (!cache.has(key)) cache.set(key, ancestry(target, threshold));
    assert(cache.get(key)[a[j]].has(a[p]), `lost cover: ${[k,q,p,j]}`);
  }
  for (const p of high.values()) assert(!high.has(p), 'high-star roots have no high parent');
  if (forests) {
    const labels = new Map(target.flat().map(e => [JSON.stringify(e.x), e.x]));
    for (const threshold of labels.values()) {
      const paths = ancestry(target, threshold);
      for (const own of paths) for (const p of own) for (const q of own)
        assert(p === q || paths[p].has(q) || paths[q].has(p), 'threshold forest');
    }
  }
  return true;
}
function normalizeAt(h, tau, emit = () => {}) {
  const col = h.at(-1), i = col.findIndex(e => ocmp(e.x, tau) >= 0);
  assert(i >= 0, 'requested threshold exists');
  const out = [...h.slice(0, -1), [...col.slice(0, i), {a: col[i].a, x: tau}]];
  if (JSON.stringify(out) !== JSON.stringify(h)) emit({kind: 'macro', before: h, after: out});
  return out;
}
function expose(h, parent, tau, emit = () => {}) {
  assert(ancestry(h, tau).at(-1).has(parent), 'requested ancestor exists');
  let out = h;
  for (let rounds = 0; rounds < h.length; rounds++) {
    out = normalizeAt(out, tau, emit);
    const control = out.at(-1).at(-1);
    assert(control.a >= parent + 1);
    if (control.a === parent + 1) return out;
    const next = M.debug.down(out);
    emit({kind: 'down', before: out, after: next});
    out = next;
  }
  throw new Error('exposure did not strictly reduce the parent');
}
function initialize(source, flags, target) {
  flags ??= Array(source.size).fill(false);
  for (const [, q] of G.realEdges(source, budget())) flags[q] = true;
  const a = positions(flags);
  target ??= Array.from({length: source.size ? a.at(-1) + 1 : 0},
    (_, j) => j ? [{a: j, x: omega}] : []);
  const state = {source, flags, target}; check(state, true); return state;
}
function step(state, n, emit = () => {}) {
  check(state);
  const {source, flags, target} = state, a = positions(flags);
  if (!source.size) return state;
  const control = G.control(source, budget()), x = source.size - 1;
  const nextSource = G.fs(source, n, budget());
  let out, nextFlags;
  if (!n || !control) {
    nextFlags = flags.slice(0, -1);
    out = target;
  } else {
    const [K, r, c] = control, span = x - c;
    // A high star has no high seam to preserve. A finite gate just above
    // all its ordinary seam thresholds is enough, when locally regular.
    const finiteGate = K ? 1 + Math.max(0, ...G.realEdges(source, budget())
      .filter(([k, , , j]) => k === 0 && j === x).map(([, q]) => a[q] + 2)) : 0;
    const tau = K ? (finiteGate <= a[x] ? nat(finiteGate) : omega) : nat(a[r] + 2);
    const ready = expose(target, a[c], tau, emit);
    out = M.FS(ready, n);
    emit({kind: 'FS', before: ready, after: out, n});
    nextFlags = flags.slice(0, x);
    for (let b = 1; b <= n; b++) nextFlags.push(...flags.slice(c, x));
    assert.equal(nextFlags.length, x + n * span);
  }
  const end = nextSource.size ? positions(nextFlags).at(-1) + 1 : 0;
  while (out.length > end) {
    const child = M.FS(out, 0);
    emit({kind: 'FS', before: out, after: child, n: 0}); out = child;
  }
  const next = {source: nextSource, flags: nextFlags, target: out};
  assert(M.compare(out, target) < 0, 'strict target descent');
  check(next); return next;
}

// Independent compressed local trace certifies each preparation endpoint.
// The endpoint was not selected by this counting/unranking routine.
function certify(e, tick = () => {}) {
  if (e.kind === 'FS') { assert.deepEqual(M.FS(e.before, e.n), e.after); return 0n; }
  assert.deepEqual(e.before.slice(0, -1), e.after.slice(0, -1));
  const old = model(e.before, tick), next = model(e.after, tick), d = old.count - next.count;
  assert(d > 0n, 'positive number of true local steps');
  assert.deepEqual(old.columnAtStep(d), e.after.at(-1), 'exact local-step endpoint');
  if (e.kind === 'down') assert.equal(d, 1n);
  return d;
}
module.exports = {M, G, R, nat, omega, ocmp, positions, ancestry, check,
  initialize, step, expose, normalizeAt, certify, budget};
