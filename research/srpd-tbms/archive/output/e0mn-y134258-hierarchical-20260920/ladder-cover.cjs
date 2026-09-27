'use strict';

// Real-M simulation accompanying Y134258-BOUND.zh-CN.md (paper, not Lean).
// Each owner depth has its own growth anchor. Tests do not replace the proof.
const assert = require('node:assert/strict');
const N = require('./nested-source.cjs');
const F = require('../e0mn13-y-location-20260920/graded-bands-real.cjs');
const C = require('../e0mn-y134258a-20260920/omega-star-simulation.cjs');
const {M, nat, capacity} = F;
const {D, S} = N;

function expose(target, parent, threshold, emit) {
  // The existing expose routine materializes every threshold-ancestor set.
  // On this finite-row cone, a single capacity check suffices. The subsequent
  // normalization/down events are exactly the same real local operations.
  assert.equal(threshold.length, 1);
  assert.equal(threshold[0].exp.length, 0);
  assert(capacity(target, parent, target.length - 1) >= threshold[0].coeff);
  let out = target;
  for (let i = 0; i < target.length; i++) {
    out = C.normalizeAt(out, threshold, emit);
    const control = out.at(-1).at(-1);
    assert(control.a >= parent + 1);
    if (control.a === parent + 1) return out;
    const next = M.debug.down(out);
    emit({kind: 'down', before: out, after: next}); out = next;
  }
  throw new Error('finite control exposure did not decrease parent address');
}

function grade(s, r, j, row) {
  let level = -1;
  for (let k = 0; k < r.owners[j].length; k++) {
    if (r.ps[r.owners[j][k]].parents.length <= row) level = k;
    else break;
  }
  return level < 0 ? row + 1
    : s.anchors[level] + 1 + row - r.ps[r.owners[j][level]].parents.length;
}

function check(s) {
  const r = N.inspect(s.source, s.base, s.levels);
  assert(M.debug.isLegalExpr(s.target));
  for (const col of s.target) for (const e of col)
    assert(e.x.length === 1 && !e.x[0].exp.length && e.x[0].coeff <= e.a, 'finite strict M cone');
  assert.equal(s.points.length, s.source.size);
  assert.equal(s.target.length, s.source.size ? s.points.at(-1) + s.levels + 1 : 1);
  if (!s.source.size) return r;
  assert.equal(s.anchors.length, s.levels + 1);
  assert(s.anchors[0] >= r.height, 'height anchor');
  assert(s.Q > s.anchors.at(-1));
  const cap = (p, j) => capacity(s.target, p - 1, j - 1);
  for (let k = 1; k <= s.levels; k++) {
    assert(s.anchors[k] >= s.anchors[k - 1] + r.height + 2, 'inter-level spacing');
    assert(cap(s.anchors[k - 1], s.anchors[k]) >= 1, 'anchor chain');
  }
  for (let j = 0; j < s.points.length; j++) {
    const point = s.points[j], p = r.ps[j];
    assert(point > s.Q);
    if (j) assert(point > s.points[j - 1] + s.levels + 1);
    for (let k = 0; k <= s.levels + 1; k++)
      assert(cap(s.anchors.at(-1), point + k) >= 1, 'pump background');
    for (let row = 0; row < p.parents.length; row++) {
      const available = cap(s.points[p.parents[row]], point), need = grade(s, r, j, row);
      assert(available >= row + 1, 'literal cover');
      assert(available >= need, `graded cover j=${j} row=${row}: ${available}<${need}`);
      assert(need < s.Q - 1, 'all grades below high seam');
    }
    if (!s.base[j] && p.parents.length)
      assert(cap(s.points[p.parents.at(-1)], point) >= s.Q, 'unmarked highest reserve');
    if (p.high !== null) assert(cap(s.points[p.high], point) >= s.Q, 'high reserve');
  }
  return r;
}

function fs(s, n, emit) {
  const before = s.target;
  s.target = M.FS(before, n);
  emit({kind: 'FS', before, after: s.target, n});
}

function pump(s, level, required, emit, minimum = 0) {
  const cut = s.anchors[level], span = s.target.length - cut;
  const count = Math.max(minimum, 0, Math.ceil((required - cut) / span));
  const delta = count * span;
  if (count) s.target = expose(s.target, cut - 1, nat(1), emit);
  fs(s, count, emit); // Even count zero consumes one real auxiliary.
  if (count) {
    for (let k = level; k < s.anchors.length; k++) s.anchors[k] += delta;
    s.Q += delta;
    s.points = s.points.map(p => p + delta);
  }
  return count;
}

function prepare(s, height, emit, minimumPumps = {}) {
  const counts = [];
  for (let k = s.levels; k >= 0; k--) {
    const required = k ? s.anchors[k - 1] + height + 2 : height;
    counts[k] = pump(s, k, required, emit, minimumPumps[k] ?? 0);
  }
  return counts;
}

function initializeSource(values, emit = () => {}, options = {}) {
  const source = D.encode(values), base = S.mark(source);
  assert(source.size > 0, 'initialize a nonempty source; empty states are reached by step');
  const r = N.inspect(source, base), levels = options.levels ?? Math.max(1, r.depth);
  assert(levels >= r.depth && levels >= 1);
  const unit = levels + 2;
  if (options.direct) {
    const readyHeight = Math.max(r.height, options.readyHeight ?? 0);
    const anchors = Array.from({length: levels + 1}, (_, k) => Math.max(1, readyHeight) + k * (readyHeight + 2));
    const Q = anchors.at(-1) + 1, seedHeight = Q + 1;
    const seed = M.FS(M.debug.parseExpr('()(1:ω)'), seedHeight);
    const s = {source, base, levels, seed, target: seed, anchors, Q,
      points: Array.from({length: source.size}, (_, j) => seedHeight + unit * j)};
    fs(s, unit * source.size - 1, emit);
    s.lastPumps = []; check(s); return s;
  }
  {
    // Use ONE row-2 copy to create a long row-1 chain of distinct anchors.
    // Subsequent maintenance uses row 1 only; no repeatable row-2 background
    // is assumed. This starts below the SAME D4 for every finite depth.
    const seed = M.FS(M.debug.parseExpr('()(1:ω)'), 4);
    const padding = Math.max(0, r.height + 2 - (unit * source.size + 3));
    const first = 4 + padding;
    const s = {source, base, levels, seed, target: seed, anchors: [], Q: 3,
      points: Array.from({length: source.size}, (_, j) => first + unit * j)};
    fs(s, padding + unit * source.size + 1, emit);
    const span = s.target.length - 2;
    assert(span >= r.height + 2);
    s.target = expose(s.target, 1, nat(2), emit);
    fs(s, levels, emit);
    s.anchors = Array.from({length: levels + 1}, (_, k) => 2 + k * span);
    s.Q += levels * span;
    s.points = s.points.map(p => p + levels * span);
    assert.equal(s.target.length, s.points.at(-1) + levels + 2);
    // One extra closer remains for the common height pump.
    s.lastPumps = [pump(s, 0, r.height, emit)];
    check(s); return s;
  }
}

function initialize(n, emit = () => {}, options = {}) {
  return initializeSource(D.Y.fs(N.top, n), emit, options);
}

function step(s, n, emit = () => {}, options = {}) {
  const old = check(s);
  if (!s.source.size) return s;
  const c = D.G.control(s.source), x = s.source.size - 1;
  const child = N.sourceStep(s, n);
  const nextData = N.inspect(child.source, child.base, s.levels);
  const t = {...s, ...child, anchors: s.anchors.slice(), points: s.points.slice()};
  let next = t.points.slice(0, -1), pumps = [];
  if (n && c) {
    if (c[0]) pumps = prepare(t, nextData.height, emit, options.minimumPumps);
    else for (let k = 0; k <= s.levels; k++) fs(t, 0, emit);
    next = t.points.slice(0, -1);
    const row = old.ps[x].parents.length - 1;
    const threshold = c[0] || !s.base[x] ? t.Q : grade(t, old, x, row);
    const cut = c[2], point = t.points[cut];
    t.target = expose(t.target, point - 1, nat(threshold), emit);
    const span = t.target.length - point;
    fs(t, n, emit);
    for (let b = 1; b <= n; b++) for (let j = cut; j < x; j++)
      next.push(t.points[j] + b * span);
  }
  t.points = next;
  const width = next.length ? next.at(-1) + s.levels + 1 : 1;
  assert(t.target.length >= width);
  while (t.target.length > width) fs(t, 0, emit);
  t.lastPumps = pumps;
  check(t);
  assert(M.compare(t.target, s.target) < 0, 'actual target strictly decreases');
  return t;
}

module.exports = {...N, ...F, inspect: N.inspect, sourceStep: N.sourceStep,
  grade, check, expose, initializeSource, initialize, step};
