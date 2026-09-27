'use strict';

// Experimental only: use the largest available threshold at ordinary controls.
// Unlike the rejected literal-row protocol, this does not deliberately discard
// stronger seams merely because the source control has a low ordinary height.
const assert = require('node:assert/strict');
const C = require('../e0mn-y134258a-20260920/omega-star-simulation.cjs');
const D = require('../e0mn13-y-location-20260920/direct-source.cjs');
const {M, nat, ancestry, expose} = C;

function capacity(target, p, j) {
  // Zero-based endpoints; all tested rows are finite positive integers.
  const caps = Array(j + 1).fill(0); caps[p] = Infinity;
  for (let v = p + 1; v <= j; v++) for (const e of target[v]) {
    assert(e.x.length === 1 && !e.x[0].exp.length);
    caps[v] = Math.max(caps[v], Math.min(e.x[0].coeff, caps[e.a - 1] || 0));
  }
  return caps[j];
}
function check(s) {
  assert.equal(s.points.length, s.source.size);
  if (!s.source.size) { assert.equal(s.target.length, 0); return; }
  assert.equal(s.reserve, s.anchor + 1);
  assert.equal(s.target.length, s.points.at(-1) + 1);
  assert(M.debug.isLegalExpr(s.target));
  for (const col of s.target) for (const e of col)
    assert(e.x.length === 1 && !e.x[0].exp.length && e.x[0].coeff <= e.a, 'finite strict cone');
  const ps = D.parents(s.source);
  for (let j = 0; j < s.source.size; j++) {
    const a = s.points[j];
    assert(a > s.reserve);
    assert(capacity(s.target, s.anchor - 1, a - 1) >= 1);
    assert(capacity(s.target, s.anchor - 1, a) >= 1);
    ps[j].parents.forEach((p, r) =>
      assert(capacity(s.target, s.points[p] - 1, a - 1) >= r + 1, `ordinary ${j},${r}`));
    if (ps[j].high !== null)
      assert(capacity(s.target, s.points[ps[j].high] - 1, a - 1) >= s.reserve + 1, `high ${j}`);
  }
}
function initialize(values, seedHeight = 4) {
  const source = D.encode(values);
  const seed = M.FS(M.debug.parseExpr('()(1:ω)'), seedHeight);
  const target = M.FS(seed, 2 * source.size - 1);
  const s = {source, target, points: values.map((_, j) => seedHeight + 2 * j), anchor: 1, reserve: 2};
  check(s); return s;
}
function step(s, n, emit = () => {}, verify = true) {
  const x = s.source.size - 1;
  if (x < 0) return s;
  const ctrl = D.G.control(s.source), source = D.G.fs(s.source, n);
  let {target, anchor, reserve} = s, points = s.points.slice(), next = points.slice(0, -1);
  const fs = k => {
    const old = target; target = M.FS(target, k); emit({kind: 'FS', before: old, after: target, n: k});
  };
  if (n && ctrl) {
    if (ctrl[0]) {
      const required = Math.max(0, ...D.parents(source).map(p => p.parents.length)) + 1;
      const L = target.length - anchor;
      const pump = Math.max(0, Math.ceil((required - reserve) / L)), delta = pump * L;
      if (pump) target = expose(target, anchor - 1, nat(1), emit);
      fs(pump);
      if (pump) { anchor += delta; reserve += delta; points = points.map(p => p + delta); }
      next = points.slice(0, -1);
    } else fs(0);
    const cut = ctrl[2], parent = points[cut] - 1;
    const threshold = capacity(target, parent, target.length - 1);
    assert(threshold >= 1);
    target = expose(target, parent, nat(threshold), emit);
    const L = target.length - points[cut]; fs(n);
    for (let b = 1; b <= n; b++) for (let j = cut; j < x; j++) next.push(points[j] + b * L);
  }
  const width = next.length ? next.at(-1) + 1 : 0;
  assert(target.length >= width);
  while (target.length > width) fs(0);
  const t = {source, target, points: next, anchor, reserve};
  if (verify) check(t);
  assert(M.compare(target, s.target) < 0); return t;
}
module.exports = {...C, D, capacity, initialize, step, check};
