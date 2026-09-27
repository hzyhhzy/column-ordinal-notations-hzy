'use strict';

// Exact finite-threshold projection candidate. All physical addresses and row
// capacities are BigInt, so repeated global pumps need not be materialized.
// The source still executes the original numerical Y.
const assert = require('node:assert/strict');
const F = require('./greedy-cover.cjs'), {D} = F;
const min = (a, b) => a < b ? a : b;
const max = (a, b) => a > b ? a : b;

function initialize(values, height = 4) {
  const a = F.initialize(values, height);
  const pos = [BigInt(a.anchor), ...a.points.flatMap(p => [BigInt(p), BigInt(p + 1)])];
  const caps = pos.map((p, j) => pos.slice(0, j).map(q => BigInt(F.capacity(a.target, Number(q) - 1, Number(p) - 1))));
  const rootSet = new Set(a.source.atoms.map(e => e[1]));
  const s = {source: a.source, pos, caps, anchor: BigInt(a.anchor), reserve: BigInt(a.reserve),
    base: values.map((_, j) => rootSet.has(j)), gap: height - 1};
  check(s); return s;
}
function check(s) {
  const w = s.source.size;
  if (!w) { assert.equal(s.pos.length, 0); return; }
  assert.equal(s.pos.length, 1 + 2 * w);
  assert.equal(s.anchor, s.pos[0]); assert.equal(s.reserve, s.anchor + 1n);
  const ps = D.parents(s.source);
  for (let j = 0; j < w; j++) {
    const a = 1 + 2 * j;
    assert.equal(s.pos[a], s.anchor + BigInt(s.gap + 2 * j));
    assert(s.caps[a][0] >= 1n && s.caps[a + 1][0] >= 1n);
    for (let r = 0; r < ps[j].parents.length; r++)
      assert(s.caps[a][1 + 2 * ps[j].parents[r]] >= BigInt(r + 1), `ordinary ${j},${r}`);
    if (ps[j].high !== null)
      assert(s.caps[a][1 + 2 * ps[j].high] >= s.reserve + 1n, `high ${j}`);
  }
}
function copy(s, cut, n, threshold) {
  const old = s.caps, oldPos = s.pos, x = old.length - 1;
  const L = oldPos[x] - oldPos[cut], count = x - cut;
  const caps = old.slice(0, x).map(a => a.slice()), pos = oldPos.slice(0, x);
  const rootCaps = old[cut];
  for (let b = 1; b <= n; b++) {
    const shift = BigInt(b) * L, start = caps.length;
    const row = Array(start).fill(0n);
    for (let v = 0; v < cut; v++) row[v] = rootCaps[v];
    for (let p = 0; p < x; p++) {
      const weight = min(old[x][p], threshold - 1n);
      if (!weight) continue;
      const actual = p < cut ? p : p + (b - 1) * count;
      row[actual] = max(row[actual], weight);
      for (let v = 0; v < actual; v++) row[v] = max(row[v], min(caps[actual][v], weight));
    }
    caps.push(row); pos.push(oldPos[cut] + shift);
    const moveRow = r => r > oldPos[cut] ? r + shift : r;
    for (let j = cut + 1; j < x; j++) {
      const col = Array(caps.length).fill(0n), via = moveRow(old[j][cut]);
      for (let v = 0; v < start; v++) {
        col[v] = min(row[v], via);
        if (v < cut) col[v] = max(col[v], old[j][v]);
      }
      col[start] = via;
      for (let i = cut + 1; i < j; i++) col[start + i - cut] = moveRow(old[j][i]);
      caps.push(col); pos.push(oldPos[j] + shift);
    }
  }
  return {...s, caps, pos};
}
function step(s, n, verify = true) {
  const w = s.source.size;
  if (!w) return s;
  const ctrl = D.G.control(s.source), source = D.G.fs(s.source, n);
  if (!n || !ctrl) {
    const width = w > 1 ? s.pos.length - 2 : 0;
    const t = {...s, source, base: s.base.slice(0, -1), caps: s.caps.slice(0, width), pos: s.pos.slice(0, width)};
    if (verify) check(t); return t;
  }
  let t = {...s, caps: s.caps.slice(0, -1).map(a => a.slice()), pos: s.pos.slice(0, -1)};
  if (ctrl[0]) {
    const required = BigInt(Math.max(0, ...D.parents(source).map(p => p.parents.length)) + 1);
    const L = s.pos.at(-1) - s.anchor;
    const pump = required > s.reserve ? (required - s.reserve + L - 1n) / L : 0n;
    const delta = pump * L;
    t.pos = t.pos.map(p => p + delta);
    t.caps = t.caps.map(a => a.map(r => r > s.anchor ? r + delta : r));
    t.anchor += delta; t.reserve += delta;
  }
  const cut = 1 + 2 * ctrl[2], threshold = t.caps.at(-1)[cut];
  assert(threshold > 0n);
  t = copy(t, cut, n, threshold); t.source = source;
  t.base = s.base.slice(0, -1);
  for (let b = 1; b <= n; b++) t.base.push(...s.base.slice(ctrl[2], -1));
  if (verify) check(t); return t;
}
function growthObstruction(s) {
  const ctrl = D.G.control(s.source);
  if (!ctrl || ctrl[0] === 0) return null;
  const ps = D.parents(s.source), c = ctrl[2], x = s.source.size - 1, L = x - c;
  if (x + L > 90) return null;
  const next = D.G.fs(s.source, 1), qs = D.parents(next);
  for (const [k, q, p, j] of s.source.atoms) if (!k && q >= c && j < x) {
    if (qs[q + L].parents.length > ps[q].parents.length) {
      const capacity = s.caps[1 + 2 * j][1 + 2 * p];
      if (capacity <= s.anchor) return {edge: [q, p, j], cut: c, capacity: String(capacity),
        anchor: String(s.anchor), oldRootHeight: ps[q].parents.length,
        newRootHeight: qs[q + L].parents.length};
    }
  }
  return null;
}
module.exports = {F, D, initialize, step, check, growthObstruction, copy};
