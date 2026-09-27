'use strict';

// Full original Y parent graph, with an ordered stack of
// live high-star owners instead of a single owner. No source rule is changed.
const assert = require('node:assert/strict');
const D = require('../e0mn13-y-location-20260920/direct-source.cjs');
const S = require('../e0mn13-y-location-20260920/banded-source.cjs');
const {rowAncestor} = S;
const top = [1n, 3n, 4n, 2n, 5n, 8n];

function inspect(source, base, levels = Infinity) {
  const ps = D.parents(source);
  const roots = new Set(ps.filter(p => p.high !== null).map(p => p.high));
  const sets = ps.map(() => new Set());
  assert.equal(base.length, source.size);
  for (const [, q] of source.atoms) assert(base[q], 'every genuine root marked');
  for (let t = 0; t < ps.length; t++) {
    const p = ps[t];
    for (let r = 1; r < p.parents.length; r++)
      assert.equal(ps[p.parents[r]].high, null, 'no upper ordinary tip father');
    if (p.high === null) continue;
    const c = p.high, h = ps[c].parents.length;
    assert(!base[t] && base[c] && ps[c].high === null);
    assert.deepEqual(p.parents, Array(h + 1).fill(c), 'uniform high tip');
    for (let v = c + 1; v < t; v++) {
      if (!h) assert.equal(ps[v].high, c, 'pure zero-height star band');
      let a = v;
      while (a > c && ps[a].high !== c && ps[a].parents.length) a = ps[a].parents[0];
      assert(a > c && ps[a].high === c, 'high-star band condition');
    }
    const zero = [];
    for (let j = t + 1; j < ps.length; j++) if (rowAncestor(ps, t, j, 0)) {
      if (!h) zero.push(j);
      if (rowAncestor(ps, c, j, h)) sets[j].add(c);
    }
    if (!h && zero.length) {
      assert.deepEqual(zero, [t + 1]);
      assert(!base[t + 1]);
      assert.deepEqual(ps[t + 1], {parents: [t], high: null});
    }
  }
  const owners = sets.map(s => [...s].sort((a, b) => a - b));
  const depth = Math.max(0, ...owners.map(a => a.length));
  assert(depth <= levels, 'bounded owner-stack depth');
  for (let j = 0; j < ps.length; j++) {
    const chain = owners[j];
    for (let k = 0; k < chain.length; k++) {
      assert.deepEqual(owners[chain[k]], chain.slice(0, k), 'owners form a full ancestor stack');
      assert(ps[chain[k]].parents.length < ps[j].parents.length);
      if (k) assert(ps[chain[k - 1]].parents.length < ps[chain[k]].parents.length);
    }
    if (ps[j].high !== null)
      assert.deepEqual(chain, owners[ps[j].high], 'a tip inherits its roots external stack');
  }
  return {ps, roots, owners, depth, height: Math.max(0, ...ps.map(p => p.parents.length))};
}

function expected(source, base, levels, n) {
  const {ps, owners} = inspect(source, base, levels), x = source.size - 1;
  const control = D.G.control(source);
  const out = ps.slice(0, x).map(p => ({parents: p.parents.slice(), high: p.high}));
  if (!n || !control) return out;
  const high = !!control[0], c = control[2], span = x - c;
  const h = ps[c].parents.length, row = ps[x].parents.length - 1;
  if (high) for (let j = c + 1; j < x; j++)
    assert.equal(rowAncestor(ps, c, j, h), ps[j].high === c || owners[j].includes(c),
      'ascending set = own tips and all nested bodies');
  for (let b = 1; b <= n; b++) for (let j = c; j < x; j++) {
    const move = p => p < c ? p : p + b * span;
    const previous = p => p < c ? p : p + (b - 1) * span;
    let p = {parents: ps[j].parents.map(move), high: ps[j].high === null ? null : move(ps[j].high)};
    if (high) {
      if (j === c) p = {parents: Array(h + b).fill(c + (b - 1) * span), high: null};
      else if (rowAncestor(ps, c, j, h)) p.parents = ps[j].parents.slice(0, h).map(move)
        .concat(Array(b + 1).fill(move(ps[j].parents[h])), ps[j].parents.slice(h + 1).map(move));
    } else if (j === c) for (let u = 0; u < row; u++) p.parents[u] = previous(ps[x].parents[u]);
    out.push(p);
  }
  return out;
}

function sourceStep(s, n) {
  const old = inspect(s.source, s.base, s.levels);
  const c = D.G.control(s.source), x = s.source.size - 1;
  const source = D.G.fs(s.source, n), base = S.nextMarks(s.source, s.base, n);
  assert.deepEqual(D.parents(source), expected(s.source, s.base, s.levels, n), 'original Y full parents');
  const next = inspect(source, base, s.levels);
  const owners = old.owners.slice(0, x).map(a => a.slice());
  if (n && c) for (let b = 1; b <= n; b++) for (let j = c[2]; j < x; j++)
    owners.push(old.owners[j].map(a => a < c[2] ? a : a + b * (x - c[2])));
  assert.deepEqual(next.owners, owners, 'exact whole-stack transport');
  return {source, base};
}

module.exports = {D, S, top, inspect, expected, sourceStep};
