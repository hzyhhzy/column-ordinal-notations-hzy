'use strict';

// Source-only acceleration: retain true row roots rather than their entire
// downward closure. Every expansion still runs Naruyoko's original Y rules.
const assert = require('node:assert/strict');
const {createYEngine} = require('../rpd-y-converter-20260914/y-engine.cjs');
const Y = createYEngine({maxWidth: 96, maxLayers: 100, maxAtoms: 120000, timeoutMs: 500});

function encode(values) {
  const g = Y.genuine(values);
  return {...g, values: values.slice()};
}
const G = {
  realEdges(g) { return g.atoms; },
  control(g) {
    let ctrl = null;
    for (const edge of g.atoms) if (edge[3] === g.size - 1) ctrl = edge;
    return ctrl;
  },
  fs(g, n) { return encode(Y.fs(g.values, n)); },
};

function parents(g) {
  const heights = Array(g.size).fill(0);
  for (const [k,,,j] of g.atoms) if (!k) heights[j]++;
  const p = heights.map(h => ({parents: Array(h).fill(null), high: null}));
  for (const [k,q,f,j] of g.atoms) {
    if (!k) {
      const row = heights[q];
      assert(row < heights[j] && p[j].parents[row] === null);
      p[j].parents[row] = f;
    } else {
      assert(k === 1 && q === f && p[j].high === null, 'flat high stars');
      p[j].high = f;
    }
  }
  assert(p.every(v => v.parents.every(x => x !== null)));
  return p;
}

module.exports = {Y, G, encode, parents};
