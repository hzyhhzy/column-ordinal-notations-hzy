'use strict';
// View extraction only. Ordinal equalities are paper results in the research
// document, not conclusions inferred from these finite API checks.
const assert = require('node:assert/strict');
const notation = require('../../../notations/DQDN/DQDN.ne-rewritten.js');
const d = notation.debug;
const started = performance.now();
const samples = [
  ['0', [0]], ['1', [1, 0]],
  ['\\omega', [1, 1]], ['\\omega\\cdot2', [1, 2]], ['\\omega\\cdot3', [1, 3]],
  ['\\omega^2', [1, 4]], ['\\omega^3', [1, 6]], ['\\omega^4', [1, 8, 38]],
  ['\\omega^5', [1, 8]], ['\\omega^6', [1, 10]], ['\\omega^7', [1, 12]],
  ['\\omega^8', [1, 14, 38]], ['\\omega^9', [1, 14]], ['\\omega^{10}', [1, 16]],
  ['\\omega^\\omega', d.OMEGA_OMEGA_PATH],
  ['\\omega^{\\omega+1}', d.OMEGA_OMEGA_PATH.slice(0, -1)],
  ['\\omega^{\\omega\\cdot2}', [1,64,8,1,1,1,8,1,1,1,26,1,1,1,30,1,1,30,1,1,
    40,8,1,42,1,4,1,1,42,1,6,1,1,1,1,1]],
  ['\\varepsilon_0', [1]]
];
const early = [
  [0,'1'], [1,'\\omega'], [2,'\\omega\\cdot2'], [3,'\\omega\\cdot3'],
  [4,'\\omega^2'], [5,'\\omega^2+\\omega'], [6,'\\omega^3'],
  [8,'\\omega^5'], [10,'\\omega^6'], [20,'\\omega^{13}'],
  [30,'\\omega^{19}'], [40,'\\omega^{26}'], [50,'\\omega^{33}'],
  [52,'\\omega^{34}'], [53,'\\omega^{34}+\\omega^{17}'],
  [54,'\\omega^{\\omega+27}'], [55,'\\omega^{\\omega+27}+\\omega^3'],
  [56,'\\omega^{\\omega+28}'], [58,'\\omega^{\\omega+29}'],
  [60,'\\omega^{\\omega+31}'], [62,'\\omega^{\\omega+32}'],
  [64,'\\omega^{\\omega\\cdot3+32}'], [65,'\\omega^{\\omega\\cdot3+32}+\\omega^{21}']
];
function extract(ordinal, path) {
  if (performance.now() - started > 15000) throw new Error('15-second extraction budget');
  const value = d.parse('TOP' + path.map(n => `[${n}]`).join(''));
  const columns = d.standard(value).length;
  const minimal = notation.display_equiv['最简操作序列'].plain(value);
  const growth = notation.display_equiv['增列序列'].plain(value);
  assert.equal(d.parse(minimal), value);
  assert.equal(d.parseGrowth(growth), value);
  return {ordinal, columns,
    counts: columns > 100 ? `【${columns}列】` : notation.display.plain(value),
    minimal, growth};
}
console.log(JSON.stringify({
  main: samples.map(([ordinal,path]) => extract(ordinal,path)),
  early: early.map(([n,tail]) => extract('\\varepsilon_0+' + tail, [2,n])),
  note: 'View round trips only; paper ordinal proofs remain separate.'
}, null, 2));
