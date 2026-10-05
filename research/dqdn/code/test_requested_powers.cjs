'use strict';
// Checks the actual NER API, not ordinal ranks or a live browser import.
const assert = require('node:assert/strict');
const notation = require('../../../notations/DQDN/DQDN.ne-rewritten.js');
const d = notation.debug;
const samples = [
  [[1,1],18], [[1,4],26], [[1,6],32], [[1,8,38],185],
  [[1,8],38], [[1,10],44], [[1,12],50], [[1,14,38],200],
  [[1,14],56], [[1,16],62],
  [d.OMEGA_OMEGA_PATH.slice(0,-1),879],
  [[1,64,8,1,1,1,8,1,1,1,26,1,1,1,30,1,1,30,1,1,
    40,8,1,42,1,4,1,1,42,1,6,1,1,1,1,1],1079]
];
for (const [path, length] of samples) {
  const input = 'TOP' + path.map(n => '[' + n + ']').join('');
  const value = d.parse(input);
  assert.equal(d.standard(value).length, length);
  const counts = notation.display.plain(value);
  assert.equal(notation.compare(d.parse(counts), value), 0);
}
assert.deepEqual(notation.init().map(s => d.standard(s).length), [1,4,2,18,1,0]);
console.log('12 requested power paths and count-view round trips passed; defaults unchanged.');
