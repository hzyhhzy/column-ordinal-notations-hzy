'use strict';
// Bounded tests of greedy minimality, actual FS replay, and unchanged defaults.
const assert = require('node:assert/strict');
const notation = require('../../../notations/DQDN/DQDN.ne-rewritten.js');
const d = notation.debug, view = notation.display_equiv['最简操作序列'];
const growthView = notation.display_equiv['增列序列'];
const examples = new Set(notation.init());
for (let n = 0; n <= 16; n++) examples.add(d.parse('TOP[1][' + n + ']'));
for (const path of ['TOP[1][8][38]', 'TOP[1][14][38]',
    'TOP' + d.OMEGA_OMEGA_PATH.map(n => '[' + n + ']').join(''),
    'TOP' + d.OMEGA_OMEGA_PATH.slice(0, -1).map(n => '[' + n + ']').join(''),
    'TOP[1][64][8][1][1][1][8][1][1][1][26][1][1][1][30][1][1][30][1][1]' +
    '[40][8][1][42][1][4][1][1][42][1][6][1][1][1][1][1]',
    'TOP[2][0][0]', 'TOP[1][1][0][0][0]']) examples.add(d.parse(path));
// Small deterministic descendant sample. No unbounded descent search.
let current = 'TOP', seed = 19260817;
for (let i = 0; i < 80; i++) {
  if (!current || d.standard(current).length > 1200) current = 'TOP';
  seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0;
  current = notation.FS(current, seed % 5);
  examples.add(current);
}
let checkedSteps = 0;
const started = performance.now();
for (const target of examples) {
  const path = view.plain(target);
  assert.match(path, /^TOP(?:\[\d+\])*$/);
  assert.equal(d.parse(path), target, 'display path must reconstruct the same columns');
  let parent = 'TOP';
  for (const match of path.matchAll(/\[(\d+)\]/g)) {
    const n = Number(match[1]);
    assert.notEqual(parent, target, 'no redundant steps after equality');
    const next = notation.FS(parent, n);
    assert(notation.compare(next, target) >= 0, 'chosen child must still cover target');
    if (n > 0) assert(notation.compare(notation.FS(parent, n - 1), target) < 0,
      'a smaller index was sufficient');
    parent = next; checkedSteps++;
  }
  assert.equal(parent, target);
  assert.equal(view.html(target), path);
  assert.equal(view.from_display(path), target);
  const growth = growthView.plain(target);
  assert.equal(growthView.from_display(growth), target, 'growth view must reconstruct exact columns');
  assert.equal(growthView.html(target), growth);
  if (target && target !== 'TOP') {
    assert.match(growth, /^\d+(?:,\d+)*$/);
    const increments = growth.split(',').map(Number);
    assert(increments.every(n => n >= 0));
    assert.equal(1 + increments.reduce((a,b) => a+b, 0), d.standard(target).length);
  }
}
assert.equal(view.plain('TOP'), 'TOP');
assert.equal(view.plain(''), 'TOP[0]');
assert.equal(view.plain(d.parse('1')), 'TOP[1][0]');
assert.equal(view.plain(d.parse('TOP[2][0][0]')), 'TOP[1]');
assert.equal(growthView.plain('TOP'), 'TOP');
assert.equal(growthView.plain(''), '∅');
assert.equal(growthView.plain(d.parse('1')), '0');
assert.equal(growthView.plain(d.parse('TOP[1]')), '1');
assert.equal(growthView.plain(d.parse('TOP[1][1]')), '1,16');
assert.equal(growthView.plain(d.parse('TOP[1][1][0][0]')), '1,14');
for (const invalid of ['-1', '1,,2', '0,1', '1,0,0', '[1][16]'])
  assert.throws(() => growthView.from_display(invalid), SyntaxError);
assert.deepEqual(notation.init().map(s => d.standard(s).length), [1,4,2,18,1,0]);
// Resource failure must stay an error, never a truncated or invented path.
const value = d.parse('TOP[1][14][38]'), originalWork = d.LIMITS.work;
d.clearCache();
try {
  d.LIMITS.work = 2;
  assert.throws(() => view.plain(value), d.ResourceLimit);
} finally { d.LIMITS.work = originalWork; }
console.log(JSON.stringify({examples: examples.size, checkedSteps,
  elapsedMS: Math.round(performance.now() - started), views: 4,
  defaultsUnchanged: true, note: 'API checks, not a live NER browser test.'}));
