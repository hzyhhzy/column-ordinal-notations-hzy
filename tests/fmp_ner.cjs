'use strict';
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const source = fs.readFileSync(path.join(__dirname, '../notations/FMP/FMP.ne-rewritten.js'), 'utf8');
const registrations = [];
new Function('register_notation', source)(n => registrations.push(n));
assert.equal(registrations.length, 1);
const n = registrations[0], d = n.debug;
assert.equal(n.display.name, '列表');
assert.equal(Object.keys(n.display_equiv).filter(k => k === '列表').length, 0);
assert.deepEqual(Object.keys(n.display_equiv), ['计数序列', '完整对应表', '邻接表（文字）', '邻接表（图）']);
assert.equal(n.FS, n.FS_alter);
assert.equal(n.FS, n.FS_short);
const initial = n.init();
for (let i = 1; i < initial.length; i++) assert.equal(n.compare(initial[i - 1], initial[i]), 1);

const omega = d.parse('[][1]');
for (let index = 0; index < 8; index++) {
  const child = n.FS(omega, index);
  assert.equal(child.length, index + 1);
  assert.ok(child.every(c => !c.edges.length));
  assert.equal(n.compare(child, omega), -1);
}
const bmsCarrier = d.parse('[][1][2]');
assert.equal(d.countText(bmsCarrier), '1,2,3');
for (let index = 1; index < 6; index++) {
  const child = n.FS(bmsCarrier, index);
  assert.equal(child.length, 2 ** (index + 1));
  assert.equal(d.text(d.parse(d.text(child))), d.text(child));
  assert.equal(d.text(d.parse(d.text(child, true))), d.text(child));
  assert.equal(d.text(d.adjacencyParse(d.adjacencyText(child))), d.text(child));
  const shorter = n.FS(bmsCarrier, index - 1);
  assert.equal(d.text(child.slice(0, shorter.length)), d.text(shorter));
}

// Partial count output must keep verified digits, then use '?' rather than
// a fake integer.  A later computation with a larger budget can finish it.
const longSeed = d.seed(8), originalLimits = {...d.LIMITS};
d.clearCountCache();
d.LIMITS.work = 12;
d.LIMITS.countMs = 10000;
const partial = d.countValues(longSeed);
assert.deepEqual(partial.slice(0, 2), [1n, 2n]);
assert.ok(partial.slice(2).every(x => x === null));
assert.ok(d.countText(longSeed).includes('?'));
Object.assign(d.LIMITS, originalLimits);
assert.ok(d.countValues(longSeed).every(x => typeof x === 'bigint'));

// An expansion guard is an error, never an altered cut child.
const before = d.text(bmsCarrier);
d.LIMITS.columns = 3;
assert.throws(() => n.FS(bmsCarrier, 2), d.ResourceLimit);
assert.equal(d.text(bmsCarrier), before);
Object.assign(d.LIMITS, originalLimits);

// The projection-copy branch is exercised by a short standard path.
const projected = n.FS(n.FS(d.seed(4), 1), 1);
assert.equal(projected.length, 18);
assert.equal(n.FS(projected, 4).length, 82);
d.validate(n.FS(projected, 4));
assert.throws(() => d.parse('[1]'));
assert.throws(() => d.parse('[][0]'));
assert.throws(() => d.parse('[][1][1:2*;2]'));
assert.equal(n.compare(d.parse('0'), d.parse('0')), 0);

const marked = d.parse('[][1][1:2;2][1:2;2][1:2,2:4*;3][1:2;2]');
const restored = JSON.parse(JSON.stringify(marked));
assert.ok(restored.every(c => Array.isArray(c.stars)));
d.validate(restored);
assert.equal(n.compare(restored, marked), 0);
assert.equal(d.text(n.FS(restored, 1)), d.text(n.FS(marked, 1)));
assert.equal(d.countText(restored), d.countText(marked));
assert.equal(d.adjacencyText(marked), '[][2][2,3][2,4][2,4*,5][2,6]');
assert.equal(d.text(d.adjacencyParse(d.adjacencyText(marked))), d.text(marked));
const picture = d.adjacencyDiagram(marked);
assert.equal(picture._fmp.countText, '1,2,4,4,3,4');
assert.equal(picture._fmp.entries.length, marked.reduce((sum, c) => sum + Math.max(0, c.edges.length - 1), 0));
assert.equal(picture.extra_text.filter(t => t._fmp?.kind === 'diagonal').length, marked.length);
assert.ok(picture._fmp.entries.every(e => e.source < e.column && e.target <= e.column));
assert.ok(picture._fmp.entries.some(e => e.column === 5 && e.source === 2 && e.target === 4 && e.starred));
assert.ok(d.adjacencySVG(marked).includes('4*'));
const oldSvgCharacters = d.VIEW.svgCharacters;
d.VIEW.svgCharacters = 10;
const blockedSvg = d.adjacencySVG(marked);
assert.ok(blockedSvg.includes('未截取局部'));
assert.ok(!blockedSvg.includes('<svg'));
d.VIEW.svgCharacters = oldSvgCharacters;
const oldViewColumns = d.VIEW.columns;
d.VIEW.columns = 3;
const blockedPicture = n.draw_diagram.draw_diagram(marked);
assert.equal(blockedPicture._fmp.complete, false);
assert.equal(blockedPicture.elements.length, 0);
d.VIEW.columns = oldViewColumns;
assert.throws(() => d.adjacencyParse('[][2][1]'));
console.log('FMP NER: registration, five views, FS, counts, guards, JSON persistence, projection and lossless triangular table passed.');
