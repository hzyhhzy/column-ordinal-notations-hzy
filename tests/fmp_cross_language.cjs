'use strict';
// Reads the bounded Python oracle from stdin. No subprocesses or file writes.
const assert = require('node:assert/strict');
const fs = require('node:fs');
const {performance} = require('node:perf_hooks');
const notation = require('../notations/FMP/FMP.ne-rewritten.js');
const d = notation.debug;
const started = performance.now();
const payload = JSON.parse(fs.readFileSync(0, 'utf8'));
assert.equal(payload.schema, 1);
assert.ok(payload.fixtures.length >= 100 && payload.fixtures.length <= 1000);
let expansions = 0, compared = 0, countValues = 0, unknownCounts = 0, prefixes = 0;
let guards = 0, maxColumns = 0;
function clock() {
  assert.ok(performance.now() - started < 30000, '30-second test deadline');
  assert.ok(process.memoryUsage().rss < 768 * 1024 * 1024, '768 MiB RSS ceiling');
}
function countCheck(actual, expected) {
  assert.equal(actual.length, expected.length);
  for (let i = 0; i < actual.length; ++i) {
    if (actual[i] === null) { ++unknownCounts; continue; }
    assert.equal(String(actual[i]), expected[i]);
    ++countValues;
  }
}
for (const fixture of payload.fixtures) {
  clock();
  const source = d.parse(fixture.source);
  let child;
  try {
    child = notation.FS(source, fixture.index);
  } catch (error) {
    if (!(error instanceof d.ResourceLimit)) throw error;
    ++guards;
    continue; // Explicit unknown, not a passed expansion.
  }
  ++expansions;
  assert.equal(d.text(child), fixture.child);
  assert.equal(d.text(source), fixture.source, 'FS must not mutate its input');
  assert.equal(d.text(child.slice(0, source.length - 1)), d.text(source.slice(0, -1)));
  d.validate(child);
  maxColumns = Math.max(maxColumns, source.length, child.length);
  countCheck(d.countValues(source), fixture.sourceCounts);
  countCheck(d.countValues(child), fixture.childCounts);
  try {
    assert.equal(notation.compare(child, source), fixture.compare);
    ++compared;
  } catch (error) {
    if (!(error instanceof d.ResourceLimit)) throw error;
    ++guards;
  }
  if (fixture.previous !== undefined) {
    const previous = d.parse(fixture.previous);
    assert.equal(d.text(child.slice(0, previous.length)), fixture.previous);
    ++prefixes;
  }
  const restored = JSON.parse(JSON.stringify(child));
  assert.equal(d.text(restored), fixture.child);
  assert.equal(d.text(d.parse(d.text(restored, true))), fixture.child);
  assert.equal(d.text(d.adjacencyParse(d.adjacencyText(restored))), fixture.child);
}
assert.ok(expansions >= 100 && compared >= 100 && countValues >= 1000);
clock();
console.log(JSON.stringify({
  suite: 'FMP Python/NER differential', expansions, compared, countValues,
  unknownCounts, prefixes, guards, maxColumns, pythonSkipped: payload.skipped,
  pythonSeconds: payload.elapsedSeconds,
  nodeSeconds: +(performance.now() - started).toFixed(3) / 1000,
  finalRssMiB: +(process.memoryUsage().rss / 1048576).toFixed(2)
}));
