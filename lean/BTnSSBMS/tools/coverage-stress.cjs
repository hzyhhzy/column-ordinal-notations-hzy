'use strict';

// Bounded falsification check of the finite coverage lemma. Passing is not a
// proof. Inputs are raw numerically legal matrices, not claimed standard.
// The old research directory is read only and supplied explicitly.
const path = require('node:path');
const root = process.argv[2];
if (!root) throw Error('usage: node coverage-stress.cjs RESEARCH_DIRECTORY');
const { parents, compare, conditions } = require(path.join(root, 'dimensional_completion.cjs'));
const { bm } = require(path.join(root, 'check_bridge.cjs'));
const started = Date.now(), deadline = started + 25000;
let randomState = 0x2287a9;
function rand(n) {
  randomState = (Math.imul(randomState, 1664525) + 1013904223) >>> 0;
  return (randomState >>> 8) % n;
}
function raw(rows) {
  const m = [];
  for (let i = 0, size = 2 + rand(16); i < size; i++) {
    const c = [i ? rand(m[i - 1][0] + 2) : 0];
    for (let j = 1; j < rows; j++) {
      const p = parents([...m, [...c, ...Array(rows - c.length).fill(0)]]);
      const options = new Set([0]);
      for (let g = p[i][j - 1]; g >= 0; g = p[g][j - 1]) options.add(m[g][j] + 1);
      c.push([...options][rand(options.size)]);
    }
    m.push(c);
  }
  return m;
}
const report = { dimensions: [], failure: null, iterations: 0,
  scope: 'raw numeric coverage only; no standardness or universal conclusion' };
for (let rows = 1; rows <= 5 && Date.now() < deadline; rows++) {
  const targets = [], sources = [], stats = { rows, generated: 0, admitted: 0, pairs: 0 };
  for (let k = 0; k < 12000 && Date.now() < deadline; k++) {
    const m = raw(rows); stats.generated++; report.iterations++;
    if (sources.length < 350) sources.push(m);
    if (conditions(m, rows - 1, true) === null && targets.length < 350) {
      targets.push(m); stats.admitted++;
    }
    if (targets.length === 350 && sources.length === 350) break;
  }
  for (const N of targets) {
    for (let k = 0; k < 30 && Date.now() < deadline; k++) {
      const H = sources[rand(sources.length)];
      if (compare(N, H) >= 0) continue;
      const index = N.length * rows + 3;
      const child = bm('expand', H, index, true);
      stats.pairs++;
      if (compare(N, child) > 0) {
        report.failure = { rows, N, H, index, child,
          meaning: 'fails the proposed word-length witness; requires mathematical analysis' };
        break;
      }
    }
    if (report.failure || Date.now() >= deadline) break;
  }
  report.dimensions.push(stats);
  if (report.failure) break;
}
report.elapsedMs = Date.now() - started;
report.rssMiB = Math.round(process.memoryUsage().rss / 1048576);
report.deadlineReached = Date.now() >= deadline;
console.log(JSON.stringify(report, null, 2));
