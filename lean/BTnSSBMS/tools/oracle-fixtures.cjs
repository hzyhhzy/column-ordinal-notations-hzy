'use strict';

// Read-only diagnostic bridge to the original research implementation. The
// emitted fixtures are NOT a proof of equivalence for every reachable term.
const fs = require('node:fs');
const path = require('node:path');
const crypto = require('node:crypto');
const researchRoot = process.argv[2];
if (!researchRoot) throw Error('Usage: node oracle-fixtures.cjs PATH_TO_OLD_RESEARCH');
const encoderPath = path.resolve(researchRoot, 'btnss_guard_candidate.cjs');
const {encodePruned} = require(encoderPath);
const {BT} = require(path.resolve(researchRoot, 'check_bridge.cjs'));
const deadline = Date.now() + 20000;
const size = e => e.reduce((n, [, hs]) => n + 1 + hs.reduce((m,h) => m + size(h), 0), 0);
const records = [];
const seen = new Set();
const routes = [[], [1], [2], [2, 1], [2, 2], [1, 0, 1, 1, 0, 1, 0, 2]];
for (const d of [1, 2, 3, 5]) {
  for (const route of routes) {
    if (Date.now() > deadline) throw Error('fixture time bound');
    let e = BT.call('infinity_FS', [2, d]);
    for (const n of route) e = BT.fsn(e, n, d);
    const id = `${d}:${JSON.stringify(e)}`;
    if (seen.has(id)) continue;
    if (size(e) > 80) throw Error('fixture source size bound');
    seen.add(id);
    const encoded = encodePruned(e, d, {maxColumns: 400, deadline}).matrix;
    const parents = BT.call('compute_lower_parents', [e, d]);
    records.push({d, seed: 2, route, input: e, parents, encoded});
  }
}
const sha = file => crypto.createHash('sha256').update(fs.readFileSync(file, 'utf8').replace(/\r\n/g, '\n')).digest('hex');
console.log(JSON.stringify({kind: 'finite executable regression fixtures, not a general equivalence theorem',
  sourceEncoderSha256: sha(encoderPath), count: records.length, records}));
