'use strict';
// One bounded, local-only JS reference call for the Python regression suite.
const fs = require('node:fs');
const vm = require('node:vm');
const input = fs.readFileSync(0, 'utf8');
if (input.length > 4000000) throw Error('test payload too large');

function checkReference() {
  const path = require('node:path');
  const assert = require('node:assert/strict');
  const root = path.resolve(__dirname, '..');
  const request = JSON.parse(input);
  const files = {
    rpd: 'notations/RPD/RPD-mountain.ne-rewritten.js',
    lrd: 'notations/LRD/LRD.ne-rewritten.js',
    omega3: 'notations/Omega-LRD3/Omega-LRD3.ne-rewritten.js'
  };
  const notations = {};
  for (const [name, file] of Object.entries(files)) {
    new Function('register_notation', fs.readFileSync(path.join(root, file), 'utf8'))(n => {
      assert(!notations[name]);
      notations[name] = n;
    });
    assert(notations[name]);
  }
  assert(request.cases.length <= 300 && request.comparisons.length <= 1000);
  let expansions = 0, comparisons = 0;
  for (const item of request.cases) {
    const ne = notations[item.notation];
    assert(ne && item.outputs.length === 4);
    for (let n = 0; n < 4; n++) {
      assert.equal(ne.FS(item.raw, n), ne.display.plain(item.outputs[n]),
        item.notation + ' case ' + item.id + ' [' + n + ']');
      expansions++;
    }
  }
  for (const item of request.comparisons) {
    assert.equal(Math.sign(notations[item.notation].compare(item.a, item.b)), item.expected,
      item.notation + ': comparison');
    comparisons++;
  }
  console.log(JSON.stringify({cases: request.cases.length, expansions, comparisons}));
}
new vm.Script('(' + checkReference.toString() + ')();')
  .runInNewContext({require, __dirname, fs, input, console}, {timeout: 15000});
