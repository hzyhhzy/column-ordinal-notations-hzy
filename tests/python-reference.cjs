'use strict';
// Bounded local-only JS reference calls. Yield between API calls so each call
// has a normal event-task budget; do not disable a notation's own limits.
const fs = require('node:fs');
const vm = require('node:vm');
const path = require('node:path');
const assert = require('node:assert/strict');
const input = fs.readFileSync(0, 'utf8');
if (input.length > 4000000) throw Error('test payload too large');
const began = Date.now();
const root = path.resolve(__dirname, '..');
const request = JSON.parse(input);
const files = {
  rpd: 'notations/RPD/RPD-mountain.ne-rewritten.js',
  lrd: 'notations/LRD/LRD.ne-rewritten.js',
  omega3: 'notations/Omega-LRD3/Omega-LRD3.ne-rewritten.js',
  ard: 'notations/ARD/ARD.ne-rewritten.js',
  ard_legacy: 'notations/ARD-legacy/ARD-arcs.ne-rewritten.js'
};
const contexts = {};
for (const [name, file] of Object.entries(files)) {
  const ctx = vm.createContext({queueMicrotask});
  ctx.register_notation = notation => { assert(!ctx.ne); ctx.ne = notation; };
  vm.runInContext(fs.readFileSync(path.join(root, file), 'utf8'), ctx,
    {timeout: 1000, filename: path.basename(file)});
  assert(ctx.ne);
  contexts[name] = ctx;
}
async function call(name, expression, args) {
  await Promise.resolve();
  assert(Date.now() - began < 15000, '15-second reference deadline');
  const ctx = contexts[name];
  assert(ctx, 'known notation');
  ctx.args = args;
  return vm.runInContext(expression, ctx, {timeout: 1250});
}
async function main() {
  assert(request.cases.length <= 300 && request.comparisons.length <= 1000);
  let expansions = 0, comparisons = 0, countChecks = 0;
  for (const item of request.cases) {
    assert(item.outputs.length === 4);
    for (let n = 0; n < 4; n++) {
      const result = await call(item.notation,
        '({actual:ne.FS(args.raw,args.n),expected:ne.display.plain(args.expected)})',
        {raw:item.raw,n,expected:item.outputs[n]});
      assert.equal(result.actual, result.expected,
        item.notation + ' case ' + item.id + ' [' + n + ']');
      expansions++;
    }
  }
  for (const item of request.comparisons) {
    assert.equal(await call(item.notation, 'Math.sign(ne.compare(args.a,args.b))', item),
      item.expected, item.notation + ': comparison');
    comparisons++;
  }
  assert((request.counts || []).length <= 100);
  for (const item of request.counts || []) {
    const values = await call(item.notation, 'ne.debug.counts(args).map(String)', item.raw);
    assert.deepEqual(Array.from(values), item.expected, item.notation + ': exact counts');
    countChecks++;
  }
  console.log(JSON.stringify({cases:request.cases.length, expansions, comparisons, countChecks}));
}
main().catch(error => { console.error(error); process.exitCode = 1; });
