'use strict';
const assert = require('node:assert/strict');
const fs = require('node:fs');
const vm = require('node:vm');
const notation = require('../../../notations/DQDN/DQDN.ne-rewritten.js');
const d = notation.debug;
const fixture = JSON.parse(fs.readFileSync(0, 'utf8').replace(/^\uFEFF/, ''));
let expansions = 0;
for (const [source, children] of fixture.rows) {
  assert.equal(d.parse(source), source);
  const a = d.standard(source);
  for (let j = 0; j < fixture.indices.length; j++) {
    const n = fixture.indices[j], child = notation.FS(source, n);
    assert.equal(child, children[j], 'FS ' + source.slice(0, 50) + ' / ' + n);
    const b = d.standard(child);
    if (source) assert(notation.compare(child, source) < 0);
    if (j) assert(children[j].startsWith(children[j - 1]));
    if (!n && source !== 'TOP') assert.equal(b.length, Math.max(0, a.length - 1));
    expansions++;
  }
}
let endpoint = 'TOP';
for (const n of fixture.path) endpoint = notation.FS(endpoint, n);
assert.equal(endpoint, fixture.endpoint);
assert.equal(d.standard(endpoint).length, 880);
d.clearCache();
const started = performance.now();
assert.equal(d.parse(notation.display.plain(endpoint)), endpoint);
const reconstructionMS = performance.now() - started;
for (const s of notation.init()) {
  assert.equal(d.parse(notation.display.plain(s)), s);
  const view = notation.display_equiv['列列表'];
  assert.equal(d.parse(view.plain(s)), s);
  assert.equal(typeof notation.display.html(s), 'string');
  assert.equal(typeof view.html(s), 'string');
  assert.equal(notation.FS(s, 2), notation.FS_short(s, 2));
  assert.equal(notation.FS(s, 2), notation.FS_alter(s, 2));
}
// NER searches for a fundamental-sequence term strictly above the next
// displayed node. Every initial limit must succeed within its default cap.
const initial = notation.init();
assert.equal(notation.id, 'dqdn-20261005-init-v2');
assert.equal(initial.length, 6);
assert.deepEqual(initial.map(s => d.standard(s).length), [1, 4, 2, 18, 1, 0]);
assert(!initial.includes(endpoint));
for (let i = 0; i < initial.length - 1; i++) {
  if (!notation.is_limit(initial[i])) continue;
  let firstIndex = -1;
  for (let n = 0; n <= 10; n++) {
    if (notation.compare(notation.FS(initial[i], n), initial[i + 1]) > 0) {
      firstIndex = n;
      break;
    }
  }
  assert(firstIndex >= 0, 'Initial NER node exceeds the default sibling-bound search cap');
  if (initial[i] === '[g:0][!:0]') assert.equal(firstIndex, 2);
}
const t = new d.Terms(new d.Budget()), rules = new Set();
for (let i = 0; i < fixture.commands.length; i++) {
  const [kind, name, args, levelOrResult, result] = fixture.commands[i];
  // Keep per-operation timers fresh; do not change the mathematical state.
  t.budget = new d.Budget();
  if (kind === 'make') assert.equal(t.make(name, ...args), levelOrResult, 'make ' + i);
  else {
    rules.add(name);
    if (result === null) assert.throws(() => t.construct(name, args, BigInt(levelOrResult)), d.BadConstruction);
    else assert.equal(t.construct(name, args, BigInt(levelOrResult)), result, 'construct ' + name + ' / ' + i);
  }
}
assert.equal(rules.size, 28);
const huge = 10n ** 90n;
const n = t.numeral(huge), successor = t.make('s', n);
assert.equal(t.data[t.computationChild(successor, 0)][1], huge + 1n);
for (const bad of ['21', '22', '11112', '[n:0][q:0][!:1]',
  '[v:0][a:0,0][l:1][a:2,2][!:3]', '[g:0][!:99]', '[g:0][!:0][g:99]', '1,,2'])
  assert.throws(() => d.parse(bad), Error, bad);
const untypedLoop = '[v:0][a:0,0][l:1][a:2,2][!:3]';
assert.throws(() => notation.FS(untypedLoop, 1), SyntaxError);
assert.throws(() => notation.compare(untypedLoop, 'TOP'), SyntaxError);
assert.throws(() => notation.is_limit(untypedLoop), SyntaxError);
assert.throws(() => notation.FS('TOP', -1));
assert.throws(() => notation.FS('TOP', Number.MAX_SAFE_INTEGER), d.ResourceLimit);
assert.throws(() => d.natural(Number.MAX_SAFE_INTEGER + 1), SyntaxError);
const old = d.LIMITS.work;
try { d.LIMITS.work = 2; d.clearCache(); assert.throws(() => d.parse('TOP[1][54]'), d.ResourceLimit); }
finally { d.LIMITS.work = old; }
let registered;
vm.runInNewContext(fs.readFileSync(__dirname + '/../../../notations/DQDN/DQDN.ne-rewritten.js', 'utf8'),
  {register_notation: n => { registered = n; }, performance}, {timeout: 2000});
assert.equal(registered.name, 'DQDN');
assert.equal(registered.id, 'dqdn-20261005-init-v2');
assert.equal(registered.init().length, 6);
assert.equal(registered.FS('TOP', 1), '[g:0][!:0]');
assert.equal(registered.display.plain('[g:0][!:0]'), '1,2');
assert.equal(Object.keys(registered.display_equiv).length, 3);
console.log(JSON.stringify({parents: fixture.rows.length, expansions,
  constructionCommands: fixture.commands.length, rules: rules.size,
  views: 4, omegaOmegaColumns: 880, reconstructionMS,
  cacheBytes: d.cacheSize(), browserRegistration: true,
  note: 'Finite differential tests, not a well-ordering proof or a live NER UI test.'}));
