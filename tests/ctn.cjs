'use strict';
// Bounded Python parity, lossless displays, local counts, and real NER host.
const fs = require('node:fs'), path = require('node:path'), vm = require('node:vm');
const assert = require('node:assert/strict');
const {spawnSync} = require('node:child_process');
const {performance} = require('node:perf_hooks');
const notationFile = path.resolve(__dirname, '../notations/CTN/CTN.ne-rewritten.js');
const start = performance.now(), N = require(notationFile), D = N.debug;
const source = fs.readFileSync(notationFile, 'utf8');
const referenceProgram = String.raw`
import itertools, json, random, unittest
import sys
sys.path.insert(0, ${JSON.stringify(path.dirname(notationFile))})
sys.path.insert(0, ${JSON.stringify(__dirname)})
import ctn_table as old
import ctn as c
import ctn_table_cases as test
classified, legal = [], {''}
for length in range(13):
    for digits in itertools.product('12', repeat=length):
        word = ''.join(digits)
        valid = c.is_standard(word)
        classified.append([word, valid])
        if valid: legal.add(word)
rng = random.Random(20260927)
for trial in range(200):
    word = '2'
    for step in range(20):
        legal.add(word)
        word = c.fundamental(word, rng.randrange(10))
        if not word: break
terms = [{'word': w, 'fs': [c.fundamental(w, n) for n in range(12)]} for w in sorted(legal)]
tables = []
for length in range(7):
    for values in itertools.product(range(3), repeat=length):
        tables.append({'values': list(values), 'valid': c.table_tree(values)})
clauses, original = [], old.check_entry
def record(values, index):
    result = original(values, index)
    if isinstance(values, test.SparseTable):
        clauses.append({'size': str(len(values)), 'index': str(index),
                        'entries': {str(k): str(v) for k,v in values.entries.items()}, 'valid': result})
    return result
old.check_entry = record
names = ['test_atomic_arithmetic_and_scope', 'test_boolean_rules',
         'test_existential_witness_and_negative_instances', 'test_set_quantifier_and_membership',
         'test_comprehension']
result = unittest.TestResult()
unittest.TestSuite(test.TableTests(n) for n in names).run(result)
assert result.wasSuccessful(), (result.errors, result.failures)
large = []
for size in (1000, 5000):
    values = test.shallow_table(size)
    word = c.encode_table(values, cap=True)
    assert c.is_standard(word)
    large.append({'values': values, 'word': word})
print(json.dumps({'classified': classified, 'terms': terms, 'tables': tables,
                  'clauses': clauses, 'large': large}))
`;
if (process.argv.includes('--print-reference-script')) { process.stdout.write(referenceProgram); process.exit(0); }
let referenceText;
if (process.argv.includes('--fixtures-stdin')) referenceText = fs.readFileSync(0, 'utf8');
else {
  const result = spawnSync('python', ['-c', referenceProgram],
    {cwd:path.dirname(notationFile), env:{...process.env, PYTHONDONTWRITEBYTECODE:'1', PYTHONPATH:__dirname},
      encoding:'utf8', timeout:20000, maxBuffer:16*1024*1024});
  assert.equal(result.status, 0, result.stderr || String(result.error));
  referenceText = result.stdout;
}
const fixtures = JSON.parse(referenceText);
let fsChecks = 0, displayChecks = 0, countChecks = 0;
for (const [word, valid] of fixtures.classified) {
  let result = true;
  try { D.inspect(word); } catch (error) { if (error instanceof D.ResourceLimit) throw error; result = false; }
  assert.equal(result, valid, word);
}
for (const item of fixtures.tables) assert.equal(D.tableTree(item.values.map(BigInt)), item.valid);
for (const item of fixtures.clauses) {
  const values = new Map(Object.entries(item.entries).map(([k, v]) => [BigInt(k), BigInt(v)]));
  const read = address => { assert(values.has(address), 'Unexpected dependency ' + address); return values.get(address); };
  assert.equal(D.checkEntry(BigInt(item.size), read, BigInt(item.index), new D.Budget()), item.valid);
}
for (const {word, fs: expected} of fixtures.terms) {
  D.inspect(word);
  assert.equal(N.is_limit(word), word.endsWith('2'));
  assert.equal(JSON.parse(JSON.stringify(word)), word);
  for (const view of [N.display, ...Object.values(N.display_equiv)]) {
    assert.equal(typeof view.plain(word), 'string');
    assert.equal(typeof view.html(word), 'string');
    if (view.from_display) assert.equal(view.from_display(view.plain(word)), word);
    displayChecks++;
  }
  const before = D.runCounts(word);
  assert.equal(before.counts.map(k => '2'.repeat(k) + '1').join('') + '2'.repeat(before.tail), word);
  const blocks = D.blockCounts(word);
  if (blocks !== null) assert.equal(blocks.map(k => '1' + '2'.repeat(k - 1)).join(''), word);
  assert.deepEqual(D.columnCounts(word), [...word].map(Number));
  let previous = word.slice(0, -1);
  for (let n = 0; n < expected.length; n++) {
    const result = N.FS(word, n);
    assert.equal(result, expected[n], JSON.stringify({word, n}));
    D.inspect(result);
    assert(result.startsWith(previous));
    assert(result.startsWith(word.slice(0, -1)));
    if (word) assert(N.compare(result, word) < 0);
    if (!n) assert.equal(result, word.slice(0, -1));
    if (n && N.is_limit(word)) {
      assert(result.length > previous.length);
      assert(result.length >= word.length - 1 + n && result.length <= word.length + n);
    }
    if (n && word.endsWith('1')) assert.equal(result, word.slice(0, -1));
    if (blocks && blocks.length) {
      const resultBlocks = D.blockCounts(result), last = blocks.at(-1);
      if (last === 1) assert.deepEqual(resultBlocks, blocks.slice(0, -1));
      else assert.deepEqual(resultBlocks.slice(0, blocks.length), [...blocks.slice(0, -1), last - 1]);
      countChecks++;
    }
    previous = result; fsChecks++;
  }
  // Real per-column clearance: each 2 becomes a 1 before appended material.
  for (let length = 1; length <= Math.min(word.length, 32); length++) {
    const prefix = word.slice(0, length), keep = prefix.slice(0, -1);
    const first = N.FS(prefix, 1).slice(0, length);
    if (prefix.endsWith('1')) assert.equal(first, keep);
    else { assert.equal(first, keep + '1'); assert.equal(N.FS(first, 1), keep); }
    countChecks++;
  }
}
assert.equal(N.FS, N.FS_alter);
assert.equal(N.FS, N.FS_short);
for (let n = 0; n < 120; n++) assert.equal(N.FS('12', n), '1'.repeat(n + 1));
assert.equal(D.runText('1'), '0');
assert.equal(D.runText('12'), '0 | 2^1');
assert.equal(D.runText('2'), '∅ | 2^1');
assert.equal(D.runText('1221'), '0,2');
assert.equal(D.blockCountText('1221'), '3,1');
assert.equal(D.blockCountText('12'), '2');
assert.equal(D.blockCountText('2'), 'Top of CTN');
assert.equal(D.blockCountText(''), '0');
assert.equal(D.groupedText('11'), '⟦0⟧!');
assert.equal(D.groupedText('1111'), '⟦0⟧!·1^2');
assert.equal(D.groupedText('12121'), '⟦1⟧|2·1^1');
assert.match(D.tableText('1111'), /零号终止分支/);
assert.match(D.tableText('122221'), /候选 3 未通过检查/);
// The block view is not a new column system: its lengths/prefixes can differ.
assert.deepEqual([1, 2, 3].map(n => D.blockCountText(N.FS('1212', n))), ['2,1,1', '2,1,2', '2,1,3']);
assert.equal(D.blockCountText(N.FS('122', 0)), '2'); // original view: 1,2,2 -> 1,2
assert.equal(D.parse('1'.repeat(18)), '1'.repeat(18)); // valid here; invalid in old CTN
for (const input of ['3', '0,1', '1,,2', '[11][2]', '1,2,1,0', '22', '21', '112', '121212'])
  assert.throws(() => D.parse(input));
assert.throws(() => N.FS('2', D.LIMITS.columns + 1), D.ResourceLimit);
assert.throws(() => N.FS('12', -1));
assert.throws(() => D.encodeTable([Number.MAX_SAFE_INTEGER + 1]));

const benchmarks = []; let oversizedInputGuards = 0;
for (const item of fixtures.large) {
  const word = item.word;
  if (word.length > D.LIMITS.columns) {
    assert.throws(() => N.FS(word, 3), D.ResourceLimit); oversizedInputGuards++; continue;
  }
  assert.equal(D.encodeTable(item.values, true), word);
  assert(D.tableOK(item.values.map(BigInt)));
  const t = performance.now();
  assert.equal(N.FS(word, 3), word.slice(0, -1) + '122');
  benchmarks.push({tableEntries: item.values.length, columns: word.length, ms: +(performance.now() - t).toFixed(2)});
}
{
  const word = '1' + '2'.repeat(100000), t = performance.now();
  assert.equal(N.FS(word, 3), word.slice(0, -1) + '111');
  benchmarks.push({columns: word.length, ms: +(performance.now() - t).toFixed(2)});
}


let registered;
vm.runInNewContext(source,{register_notation:value=>{assert.equal(registered,undefined);registered=value;},performance}, {timeout:2000});
assert.equal(registered.name,'CTN');
assert.equal(registered.id,'ctn-linear-20261001');
assert.equal(registered.FS('122',3),'121211');
assert.equal(registered.display.from_display('Limit of CTN'),'2');
assert.equal(1+Object.keys(registered.display_equiv).length,6);
assert.deepEqual(JSON.parse(JSON.stringify(registered.init())),N.init());
assert(performance.now()-start<45000,'45-second suite deadline');
assert(process.memoryUsage().rss<512*1048576,'512 MiB RSS checkpoint');
console.log(JSON.stringify({passed:true,classifiedInputs:fixtures.classified.length,
  legalTerms:fixtures.terms.length,tableCases:fixtures.tables.length,fsChecks,displayChecks,countChecks,
  sparseClauses:fixtures.clauses.length,views:6,registration:'standalone VM stub; not browser clicks',benchmarks,oversizedInputGuards,
  milliseconds:+(performance.now()-start).toFixed(1),rssMiB:Math.ceil(process.memoryUsage().rss/1048576)},null,2));
