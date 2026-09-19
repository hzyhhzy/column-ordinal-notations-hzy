/* Bounded portable import regression: fixtures on stdin, no browser or network.
   Run with --max-old-space-size=256. Deadline 35 s; 512 MiB RSS; vm call 2 s. */
'use strict';
const fs = require('node:fs'), path = require('node:path'), vm = require('node:vm');
const assert = require('node:assert/strict');
const root = path.resolve(__dirname, '..'), started = Date.now();
const fixtures = JSON.parse(fs.readFileSync(0, 'utf8'));
function tick() {
  assert(Date.now() - started < 35000, '35-second deadline');
  assert(process.memoryUsage().rss < 512 * 1048576, '512 MiB RSS ceiling');
}
const specs = {
  ACD: ['notations/ACD/ACD.ne-rewritten.js', 'acd-candidate-20260918'],
  CSD: ['notations/CSD/CSD.ne-rewritten.js', 'csd-v01'],
  ICP: ['notations/ICP/ICP.ne-rewritten.js', 'icp-candidate-20260919'],
  e0MN: ['external/e0MN/e0MN-fast-counting.ne-rewritten.js', 'e0mn-fast-counting-v02'],
  strong: ['external/strong-e0MN/strong-e0MN-fast-counting.ne-rewritten.js', 'strong-e0mn-all-coeff-fast-counting-20260919'],
};
const loaded = new Map();
function load(name) {
  const [filename, id] = specs[name];
  const context = vm.createContext({queueMicrotask});
  context.register_notation = ne => { assert(!context.ne); context.ne = ne; };
  vm.runInContext(fs.readFileSync(path.join(root, filename), 'utf8'), context, {timeout: 1500});
  assert.equal(context.ne.id, id);
  loaded.set(name, context);
  return context;
}
async function call(context, code, args) {
  await new Promise(setImmediate); tick(); context.args = args;
  return vm.runInContext(code, context, {timeout: 2000});
}
const stats = {pythonJsSteps: 0, countValues: 0, countUnknown: 0, views: 0,
  e0NaiveCounts: 0, e0NaiveUnknown: 0, e0Steps: 0, chainSteps: 0};
async function main() {
  for (const item of fixtures.notations) {
    const context = load(item.name), ne = context.ne;
    assert.equal(ne.FS, ne.FS_alter); assert.equal(ne.FS, ne.FS_short);
    const seen = new Set();
    for (const test of item.cases) {
      const result = await call(context, `(() => {
        const a = ne.display.from_display(args.input), before = JSON.stringify(a);
        const b = ne.FS(a, args.index), expected = ne.display.from_display(args.output);
        return {actual: ne.display.plain(b), expected: ne.display.plain(expected),
          unchanged: before === JSON.stringify(a), compare: ne.compare(b, expected)};
      })()`, test);
      assert.equal(result.actual, result.expected); assert(result.unchanged); assert.equal(result.compare, 0);
      stats.pythonJsSteps++;
      if (!seen.has(test.input)) {
        seen.add(test.input);
        if (test.counts) {
          const counts = await call(context, 'ne.debug.counts(ne.display.from_display(args)).map(x => x === null ? null : String(x))', test.input);
          assert.equal(counts.length, test.counts.length);
          counts.forEach((value, j) => {
            if (value === null) stats.countUnknown++;
            else { assert.equal(value, test.counts[j]); stats.countValues++; }
          });
        } else stats.countUnknown++;
        if (seen.size <= 6) {
          const views = await call(context, `(() => {
            const a = ne.display.from_display(args);
            return [ne.display, ...Object.values(ne.display_equiv)].map(d => {
              if (typeof d.plain === 'function') if (typeof d.plain(a) !== 'string') throw Error('plain');
              if (typeof d.html === 'function') if (typeof d.html(a) !== 'string') throw Error('html');
              return d.name || '';
            });
          })()`, test.input);
          assert.equal(views.filter(x => x === '列表').length, 1);
          stats.views += views.length;
        }
      }
    }
  }
  const icp = loaded.get('ICP');
  assert(icp.ne.description.some(t => t.includes('不良序')));
  await call(icp, 'globalThis.chain = ne.FS(ne.FS(ne.FS(ne.debug.seed(3), 1), 1), 0)', null);
  for (let i = 0; i < 100; i++) {
    const r = await call(icp, '(() => { const old = chain; chain = ne.FS(chain, 1); return [chain.length, ne.compare(chain,old)]; })()', null);
    assert.equal(r[0], 7 + 3 * i); assert(r[1] < 0); stats.chainSteps++;
  }
  for (const name of ['e0MN', 'strong']) {
    const context = load(name);
    assert(context.ne.description.some(t => t.includes('test_alpha0')));
    assert.notEqual(context.ne.FS, context.ne.FS_short);
    const targets = [
      ['()(1:ω)(2:ω2)(1:1)', '1,3,13,2'],
      ['()(1:ω)(2:ω^2)()(4:ω)(5:ω^2+1)', '1,3,14,1,6,54'],
      ['()(1:ω)(2:ω^2)()(4:ω)(5:ω^3+ω+1)', '1,3,14,1,6,185'],
      ['()(1:ω)(2:ω^2)(1:1)', '1,3,14,2'],
      ['()(1:ω)(2:ω+1)', '1,3,11'],
    ];
    if (name === 'e0MN') for (const [raw, expected] of targets) {
      const actual = await call(context, 'ne.debug.exactCounts(ne.display.from_display(args)).map(String).join(",")', raw);
      assert.equal(actual, expected);
    }
    const result = await call(context, `(() => {
      const queue = [], seen = new Set(); let checks=0, unknown=0, steps=0;
      const add = a => { const key=JSON.stringify(a); if(a.length<=9 && key.length<5000 && seen.size<160 && !seen.has(key)){seen.add(key);queue.push(a);} };
      for(let n=0;n<=2;n++)add(ne.FS('Limit',n));
      for(let i=0;i<queue.length && i<80;i++) {
        const a=queue[i], naive=[]; let work=0, complete=true;
        for(let j=0;j<a.length;j++) {
          let part=a.slice(0,j+1), count=1n;
          while(part.at(-1).length) { if(++work>1500){complete=false;break;} part=ne.debug.down(part); count++; }
          if(!complete)break; naive.push(count);
        }
        if(complete) {
          const fast=ne.debug.exactCounts(a,{maxMs:80,maxWork:200000});
          if(fast.map(String).join(',')!==naive.map(String).join(','))throw Error('Fast-count mismatch');checks++;
        } else unknown++;
        const before=JSON.stringify(a);
        for(const fn of [ne.FS,ne.FS_short])for(let n=0;n<3;n++){
          const b=fn(a,n); if(!ne.debug.isLegalExpr(b))throw Error('Illegal output');
          if(a.length && ne.compare(b,a)>=0)throw Error('Nondecreasing FS');add(b);steps++;
        }
        if(JSON.stringify(a)!==before)throw Error('Input mutation');
      }
      if(checks<20)throw Error('Insufficient exact-count checks');
      return {checks,unknown,steps};
    })()`, null);
    stats.e0NaiveCounts += result.checks; stats.e0NaiveUnknown += result.unknown; stats.e0Steps += result.steps;
    const views = await call(context, 'Object.keys(ne.display_equiv)', null);
    assert.deepEqual(Array.from(views), ['行高差', '计数序列']);
  }
  assert.equal(new Set([...loaded.values()].map(c => c.ne.id)).size, 5);
  assert(stats.pythonJsSteps >= 1000); assert(stats.countValues >= 500);
  console.log(JSON.stringify({ok: true, ...stats, states: fixtures.notations.map(x => ({
    name:x.name,states:x.states,sizeSkips:x.size_skips,countSkips:x.count_skips})),
    seconds:(Date.now()-started)/1000,rssMiB:Math.round(process.memoryUsage().rss/1048576)},null,2));
}
main().catch(e => { console.error(e); process.exitCode=1; });
