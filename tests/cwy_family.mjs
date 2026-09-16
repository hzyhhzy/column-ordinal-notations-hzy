/** Bounded release-only checks for the three CWY-family NER artifacts.
 * Run: node --max-old-space-size=256 tests/cwy_family.mjs
 * Optional --python PATH selects the Python interpreter for the CWY oracle.
 * --fixtures-stdin instead reads `python -B tests/test_cwy.py --fixtures` on stdin,
 * for hosts where nested subprocess creation is restricted.
 * Tests are diagnostics, not formal equivalence or well-ordering proofs.
 */
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import vm from 'node:vm';
import {spawnSync} from 'node:child_process';
import * as direct from '../notations/CWY2/cwy_direct.mjs';
import {createKernel} from '../notations/Omega-CWY/core.mjs';
import {countSequence} from '../notations/Omega-CWY/counts.mjs';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const started = Date.now(), stats = {states:0, numericFS:0, compactFS:0,
  omegaFiniteFS:0, omegaSelfFS:0, prefixes:0, orderPairs:0, views:0,
  diagrams:0, invalid:0, resourceExclusions:0};
const json = x => JSON.stringify(x, (_k,v) => typeof v === 'bigint' ? String(v) : v);
const same = (a,b,note) => assert.equal(json(a),json(b),note);
function tick() {
  assert(Date.now()-started < 45000, '45-second release-test deadline');
  assert(process.memoryUsage().rss < 768*1048576, '768 MiB RSS budget');
}
function load(file) {
  const registered = [];
  const context = vm.createContext({console, performance, structuredClone,
    register_notation:n=>registered.push(n),
    register_category:()=>{throw Error('Unexpected category');}});
  vm.runInContext(readFileSync(path.join(root,file),'utf8'),context,{timeout:1200,filename:file});
  assert.equal(registered.length,1);
  return {context,n:registered[0]};
}
function call(module,fn,...args) {
  tick(); module.context.__fn=fn; module.context.__args=structuredClone(args);
  return vm.runInContext('__fn(...__args)',module.context,{timeout:1500});
}
const cwy=load('notations/CWY/wY-CWY.ne-rewritten.js');
const cwy2=load('notations/CWY2/CWY2.ne-rewritten.js');
const omega=load('notations/Omega-CWY/Omega-CWY.ne-rewritten.js');
const w=(fn,...args)=>call(cwy,fn,...args), d=(fn,...args)=>call(cwy2,fn,...args);
const o=(fn,...args)=>call(omega,fn,...args);
assert.equal(new Set([cwy.n.id,cwy2.n.id,omega.n.id]).size,3);
assert.equal(cwy.n.id,'omega-y-weak-cwy');
assert.equal(cwy2.n.id,'cwy2-direct-v2');
assert.equal(omega.n.name,'Ω-CWY');
same(Object.keys(omega.n.display_equiv),['计数序列','山脉图']);
same(Object.keys(cwy2.n.display_equiv),['ω-Y 数列','DBMS','DBMS_MN','ADBMS']);
const prefix=(a,b)=>json(a)===json(b.slice(0,a.length));
const columns=s=>d(cwy2.n.debug.columns,s);
const plain=view=>typeof view==='function'?view:view.plain;

const pythonAt=process.argv.indexOf('--python');
const python=pythonAt<0?'python':process.argv[pythonAt+1];
let fixtureText;
if(process.argv.includes('--fixtures-stdin')) {
  fixtureText=readFileSync(0,'utf8');
} else {
  const child=spawnSync(python,['-B',path.join(root,'tests/test_cwy.py'),'--fixtures'],
    {encoding:'utf8',timeout:22000,maxBuffer:4*1048576,windowsHide:true});
  assert.ifError(child.error); assert.equal(child.status,0,child.stderr);
  fixtureText=child.stdout;
}
assert(fixtureText.length<4*1048576,'fixture size budget');
const fixtures=JSON.parse(fixtureText);
stats.pythonOracle=fixtures.statistics;
for(const record of fixtures.records) {
  for(let n=0;n<4;n++) {
    const next=d(cwy2.n.FS,record.text,n);
    assert.equal(next,record.fs[n],'independent Python geometry / CWY2');
    assert.equal(direct.display(direct.fs(record.term,n)),next,'readable core / bundle');
    stats.compactFS++;
    assert.equal(o(omega.n.FS,record.text,n),next,'finite-label agreement');
    stats.omegaFiniteFS++;
  }
}

const samples=[[],[1],[1,1],[1,2],[1,3],[1,4],[1,5],[1,6],[1,4,15,51]];
const seen=new Set(samples.map(json));
for(let cursor=1;cursor<samples.length && cursor<45;cursor++) {
  for(let n=1;n<=3;n++) {
    const next=Array.from(w(cwy.n.FS,samples[cursor],n));
    if(next.length>12 || next.some(v=>!Number.isSafeInteger(v)||v>10000)) {
      stats.resourceExclusions++; continue;
    }
    if(!seen.has(json(next)) && samples.length<80) {seen.add(json(next));samples.push(next);}
  }
}
const paired=[];
for(const numeric of samples) {
  const numberText=numeric.length?numeric.join(','):'0';
  const term=d(cwy2.n.display_equiv['ω-Y 数列'].from_display,numberText);
  const graph=columns(term), before=json(graph); paired.push({numeric,term}); stats.states++;
  // The adapter stretches only its display, not its FS indices.
  const m=numeric[1], move=q=>q===0?0:q+m-1;
  const expected=graph.length<2?term:'[][]'+'[S]'.repeat(m-1)+
    graph.slice(2).map(col=>'['+col.map(([p,W])=>move(p)+':('+W.map(move).join(',')+')').join(';')+']').join('');
  assert.equal(w(plain(cwy.n.display_equiv['CWY 紧凑列表']),numeric),expected);stats.views++;
  const geometryBefore=d(cwy2.n.debug.view_stats).geometryCalls;
  for(let n=0;n<4;n++) {
    const next=d(cwy2.n.FS,term,n), following=d(cwy2.n.FS,term,n+1);
    assert(prefix(columns(next),columns(following))); stats.prefixes++;
    if(numeric.length)assert(d(cwy2.n.compare,next,term)<0);
    for(const method of ['FS','FS_alter','FS_short']) {
      const source=Array.from(w(cwy.n[method],numeric,n));
      if(source.some(v=>!Number.isSafeInteger(v))) {stats.resourceExclusions++;continue;}
      const result=d(cwy2.n[method],term,n);
      // Delay display calls so geometry independence is checked separately.
      assert.equal(direct.display(columns(result)),result);
      paired._outputs??=[];paired._outputs.push({source,result});
      stats.numericFS++;
    }
  }
  assert.equal(d(cwy2.n.debug.view_stats).geometryCalls,geometryBefore,
    'Expansion/comparison unexpectedly reconstructed geometry');
  same(columns(term),JSON.parse(before),'input mutation');
  for(const name of ['DBMS','DBMS_MN','ADBMS']) {
    assert.equal(d(plain(cwy2.n.display_equiv[name]),term),w(plain(cwy.n.display_equiv[name]),numeric));
    stats.views++;
  }
}
for(const {source,result} of paired._outputs) {
  assert.equal(d(cwy2.n.display_equiv['ω-Y 数列'].plain,result),source.length?source.join(','):'0');
}
for(const a of paired.slice(0,20))for(const b of paired.slice(0,20)) {
  assert.equal(Math.sign(d(cwy2.n.compare,a.term,b.term)),Math.sign(w(cwy.n.compare,a.numeric,b.numeric)));
  assert.equal(Math.sign(o(omega.n.compare,a.term,b.term)),Math.sign(d(cwy2.n.compare,a.term,b.term)));
  stats.orderPairs++;
}
for(const {numeric,term} of paired.slice(0,10))for(const inverted of [false,true]) {
  same(d(cwy2.n.draw_diagram.draw_diagram,term,{invert_vertical:inverted}),
    w(cwy.n.draw_diagram.draw_diagram,numeric,{invert_vertical:inverted}),'preserved full mountain');
  stats.diagrams++;
}
assert.equal(w(plain(cwy.n.display_equiv['CWY 紧凑列表']),[1,3]),'[][][S][S]');
assert.equal(w(plain(cwy.n.display_equiv['CWY 紧凑列表']),w(cwy.n.FS,[1,3],0)),'[]');
assert.equal(d(cwy2.n.FS,'Top',0),'[][]');
same(w(cwy.n.FS,[Infinity],0),[1,1]);

const omegaTerms=['T0','T1','T2','T3','W','W2','WW','T2[2]','T3[2]'];
for(let i=0;i<omegaTerms.length && i<50;i++) {
  const term=o(omega.n.display.from_display,omegaTerms[i]);
  const K=createKernel({ms:1500}), g=K.read(term);
  for(let n=0;n<4;n++) {
    const next=o(omega.n.FS,term,n), followed=o(omega.n.FS,term,n+1);
    assert.equal(next,K.write(K.fs(g,n)),'self-indexed readable core / bundle');
    assert(prefix(K.read(next).columns,K.read(followed).columns),'self-indexed prefix');
    if(g.columns.length)assert(o(omega.n.compare,next,term)<0);
    assert.equal(o(omega.n.display.from_display,next),next);
    stats.omegaSelfFS++; stats.prefixes++;
    if(n===1 && omegaTerms.length<50 && next!=='0')omegaTerms.push(next);
  }
}
for(const term of ['0','[]','W','W2','WW','T2']) {
  const counts=o(omega.n.debug.counts,term);
  const diagram=o(omega.n.debug.diagram,term,{});
  assert(diagram._omegaCWY2.complete,'unexpected partial diagram');
  assert(o(omega.n.debug.svg,term).includes(counts.text),'missing count footer');
  stats.diagrams++;
}
const K=createKernel({ms:1500}), partial=countSequence(K.read('T1[10]'),K,{steps:3,ms:1000});
assert(!partial.complete); assert(partial.values.some(v=>v===null));
assert(partial.text.startsWith('1,2,'));
assert(partial.values.slice(partial.completedColumns).every(v=>v===null));
for(const bad of ['[0:(0)]','[][0:(1)]','T-1','[][0:(0|{Limit}:1)]']) {
  assert.throws(()=>o(omega.n.display.from_display,bad));stats.invalid++;
}
for(const bad of ['[S]','E0','[0:(0)]']) {
  assert.throws(()=>d(cwy2.n.display.from_display,bad));stats.invalid++;
}
for(let n=0;n<5;n++) {
  assert.equal(o(omega.n.FS,'Top',n),o(omega.n.display.from_display,'T'+n));
}
tick();
console.log(JSON.stringify({...stats,elapsedMs:Date.now()-started,
  rssMiB:+(process.memoryUsage().rss/1048576).toFixed(1)},null,2));
