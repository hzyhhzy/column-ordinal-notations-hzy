'use strict';

// Research delta: keep two-row control/root background and full finite-bank
// cover, but ceiling high-pair -> archive/work needs only one ancestor row.
// Native SRPD and TBMS rules, source endpoint closure, and paid operations
// are unchanged. Finite tests do not establish the all-future paper contract.
const assert=require('node:assert/strict'),fs=require('node:fs');
const path=require('node:path'),Module=require('node:module'),crypto=require('node:crypto');
const Old=require('./one-port-recursive-row-bank.cjs');
const Trimmed=require('./trimmed-one-port-row-bank.cjs');
const originalPath=path.join(__dirname,'packet-recursive-row-bank-cover.cjs');
let source=fs.readFileSync(originalPath,'utf8');
const originalSHA256=crypto.createHash('sha256').update(source).digest('hex'),patches=[];
function replace(before,after,count=1){assert.equal(source.split(before).length-1,count,'exact weak-archive patch: '+before);
  source=source.split(before).join(after);patches.push({before,after,count});}
for(const p of Old.patches)replace(p.before,p.after,p.count);
replace('C(u,w)>=v.high&&C(u,e)>=2&&C(w,e)>=2','C(u,w)>=v.high&&C(u,e)>=1&&C(w,e)>=1');
replace('C(r,N)>=s.active.background&&C(u,N)>=2&&C(v,N)>=2',
  'C(r,N)>=s.active.background&&C(u,N)>=1&&C(v,N)>=1');
const generatedPath=path.join(__dirname,'weak-archive-row-bank.generated.cjs');
const runtime=new Module(generatedPath,module);runtime.filename=generatedPath;runtime.paths=module.paths;
runtime._compile(source,generatedPath);
const R=runtime.exports,Initial=require('./packet-amplified-resource-cover.cjs');
const S=require('../m13-lists-20260926/SRPD.ne-rewritten.js');
const {createCertifier}=require('../e0mn-y13425810-20260920/finite-local-certificate.cjs');
const {P,Sparse,B,limits}=R,started=Date.now(),copy=x=>JSON.parse(JSON.stringify(x));
Object.assign(limits,{width:160000,downTransientWidth:320000});
Object.assign(P.limits,limits);Object.assign(P.E.limits,limits);
function tick(){P.tick();assert(Date.now()-started<20000,'weak archive time guard');
  assert(process.memoryUsage().rss<650*2**20,'weak archive RSS guard');}
function restore(s,v=s.root){s.active=v;s.archive=v.points.at(-1);P.prepare(s,s.archive,1,true);}

function makeSeed(columns){
  // Start from the preceding CERTIFIED Qtrim, not a hand-edited initial graph.
  const previous=Trimmed.makeSeed(1).seedAudit;
  let g=previous.commonSeed.map(c=>c.slice()),events=0;const previousCounts=S.counts(g),stages=[];
  const compress=a=>a.map(col=>col.flatMap((p,j)=>j===col.length-1||p!==col[j+1]
    ?[{a:p,x:[{exp:[],coeff:j+1}]}]:[]));
  const cert=createCertifier(Initial.M,{tick,maxNodes:40000});
  function move(after,event){tick();assert(after.length<=limits.width&&++events<=500);
    cert.certify({...event,before:compress(g),after:compress(after)});g=after;}
  const s={get g(){return g;},fs(n){move(S.expand(g,n),{kind:'FS',n});},
    truncate(h){assert(h>=1&&h<=g.at(-1).length);
      if(h!==g.at(-1).length)move(g.slice(0,-1).concat([g.at(-1).slice(0,h)]),{kind:'truncate',height:h});},
    down(){const col=g.at(-1),h=col.length,p=col.at(-1);assert(h>0);
      move(g.slice(0,-1).concat([col.slice(0,h-1).concat(g[p-1].slice(h-1))]),{kind:'down'});}};
  const stage=name=>stages.push({name,counts:S.counts(g),graph:g.map(c=>c.slice())});
  P.trim(s,13);P.prepare(s,10,2);stage('expose10 at row2 while keeping first parent12');
  s.fs(1);P.trim(s,14);stage('child archive13 has parents12 and7');
  s.truncate(2);s.fs(2);stage('mother archive14 and work15 retain root port2');
  P.prepare(s,7,2);s.fs(1);P.trim(s,17);
  const Q=g.map(c=>c.slice());
  assert.deepEqual(Q.slice(6),[[6],Array(7).fill(7),Array(8).fill(8),[7,7],
    Array(7).fill(10),Array(8).fill(11),[12,7],[13,7],[14],Array(7).fill(15),Array(16).fill(16)]);
  const commonCounts=S.counts(Q);
  assert.equal(commonCounts,'1,2,4,8,4,1,2,9,38,4,12,42,44,46,47,54,91');
  const capacities=Sparse.capacities(Q),at=(p,j)=>Sparse.at(capacities,p,j);
  assert(at(7,11)>=2&&at(7,12)>=2);assert.equal(at(11,12),8);
  const archiveAudit=[13,14].map(e=>({e,root:at(7,e),u:at(11,e),v:at(12,e)}));
  for(const a of archiveAudit)assert.deepEqual([a.root,a.u,a.v],[2,1,1]);
  assert.equal(at(13,14),1);
  s.fs(4*columns-1);assert.equal(g.length,15+4*columns);
  s.a=15;s.K=15;s.codes=[7,15];s.taxed=false;s.archive=14;
  s.packets=Array.from({length:columns},(_,i)=>({point:16+4*i,g1:17+4*i,g2:18+4*i,g3:19+4*i}));
  P.prepare(s,14,1,true);
  s.seedAudit={WIndex:1,r:7,background:2,columns,events,port:1,extraArchive:true,
    ceilingArchivePort:1,archiveAudit,previousCounts,commonCounts,commonSeed:Q,stages,certificates:cert.stats,
    previousSeedCertificates:previous.certificates,
    path:'Qtrim, trim13, expose10row2, [1], trim14, truncate2, [2], expose7row2, [1], trim17; [4c-1], inherit entire14'};
  Sparse.attach(s,P,limits);return s;
}
function moveInitialization(s,cut,delta){
  const move=p=>p>=cut?p+delta:p,f=h=>h>cut?h+delta:h;
  s.a=move(s.a);s.K=f(s.K);s.codes=[7,s.K];
  s.packets=s.packets.map(p=>Object.fromEntries(Object.entries(p).map(([k,v])=>[k,move(v)])));
  s.slots=s.slots.map(move);
  for(const v of R.all(s)){assert.equal(v.kind,'ceiling');v.points=v.points.map(move);if(v.high>cut)v.high+=delta;}
}
function cloneFromHighest(s,level){
  const parent=s.root;assert.equal(parent.points.length,5);
  for(let l=0;l<level;l++)assert(s.levels[l].root.points.at(-1)+4<=parent.points[0]);
  R.activate(s,parent);
  const [r,u,v,z]=parent.points,H=parent.high,N=s.g.length,D=N-r,t=s.a+2;
  const C=Sparse.capacities(s.g),at=(p,j)=>Sparse.at(C,p,j);
  assert(at(r,z)>=2&&at(u,z)>=1&&at(v,z)>=1&&at(z,N)>=1);
  assert(N-1+3*D<=limits.width);
  P.prepare(s,r,2);s.fs(3);moveInitialization(s,r,2*D);
  const root={id:s.nextId++,level,kind:'ceiling',word:copy(B.infinity_FS(level+2)),
    points:[r,u,v,z],high:H,background:2};
  s.levels[level].root=root;s.levels[level].dict.set(JSON.stringify(root.word),root);
  P.trim(s,t+3*D);restore(s,root);
  s.trace.push({kind:'weak-archive-initial-layer',level,points:root.points.slice(),parent:parent.points.slice(),width:s.g.length});
  R.check(s,'weak archive initial clone');
}
function initialize(columns=2,layers=2){
  assert(layers>=1&&layers<=12);
  const seedColumns=columns+(layers>1?1:0),s=makeSeed(seedColumns),level=layers-1;
  s.nextId=1;s.mode='weak-ceiling-archive-paper-interface';
  s.levels=Array.from({length:layers},(_,l)=>({level:l,dict:new Map(),root:null}));
  s.rowRoot=copy(B.infinity_FS(level+2));s.J=[[],[[1,copy(s.rowRoot)],[1,B.ONE()]]];
  s.source=R.fs(s.J,seedColumns-1);
  s.root={id:0,level,kind:'ceiling',word:s.rowRoot,points:[7,11,12,13,14],high:8,background:2};
  s.levels[level].root=s.root;s.levels[level].dict.set(JSON.stringify(s.rowRoot),s.root);
  s.active=s.root;s.archive=14;s.K=15;s.slots=[];s.phase='cold';s.path=[];s.trace=[];
  R.check(s,'weak archive pre-simulation seed');
  if(layers>1){
    R.prepareBudget(s,layers-1);for(let l=0;l<level;l++)cloneFromHighest(s,l);
    assert.equal(s.slots.length,0);s.packets.pop();P.trim(s,s.packets.at(-1).g3);
    s.source=R.fs(s.J,columns-1);s.phase='cold';restore(s);
  }
  s.root.points.splice(3,1);s.initializationTrace=s.trace.slice();s.trace=[];
  R.check(s,'weak archive source initial state');return s;
}
module.exports={initialize,makeSeed,R,patches,originalSHA256};
