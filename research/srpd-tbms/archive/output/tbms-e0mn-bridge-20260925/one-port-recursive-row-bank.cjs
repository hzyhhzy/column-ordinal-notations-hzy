'use strict';

// Bounded research companion to ONE-PORT-WHOLE-TBMS.zh-CN.md.
// The all-future delta argument is on PAPER, not established by these tests.
// The native TBMS and SRPD/e0MN rules are NEVER changed.
// Audit-visible exact patches modify only the old simulation interface:
// bank background2, port1, entire-archive work, and a real trim to the healthy
// first main guard before a unit source step (rather than row1 reload).
const assert=require('node:assert/strict'),fs=require('node:fs');
const path=require('node:path'),Module=require('node:module'),crypto=require('node:crypto');
const originalPath=path.join(__dirname,'packet-recursive-row-bank-cover.cjs');
let source=fs.readFileSync(originalPath,'utf8');
const originalSHA256=crypto.createHash('sha256').update(source).digest('hex'),patches=[];
function replace(before,after,count=1){
  assert.equal(source.split(before).length-1,count,'exact interface patch: '+before);
  source=source.split(before).join(after);patches.push({before,after,count});
}
replace('?3+(C?Cap.at(C,i+1,j+1):lowerGrade(s,v.level,v.profile[i][j]))',
  '?2+(C?Cap.at(C,i+1,j+1):lowerGrade(s,v.level,v.profile[i][j]))');
replace('P.E.restore(s,s.archive);','P.prepare(s,s.archive,1,true);');
replace('assert.equal(s.g[s.a-1].length,2);assert.equal(s.g[s.a-1][0],s.g[s.a-1][1]);',
  'assert.equal(s.g[s.a-1].length,1);');
replace('v.background>=3&&v.background<=s.seedAudit.background','v.background>=2&&v.background<=s.seedAudit.background');
replace('C(u,e)>=3&&C(w,e)>=3','C(u,e)>=2&&C(w,e)>=2');
replace("C(p,s.a)>=2,label+': private bank port'","C(p,s.a)>=1,label+': private bank port'");
replace("C(s.a,p.point)>=2,'main point private port'","C(s.a,p.point)>=1,'main point private port'");
replace("C(s.a,t)>=2&&C(first,t)>=1,'coupon main/private ports'","C(s.a,t)>=1&&C(first,t)>=1,'coupon main/private ports'");
replace("C(v.points.at(-1),t)>=2,'coupon all archive ports'","C(v.points.at(-1),t)>=1,'coupon all archive ports'");
replace("assert.deepEqual(s.g.at(-1).slice(1),s.g[s.archive-1].slice(1),'active archive inherited tail');",
  "assert.deepEqual(s.g.at(-1).slice(),s.g[s.archive-1].slice(),'active archive inherited entire column');");
replace("assert(C(s.a,N)===1&&C(first,N)>=1,'work separation and main reload port');",
  "assert(C(s.a,N)===0,'bank work has no private ancestry; main returns by actual trim');");
replace('C(u,N)>=3&&C(v,N)>=3','C(u,N)>=2&&C(v,N)>=2');
replace('P.trim(s,z);P.prepare(s,e,2);','P.trim(s,z);P.prepare(s,e,1);');
replace('cut=points.at(-2);row=3;blocks=2;','cut=points.at(-2);row=2;blocks=2;');
replace('row=3+lowerGrade(s,level,a)+1','row=2+lowerGrade(s,level,a)+1');
replace('row=3+lowerGrade(s,level,beta)+1','row=2+lowerGrade(s,level,beta)+1');
replace('const needed=3+lowerGrade(s,level,alpha)','const needed=2+lowerGrade(s,level,alpha)');
replace('P.prepare(s,s.packets.at(-1).g1,1,true);','P.trim(s,s.packets.at(-1).g1);');
const generatedPath=path.join(__dirname,'one-port-recursive-row-bank.generated.cjs');
const runtime=new Module(generatedPath,module);runtime.filename=generatedPath;runtime.paths=module.paths;
runtime._compile(source,generatedPath);
const R=runtime.exports,Initial=require('./packet-amplified-resource-cover.cjs');
const S=require('../m13-lists-20260926/SRPD.ne-rewritten.js');
const {createCertifier}=require('../e0mn-y13425810-20260920/finite-local-certificate.cjs');
const {P,Sparse,B,limits}=R,started=Date.now(),copy=x=>JSON.parse(JSON.stringify(x));
Object.assign(limits,{width:160000,downTransientWidth:320000});
Object.assign(P.limits,limits);Object.assign(P.E.limits,limits);
function tick(){P.tick();assert(Date.now()-started<20000);assert(process.memoryUsage().rss<650*2**20);}
function restore(s,v=s.root){s.active=v;s.archive=v.points.at(-1);P.prepare(s,s.archive,1,true);}
function makeSeed(columns){
  let g=[[],[1],[2,2],[3,3,3],[2,2],[1]],events=0;
  const compress=a=>a.map(col=>col.flatMap((p,j)=>j===col.length-1||p!==col[j+1]
    ?[{a:p,x:[{exp:[],coeff:j+1}]}]:[]));
  const cert=createCertifier(Initial.M,{tick,maxNodes:40000});
  function move(after,event){
    tick();assert(after.length<=limits.width&&++events<=500);
    cert.certify({...event,before:compress(g),after:compress(after)});g=after;
  }
  const s={get g(){return g;},
    fs(n){move(S.expand(g,n),{kind:'FS',n});},
    truncate(h){assert(h>=1&&h<=g.at(-1).length);
      if(h!==g.at(-1).length)move(g.slice(0,-1).concat([g.at(-1).slice(0,h)]),{kind:'truncate',height:h});},
    down(){const col=g.at(-1),h=col.length,p=col.at(-1);assert(h>0);
      move(g.slice(0,-1).concat([col.slice(0,h-1).concat(g[p-1].slice(h-1))]),{kind:'down'});}
  };
  s.fs(1);for(let h=7;h>3;h--)s.down();
  const candidate=g.map(c=>c.slice());
  s.fs(1);s.fs(4);P.prepare(s,7,2);s.fs(1);P.trim(s,17);
  const Q=g.map(c=>c.slice());
  assert.deepEqual(Q.slice(6),[[6],Array(7).fill(7),Array(8).fill(8),[7,7],
    Array(7).fill(10),Array(10).fill(11),Array(10).fill(12),Array(10).fill(13),
    [14],Array(7).fill(15),Array(16).fill(16)]);
  s.fs(4*columns-1);assert.equal(g.length,15+4*columns);
  s.a=15;s.K=15;s.codes=[7,15];s.taxed=false;s.archive=14;
  s.packets=Array.from({length:columns},(_,i)=>({point:16+4*i,g1:17+4*i,g2:18+4*i,g3:19+4*i}));
  P.prepare(s,14,1,true);
  s.seedAudit={WIndex:1,r:7,background:2,columns,events,port:1,extraArchive:true,
    candidateCounts:S.counts(candidate),commonCounts:S.counts(Q),commonSeed:Q,
    certificates:cert.stats,path:'X5[1][4], expose7row2, [1], trim17; [4c-1], inherit entire14'};
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
  assert(at(r,z)>=2&&at(u,z)>=2&&at(v,z)>=2&&at(z,N)>=2);
  assert(N-1+3*D<=limits.width);
  P.prepare(s,r,2);s.fs(3);moveInitialization(s,r,2*D);
  const root={id:s.nextId++,level,kind:'ceiling',word:copy(B.infinity_FS(level+2)),points:[r,u,v,z],high:H,background:2};
  s.levels[level].root=root;s.levels[level].dict.set(JSON.stringify(root.word),root);
  P.trim(s,t+3*D);restore(s,root);
  s.trace.push({kind:'one-port-initial-layer',level,points:root.points.slice(),parent:parent.points.slice(),width:s.g.length});
  R.check(s,'one-port initial clone');
}
function initialize(columns=2,layers=2){
  assert(layers>=1&&layers<=12);
  const seedColumns=columns+(layers>1?1:0),s=makeSeed(seedColumns),level=layers-1;
  s.nextId=1;s.mode='one-port-paper-interface';s.levels=Array.from({length:layers},(_,l)=>({level:l,dict:new Map(),root:null}));
  s.rowRoot=copy(B.infinity_FS(level+2));s.J=[[],[[1,copy(s.rowRoot)],[1,B.ONE()]]];
  s.source=R.fs(s.J,seedColumns-1);
  s.root={id:0,level,kind:'ceiling',word:s.rowRoot,points:[7,11,12,13,14],high:10,background:2};
  s.levels[level].root=s.root;s.levels[level].dict.set(JSON.stringify(s.rowRoot),s.root);
  s.active=s.root;s.archive=14;s.K=15;s.slots=[];s.phase='cold';s.path=[];s.trace=[];
  R.check(s,'one-port pre-simulation seed');
  if(layers>1){
    R.prepareBudget(s,layers-1);for(let l=0;l<level;l++)cloneFromHighest(s,l);
    assert.equal(s.slots.length,0);s.packets.pop();P.trim(s,s.packets.at(-1).g3);
    s.source=R.fs(s.J,columns-1);s.phase='cold';restore(s);
  }
  s.root.points.splice(3,1);s.initializationTrace=s.trace.slice();s.trace=[];
  R.check(s,'one-port source initial state');return s;
}
module.exports={initialize,R,patches,originalSHA256};
if(require.main===module){
  let s,error=null;
  try{
    s=initialize(Number(process.argv[4]??2),Number(process.argv[2]??2));
    for(const n of (process.argv[3]??'0,0,0,1,0,0').split(',').filter(Boolean).map(Number))if(!R.step(s,n))break;
  }catch(e){error={message:e.message,stack:e.stack};process.exitCode=1;}
  console.log(JSON.stringify({status:error?'failed or guarded':'bounded one-port path passed',error,
    originalSHA256,interfacePatchCount:patches.length,...(s?R.report(s):{stats:R.stats,limits})},null,2));
}
