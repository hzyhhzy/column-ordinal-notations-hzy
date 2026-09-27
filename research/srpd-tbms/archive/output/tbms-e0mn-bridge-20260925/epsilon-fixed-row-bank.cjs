'use strict';

// The ROW LABEL epsilon_0 is ordinary BMS ()(1,1), a finite two-row matrix.
// It needs a fixed full-cover bank, not an internally amplifiable ceiling.
// Reuse the proved finite-bank and main-source operations unchanged.
const assert=require('node:assert/strict'),fs=require('node:fs');
const path=require('node:path'),Module=require('node:module'),crypto=require('node:crypto');
const Old=require('./one-port-recursive-row-bank.cjs');
const Trimmed=require('./trimmed-one-port-row-bank.cjs');
const originalPath=path.join(__dirname,'packet-recursive-row-bank-cover.cjs');
let source=fs.readFileSync(originalPath,'utf8');
const originalSHA256=crypto.createHash('sha256').update(source).digest('hex'),patches=[];
function replace(before,after,count=1){assert.equal(source.split(before).length-1,count,'finite top-bank patch: '+before);
  source=source.split(before).join(after);patches.push({before,after,count});}
for(const p of Old.patches)replace(p.before,p.after,p.count);
replace('if(eq(upper,s.levels[level].root.word)){',
  "if(s.levels[level].root.kind==='ceiling'&&eq(upper,s.levels[level].root.word)){");
const generatedPath=path.join(__dirname,'epsilon-fixed-row-bank.generated.cjs');
const runtime=new Module(generatedPath,module);runtime.filename=generatedPath;runtime.paths=module.paths;
runtime._compile(source,generatedPath);
const R=runtime.exports,Initial=require('./packet-amplified-resource-cover.cjs');
const S=require('../m13-lists-20260926/SRPD.ne-rewritten.js');
const {createCertifier}=require('../e0mn-y13425810-20260920/finite-local-certificate.cjs');
const {P,Sparse,B,limits}=R,started=Date.now(),copy=x=>JSON.parse(JSON.stringify(x));
Object.assign(limits,{width:160000,downTransientWidth:320000});
Object.assign(P.limits,limits);Object.assign(P.E.limits,limits);
const epsilon=copy(B.from_display('()(1,1)'));
const E=copy(B.from_display('()(1^()(1,1))'));
const J=copy(B.from_display('()(1^()(1,1),1)'));
function tick(){P.tick();assert(Date.now()-started<20000,'epsilon fixed-bank time guard');
  assert(process.memoryUsage().rss<650*2**20,'epsilon fixed-bank RSS guard');}
function makeSeed(columns){
  const previous=Trimmed.makeSeed(1).seedAudit;
  let g=previous.commonSeed.map(c=>c.slice()),events=0;const stages=[];
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
  P.trim(s,11);s.truncate(5);stage('five-row working pair before creating permanent four-row bank');
  s.fs(2);stage('four-row permanent bank plus working copy');
  P.prepare(s,7,2);s.fs(1);P.trim(s,14);
  const Q=g.map(c=>c.slice()),commonCounts=S.counts(Q);
  assert.deepEqual(Q,[[],[1],[2,2],[3,3,3],[2,2],[],[6],Array(7).fill(7),Array(8).fill(8),
    [7,7],Array(4).fill(10),[11],Array(7).fill(12),Array(13).fill(13)]);
  const cap=Sparse.capacities(Q);assert.equal(Sparse.at(cap,10,11),4);
  s.fs(4*columns-1);assert.equal(g.length,12+4*columns);
  s.a=12;s.K=12;s.codes=[7,12];s.taxed=false;s.archive=11;
  s.packets=Array.from({length:columns},(_,i)=>({point:13+4*i,g1:14+4*i,g2:15+4*i,g3:16+4*i}));
  P.prepare(s,11,1,true);
  s.seedAudit={r:7,background:2,columns,events,port:1,finiteTop:true,
    commonCounts,commonSeed:Q,previousCounts:previous.commonCounts,stages,certificates:cert.stats,
    pair:[10,11],capacity:4,requiredCapacity:2+2,
    path:'Qtrim, trim11, truncate5, [2], expose7row2, [1], trim14; [4c-1], inherit entire11'};
  Sparse.attach(s,P,limits);return s;
}
function initialize(columns=2){
  assert(columns>=1&&columns<=20);
  const s=makeSeed(columns);s.nextId=1;s.mode='epsilon-finite-top-bank';
  s.rowRoot=copy(epsilon);s.J=copy(J);s.source=R.fs(J,columns-1);
  if(columns===2)assert(R.eq(s.source,E),'source is exactly TBMS ()(1^epsilon_0)');
  s.root={id:0,level:0,word:copy(epsilon),points:[10,11],graph:R.rowGraph(epsilon)};
  s.levels=[{level:0,dict:new Map([[R.key(epsilon),s.root]]),root:s.root}];
  s.active=s.root;s.archive=11;s.slots=[];s.phase='cold';s.path=[];s.trace=[];s.initializationTrace=[];
  R.check(s,'finite epsilon top-bank initialization');return s;
}
module.exports={initialize,makeSeed,R,patches,originalSHA256,epsilon,E,J};
