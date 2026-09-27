'use strict';

// Sparse ancestor-cover extra-copy resource engine, including one real parent
// return. This is NOT yet a persistent TBMS row-label dictionary compiler.
const assert = require('node:assert/strict');
const {L,values,noInsertionExpand} = require('./srpd-boundary-factorization.cjs');
const {loadTBM} = require('./load-tbm.cjs');
const {M} = require('../e0mn-y134258-hierarchical-20260920/ladder-cover.cjs');
const {createCertifier} = require('../e0mn-y13425810-20260920/finite-local-certificate.cjs');
const Cap = require('./finite-parent-capacity.cjs');
const started = Date.now(), loader = loadTBM(), B = loader.B;
const limits={ms:15000,rssMiB:650,width:500,events:3200,states:240,
  steps:22,restore:180,coldTemplates:40,nativeWidth:500};
const stats={events:0,states:0,native:0,nativeBSteps:0,steps:0,
  coldChecks:0,coldAncestorChecks:0,warmBudgetChecks:0,pairChecks:0,parentReturns:0,
  exposureDowns:0,nonemptyLogicalRootChecks:0,maxWidth:0,nativeSkipped:0};
function tick() {
  assert(Date.now()-started<limits.ms,'time guard');
  assert(process.memoryUsage().rss<limits.rssMiB*2**20,'RSS guard');
  assert(stats.events<=limits.events && stats.states<=limits.states,'event guard');
}
const sparse=g=>g.map(col=>col.flatMap((p,r)=>r===col.length-1||p!==col[r+1]
  ?[{a:p,x:[{exp:[],coeff:r+1}]}]:[]));
const cert=createCertifier(M,{tick,maxNodes:30000});
function native(g) {
  const expr=values(g).map(col=>col.map(v=>[v,[[]]]));
  const actual=Array.from(B.parents(expr,expr.map(B.column_verticals)),
    col=>Array.from(col,e=>e[0]+1));
  assert.deepEqual(actual,g,'native parent reconstruction');stats.native++;
}
function makeState() {
  let g=[[],[1],[2,2],[3,3,3],[2,2],[1]];
  function move(after,event) {
    tick();assert(after.length<=limits.width,'width guard');stats.events++;
    cert.certify({...event,before:sparse(g),after:sparse(after)});g=after;
    stats.maxWidth=Math.max(stats.maxWidth,g.length);
  }
  const fs=n=>move(L.expand(g,n),{kind:'FS',n});
  const truncate=h=>{
    assert(g.at(-1).length>=h,'truncate really shortens');
    if(g.at(-1).length!==h)
      move(g.slice(0,-1).concat([g.at(-1).slice(0,h)]),{kind:'truncate',height:h});
  };
  const down=()=>{
    const col=g.at(-1),h=col.length,c=col.at(-1);
    move(g.slice(0,-1).concat([col.slice(0,h-1).concat(g[c-1].slice(h-1))]),{kind:'down'});
  };
  function expose(c,h) {
    for(let i=0;i<limits.restore;i++) {
      truncate(h);assert(g.at(-1).at(-1)>=c,'expose cannot skip');
      if(g.at(-1).at(-1)===c)return;down();
    }
    throw Error('expose guard');
  }
  fs(1);fs(1);expose(7,3);fs(1);fs(0);fs(0);fs(2);expose(11,2);fs(1);
  fs(0);fs(0);fs(0);
  const logical=[[],Array(3).fill(1),Array(4).fill(2)];
  return {get g(){return g;},fs,truncate,down,
    logical,points:[7,10,15],archive:11,a:12,delta:1,
    cold:[{logical,points:[7,10,11]}],warm:{at:11,credit:1,calls:0,taxes:0,logical,points:[7,10,11]}};
}
function checkTemplate(g,logical,points) {
  assert.equal(logical.length,points.length);
  assert(logical.every(col=>col.length<=4),'finite logical resource height bound');
  assert(!logical[0].length,'logical first column really empty');
  if(g[points[0]-1].length)stats.nonemptyLogicalRootChecks++;
  const small=Cap.capacities(logical),actual=Cap.capacities(g);
  for(let j=0;j<points.length;j++) {
    assert(points[j]>=7 && points[j]<=g.length,'physical resource point domain');
    if(j)assert(points[j-1]<points[j],'strict sparse representative order');
    for(let p=0;p<j;p++) {
      const demand=3+Cap.at(small,p+1,j+1);
      assert(Cap.at(actual,points[p],points[j])>=demand,
        'complete sparse ancestor cover, including baseline-three nonedges');
      stats.pairChecks++;
    }
  }
}
function inspect(s) {
  tick();stats.states++;
  if(s.g.length<=limits.nativeWidth)native(s.g);else stats.nativeSkipped++;
  native(s.logical);
  const {g,a,archive,delta}=s;
  assert(g.length>a+2,'work is after private data');assert.equal(s.points.at(-1),g.length);
  assert(s.points.slice(0,-1).every(p=>p<archive),'all nonlast representatives precede archive');
  assert.equal(g[a-1].length,2);
  assert.deepEqual(g[a],Array(7).fill(a));
  assert.deepEqual(g[a+1],Array(a+1-delta).fill(a+1));
  assert(g[a+1].length>=archive,'weakened exact insertion credit K >= archive');
  
  assert.deepEqual(g.at(-1).slice(1),g[archive-1].slice(1),'archive tail match');
  checkTemplate(g,s.logical,s.points);
  const caps=Cap.capacities(g);
  assert(Cap.at(caps,archive,a)>=2,'active archive on second-row chain');
  assert.equal(Cap.at(caps,a,g.length),1,'work first row keeps private root, higher navigation bypasses it');
  assert(archive<=s.warm.at && s.warm.at<a,'warm ancestor stays above current archive');
  assert(Cap.at(caps,s.warm.at,a)>=2,'latest warm ancestor keeps second-row port');
  assert.equal(g[a+1].length-s.warm.at,s.warm.credit-s.warm.taxes,
    'only a real private-data tax spends warm-ancestor credit');
  checkTemplate(g,s.warm.logical,s.warm.points);
  assert.equal(s.warm.points.at(-1),s.warm.at);
  stats.warmBudgetChecks++;
  assert(s.cold.length<=limits.coldTemplates,'cold template count guard');
  for(const item of s.cold) {
    checkTemplate(g,item.logical,item.points);stats.coldChecks++;
    assert(Cap.at(caps,item.points.at(-1),a)>=1,'every old archive on first-row chain');
    stats.coldAncestorChecks++;
  }
}
function restore(s,archive) {
  for(let i=0;i<limits.restore;i++) {
    s.truncate(2);const p=s.g.at(-1)[1];
    assert(p>=archive,'second navigation cannot skip archive');
    s.down();if(p===archive)return;
  }
  throw Error('restore guard');
}
function expose(s,c,h) {
  for(let i=0;i<limits.restore;i++) {
    s.truncate(h);const p=s.g.at(-1).at(-1);
    assert(p>=c,'expose selected sparse ancestor cannot skip it');
    if(p===c)return;
    s.down();stats.exposureDowns++;
  }
  throw Error('sparse exposure guard');
}
function step(s,n,surplus=0) {
  inspect(s);stats.steps++;
  assert(Number.isSafeInteger(surplus)&&surplus>=0,'finite surplus-copy index');
  const old=s.logical,oldPoints=s.points,N=s.g.length,t=s.a+2;
  const child=noInsertionExpand(old,n);
  loader.context.expr=values(old).map(col=>col.map(v=>[v,[[]]]));loader.context.n=n;
  const expected=loader.run('B.TBM.FS(expr,n)',1000);
  assert.deepEqual(JSON.parse(JSON.stringify(expected)),
    values(child).map(col=>col.map(v=>[v,[[]]])),'native B step');stats.nativeBSteps++;
  if(!child.length) {s.fs(0);s.logical=[];s.points=[];native(s.g);return false;}
  let points,archive,newHelper;
  if(!n||!old.at(-1).length) {
    assert.equal(surplus,0,'surplus is only needed on a positive resource step');
    points=oldPoints.slice(0,-1);archive=points.at(-1);
    expose(s,archive,3);
    assert.equal(s.g.at(-1)[2],archive,'selected previous representative at row three');
    const span=N-archive;newHelper=t+span;
    s.fs(1);
  } else {
    let cut=old.at(-1).at(-1);
    const c=oldPoints[cut-1],span=N-c;points=oldPoints.slice();
    for(let i=0;i<n;i++) {
      const size=points.length-cut,last=points.at(-1);
      points=points.slice(0,-1).concat([last],points.slice(cut).map(p=>p+span));cut+=size;
    }
    points.pop();archive=points.at(-1);
    assert(c<s.warm.at);
    expose(s,c,old.at(-1).length+3);
    // The logical child uses exactly n blocks. Its full archive can remain
    // earlier than the private/main bank, which may use a later copy.
    const privateCopy=n+surplus;
    s.fs(privateCopy+1);s.a+=privateCopy*span;s.warm.at+=privateCopy*span;
    s.warm.points=s.warm.points.map(p=>p<c?p:p+privateCopy*span);
    newHelper=t+(privateCopy+1)*span;
  }
  while(s.g.length>newHelper)s.fs(0);
  assert.equal(s.g.length,newHelper);
  s.cold.push({logical:child,points:points.slice()});
  restore(s,archive);s.warm.calls++;
  points[points.length-1]=s.g.length;
  s.logical=child;s.points=points;s.archive=archive;
  inspect(s);return true;
}
function parentReturn(s) {
  inspect(s);
  const e=s.warm.at,t=s.a+2,K=s.g[t-1].length;
  assert(K>7 && K-1>=e,'return needs one tax and enough subsequent sparse insertion credit');
  while(s.g.length>t)s.fs(0);
  s.fs(2);s.delta++;s.warm.taxes++;stats.parentReturns++;
  assert.equal(s.g[t-1].length,K-1,'real private-data tax');
  restore(s,e);
  s.logical=s.warm.logical;
  s.archive=e;
  s.cold.push({logical:s.warm.logical,points:s.warm.points.slice()});
  s.points=s.warm.points.slice();
  s.points[s.points.length-1]=s.g.length;
  inspect(s);
}
function runRegression() {
 const protocols=[[1,1,1,1,1], [2,0,1,0,1], [0,1,1,0,1], [0,0,0], [1,0,2]];
 const runs=[];
 for(const path of protocols) {
  const s=makeState();inspect(s);
  step(s,1);
  const nonliteralBeforeReturn={
    warmPoints:s.warm.points.slice(),
    middleColumn:s.g[s.warm.points[1]-1],
    gammaOriginalMiddle:s.warm.logical[1],
    expectedDirectHighParent:s.warm.points[0]
  };
  assert.notDeepEqual(s.g[s.warm.points[1]-1].slice(3),
    s.warm.logical[1].map(p=>s.warm.points[p-1]),'exercise genuinely nonliteral warm template');
  parentReturn(s);
  assert.equal(s.g[s.a+1].length,s.archive,'exercise K=d, not old stronger K>d');
  const postReturn={width:s.g.length,privateRoot:s.a,privateHeight:s.g[s.a+1].length,
    archive:s.archive,points:s.points.slice()};
  let done=0,stop=null;
  for(const n of path.slice(0,limits.steps)) {
    const cut=s.logical.at(-1).at(-1),physical=cut?s.points[cut-1]:s.g.length-1;
    const child=noInsertionExpand(s.logical,n);
    const planned=!child.length?s.g.length-1:(!n||!s.logical.at(-1).length)
      ?2*s.g.length-s.points.at(-2)-1
      :s.g.length-1+(n+1)*(s.g.length-physical);
    if(planned>limits.width){stop='width guard';break;}
    const cont=step(s,n);done++;if(!cont)break;
  }
  runs.push({path,done,stop,nonliteralBeforeReturn,postReturn,width:s.g.length,
    logical:s.logical,archive:s.archive,privateHeight:s.g[s.a+1]?.length,
    warm:{points:s.warm.points,credit:s.warm.credit,taxes:s.warm.taxes,calls:s.warm.calls}});
 }
 console.log(JSON.stringify({scope:'one real parent return from nonliteral warm Gamma, then a sparse resource engine; no permanent free reuse claim',
  limits,stats,certificates:cert.stats,runs,elapsedMs:Date.now()-started,
  rssMiB:process.memoryUsage().rss/2**20},null,2));
}
module.exports={makeState,inspect,step,parentReturn,restore,stats,limits,cert,native,tick,
  noInsertionExpand};
if(require.main===module)runRegression();

