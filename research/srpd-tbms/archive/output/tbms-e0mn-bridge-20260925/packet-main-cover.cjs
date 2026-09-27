'use strict';

// Actual M column packets for the main ordinary/unit-copy interface.
// This is NOT an arbitrary-order transfinite row-label dictionary.
const assert=require('node:assert/strict');
const E=require('./crossing-lower-sparse-parent-return.cjs');
const C=require('./finite-parent-capacity.cjs');
const {L,noInsertionExpand,values}=require('./srpd-boundary-factorization.cjs');
const nativeMain=require('./load-tbm.cjs').loadTBM();
const started=Date.now();
const limits={ms:14000,rssMiB:650,width:420,events:8000,pairs:100000,
  navigation:160,logicalWidth:35,steps:150,nativeWidth:90,downTransientWidth:840};
Object.assign(E.limits,{ms:limits.ms,width:limits.width,events:limits.events,states:1000,
  nativeWidth:limits.nativeWidth});
const audit={mode:process.argv.includes('--count-truncations')
  ?'counted reachable-macro certificates':'proved truncation endpoints; native FS/down endpoints',
  nativePhysicalParentsThroughWidth:limits.nativeWidth,
  allWidthChecks:'all pair capacities, main endpoints, guards, and resource contracts',
  initialEngineCountersOnly:!process.argv.includes('--count-truncations')};
const stats={mainSteps:0,resourceSteps:0,pairs:0,packetChecks:0,
  workReloads:0,privatePorts:0,deletedColumns:0,spareReturns:0,
  literalFS:0,literalDowns:0,truncateMacroEndpoints:0,maxPhysicalWidth:0,
  topParentChecks:0,spareTopDowns:0,spareHelperPorts:0,nativeMainSteps:0};
function tick(){
  E.tick();assert(Date.now()-started<limits.ms,'packet time guard');
  assert(process.memoryUsage().rss<limits.rssMiB*2**20,'packet RSS guard');
  assert(stats.pairs<=limits.pairs&&stats.mainSteps<=limits.steps,'packet operation guard');
  assert(stats.literalFS+stats.literalDowns+stats.truncateMacroEndpoints<=limits.events,
    'packet source-event guard');
}
function prepare(s,c,h,inherit=false){
  for(let i=0;i<limits.navigation;i++){
    s.truncate(h);
    const p=s.g.at(-1).at(-1);assert(p>=c,'selected ancestor cannot be skipped');
    if(p===c){if(inherit)s.down();return;}
    s.down();
  }
  throw Error('packet navigation guard');
}
function trim(s,end){
  assert(end>=1&&end<=s.g.length);
  while(s.g.length>end){s.fs(0);stats.deletedColumns++;}
}
function sourceState(){
  const original=E.makeState();
  stats.maxPhysicalWidth=Math.max(stats.maxPhysicalWidth,original.g.length);
  if(process.argv.includes('--count-truncations'))return original;
  let g=original.g;
  return {...original,get g(){return g;},
    fs(n){
      tick();
      const h=g.at(-1)?.length,c=g.at(-1)?.at(-1);
      const width=n&&h?g.length-1+n*(g.length-c):Math.max(0,g.length-1);
      assert(width<=limits.width,'literal FS preallocation guard');
      g=L.expand(g,n,tick);stats.literalFS++;
      stats.maxPhysicalWidth=Math.max(stats.maxPhysicalWidth,g.length);
    },
    down(){
      tick();const N=g.length,h=g.at(-1).length,c=g.at(-1).at(-1);
      assert(h>0&&N-1+(N-c)<=limits.downTransientWidth,'down transient width guard');
      const expanded=L.expand(g,1,tick);
      stats.maxPhysicalWidth=Math.max(stats.maxPhysicalWidth,expanded.length);
      const actual=expanded.slice(0,N);
      assert.deepEqual(actual,g.slice(0,-1).concat([
        g.at(-1).slice(0,h-1).concat(g[c-1].slice(h-1))
      ]));
      g=actual;stats.literalDowns++;
    },
    truncate(h){
      tick();assert(h>=1&&g.at(-1).length>=h,'true truncation only');
      if(g.at(-1).length===h)return;
      // Endpoint of the separately proved finite reachable truncation macro.
      // No exact enormous iteration count is computed in this test mode.
      g=g.slice(0,-1).concat([g.at(-1).slice(0,h)]);
      stats.truncateMacroEndpoints++;
    }};
}
function setup(){
  const s=sourceState();
  trim(s,14);s.fs(7); // the real height12 controller creates seven height11 columns.
  assert.equal(s.g.length,20);
  s.delta=2;
  s.logical=[[],Array(3).fill(1)];
  s.archive=10;
  s.warm={at:10,logical:s.logical.map(c=>c.slice()),points:[7,10],
    credit:1,taxes:0,calls:0};
  s.points=[7,s.g.length];
  s.main=[[],Array(4).fill(1)];
  s.codes=[7,8,9,10,11];
  s.packets=[{point:13,g1:14,g2:15,g3:16},{point:17,g1:18,g2:19,g3:20}];
  s.taxed=false;
  restoreResource(s);inspect(s);
  return s;
}
function restoreResource(s){
  E.restore(s,s.archive);
  s.points[s.points.length-1]=s.g.length;
}
function reloadWork(s){
  const last=s.packets.at(-1);
  prepare(s,last.g1,1,true);
  assert.deepEqual(s.g.at(-1),Array(s.codes.at(-1)).fill(last.point),
    'reloaded full-code work is a child of the actual current logical point');
  stats.workReloads++;
}
function inspect(s,resource=true){
  tick();if(resource)E.inspect(s);
  stats.maxPhysicalWidth=Math.max(stats.maxPhysicalWidth,s.g.length);
  assert.equal(s.main.length,s.packets.length);
  assert.equal(s.packets[0].point,s.a+1,'the first logical point is the private unit root');
  assert(s.main.length<=limits.logicalWidth&&s.g.length<=limits.width);
  assert.equal(s.codes[0],7);
  assert(s.codes.every((q,i)=>!i||q>s.codes[i-1]));
  const K=s.codes.at(-1),q=C.capacities(s.g),small=C.capacities(s.main);
  const packetNodes=new Set(s.packets.flatMap(p=>Object.values(p).filter(Number.isInteger)));
  assert.equal(K,s.g[s.a+1].length,'private master code agrees');
  assert(K<=s.a);
  for(let i=0;i<s.packets.length;i++){
    const p=s.packets[i],last=i===s.packets.length-1;
    assert.equal(p.g1,p.point+1);assert.equal(p.g2,p.point+2);
    if(p.g3!==null)assert.equal(p.g3,p.point+3);
    if(i)assert(s.packets[i-1].g2<p.point);
    assert.deepEqual(s.g[p.g1-1],Array(K).fill(p.point),'first full-code guard');
    if(!last||!s.taxed)
      assert.deepEqual(s.g[p.g2-1],Array(K).fill(p.g1),'second full-code guard');
    if(!last)assert.deepEqual(s.g[p.g3-1],Array(K).fill(p.g2),'nonlast work template');
    assert(C.at(q,s.a,p.point)>=2,'logical point keeps the private low port');
    assert(C.at(q,s.warm.at,p.g1)>=2,'warm parent low port to full-code guard');
    assert(s.g[p.point-1].length<=K,'main point stays below the global code');
    if(s.g[p.point-1].length===K){
      assert(packetNodes.has(s.g[p.point-1][K-1]),'top-row main ancestry stays in packet nodes');
      stats.topParentChecks++;
    }
    stats.privatePorts+=2;stats.packetChecks++;
    for(let j=0;j<i;j++){
      const wanted=C.at(small,j+1,i+1),actual=C.at(q,s.packets[j].point,p.point);
      if(wanted)assert.equal(actual,s.codes[wanted],'exact positive endpoint');
      else assert(actual<=7,'nonedges stay below the encoded positive rows');
      stats.pairs++;
    }
  }
  assert(C.at(q,s.packets.at(-1).g1,s.g.length)>=1,'first-row access to the live guard');
}
function mainStep(s,n){
  inspect(s);assert(Number.isSafeInteger(n)&&n>=0);
  const source=s.main,old=s.packets.map(p=>({...p}));
  const h=source.at(-1).length;
  const predicted=n&&h?source.length-1+n*(source.length-source.at(-1).at(-1))
    :source.length-1;
  assert(predicted<=limits.logicalWidth,'logical main preallocation guard');
  const next=noInsertionExpand(source,n);
  nativeMain.context.expr=values(source).map(col=>col.map(v=>[v,[[]]]));
  nativeMain.context.n=n;
  const actual=nativeMain.run('B.TBM.FS(expr,n)',1000);
  assert.deepEqual(JSON.parse(JSON.stringify(actual)),
    values(next).map(col=>col.map(v=>[v,[[]]])),'native finite-main fundamental sequence');
  stats.nativeMainSteps++;
  if(!next.length){
    s.fs(0);s.main=[];s.packets=[];stats.mainSteps++;return false;
  }
  if(!n||!h){
    trim(s,old.at(-2).g3);
    s.packets=old.slice(0,-1);
  }else{
    reloadWork(s);
    const cut=source.at(-1).at(-1),c=old[cut-1].point;
    // Endpoint codes may have gaps: expose code(predecessor)+1, not code(h).
    const row=s.codes[h-1]+1;
    prepare(s,c,row);
    const N=s.g.length,D=N-c;
    assert(N-1+n*D<=limits.width,'main preallocation guard');
    s.fs(n);
    const packets=old.slice(0,-1);
    for(let i=1;i<=n;i++)for(let j=cut-1;j<old.length-1;j++){
      const p=old[j],shift=i*D;
      packets.push({point:p.point+shift,g1:p.g1+shift,
        g2:p.g2+shift,g3:p.g3+shift});
    }
    s.packets=packets;
    trim(s,packets.at(-1).g3);
  }
  s.main=next;s.taxed=false;
  restoreResource(s);stats.mainSteps++;
  inspect(s);return true;
}
function resourceStep(s,n,surplus=0){
  inspect(s);
  const old=s.logical,N=s.g.length,positive=n>0&&old.at(-1).length>0;
  const child=noInsertionExpand(old,n);
  assert(child.length,'this interface keeps a nonzero resource label');
  const c=positive?s.points[old.at(-1).at(-1)-1]:s.points.at(-2);
  const D=N-c;
  assert(Number.isSafeInteger(surplus)&&surplus>=0);
  assert(N-1+(positive?n+surplus+1:1)*D<=limits.width,'resource preallocation guard');
  E.step(s,n,surplus);
  if(positive){
    const shift=(n+surplus)*D;
    s.codes=s.codes.map(q=>q>c?q+shift:q);
    s.packets=s.packets.map(p=>Object.fromEntries(Object.entries(p).map(
      ([k,v])=>[k,v>=c?v+shift:v])));
  }
  stats.resourceSteps++;inspect(s);
}
function recallParent(s){
  inspect(s);assert(!s.taxed,'one spare payment per current logical packet');
  const warm={at:s.warm.at,logical:s.warm.logical.map(c=>c.slice()),
    points:s.warm.points.slice()};
  const e=warm.at,K=s.codes.at(-1),spare=s.packets.at(-1).g2;
  assert.equal(K,e+1,'tight global parent envelope');
  trim(s,spare);
  for(let i=0;i<limits.navigation;i++){
    s.truncate(K);
    const c=s.g.at(-1).at(-1);
    if(s.g[c-1].length<K)break;
    s.down();stats.spareTopDowns++;
    assert(i+1<limits.navigation,'top-parent navigation guard');
  }
  s.truncate(K);
  const cut=s.g.at(-1).at(-1);
  assert(cut>=s.a+1&&K<=cut);
  assert(spare-1+3*(spare-cut)<=limits.width,'spare preallocation guard');
  const cap=C.capacities(s.g);
  assert(C.at(cap,e,spare)>=2,'same selected warm domain');
  s.fs(3);trim(s,spare+2);
  const helpers=C.capacities(s.g);
  assert(C.at(helpers,e,spare+1)>=2&&C.at(helpers,e,spare+2)>=2,
    'actual copied helper low ports');
  stats.spareHelperPorts+=2;
  prepare(s,e,2);
  const N=s.g.length,D=N-e;
  assert(N-1+D<=limits.width,'gap preallocation guard');
  s.fs(1);
  const shift=p=>p>=e?p+D:p;
  s.a=shift(s.a);
  s.codes=s.codes.map(q=>q>e?q+D:q);
  s.packets=s.packets.map(p=>Object.fromEntries(Object.entries(p).map(
    ([k,v])=>[k,typeof v==='number'?shift(v):v])));
  s.packets.at(-1).g3=null; // its old work column was truly deleted before payment.
  s.taxed=true;
  const parentPoints=warm.points.map(shift);
  s.archive=e+D;s.logical=warm.logical;
  s.warm={at:s.archive,logical:warm.logical,points:parentPoints,
    credit:1,taxes:0,calls:0};
  s.points=parentPoints.slice(0,-1).concat(s.g.length);
  s.cold.push({logical:warm.logical,points:parentPoints.slice()});
  restoreResource(s);stats.spareReturns++;
  inspect(s);
}
module.exports={setup,inspect,mainStep,resourceStep,reloadWork,restoreResource,
  prepare,trim,recallParent,tick,limits,stats,audit,E};
