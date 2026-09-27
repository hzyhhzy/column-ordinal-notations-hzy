'use strict';
const assert=require('node:assert/strict');
const F=require('./one-port-recursive-row-bank.cjs'),X=F.R;
const cases=[
  {name:'one layer ordinary refinements',levels:1,c:2,path:[2,2,1,0]},
  {name:'two layers through a main copy to empty',levels:2,c:2,path:[0,0,0,1,0,0],empty:true},
  {name:'retained high source across main copy',levels:2,c:3,path:[0,0,0,1]},
  {name:'high source reused after low main work',levels:2,c:3,path:[0,0,0,1,0,1]},
  {name:'nonzero recursive refinements',levels:2,c:2,path:[1,1,0]},
  {name:'three layers lower-code updates',levels:3,c:2,path:[0,0]},
  {name:'three layers nonzero first index',levels:3,c:2,path:[1,0]},
  {name:'five same-background layers',levels:5,c:2,path:[]},
  {name:'twelve same-background layers',levels:12,c:2,path:[]},
  {name:'larger native row matrices',levels:2,c:3,path:[2,2,1]},
  {name:'higher row copy then split',levels:2,c:3,path:[0,0,1,1,0]},
  {name:'four layers nonzero actual refinement',levels:4,c:2,path:[1,0]}
];
const id=process.argv[2]??'0';let s,error=null,strictHigherDemand=null,test;
try{
  if(id==='local'){
    test={name:'six paid local operations, no source steps',levels:2,c:1,path:[]};
    s=F.initialize(1,2);const sourceKey=X.key(s.source);X.prepareBudget(s,6);
    const h3=X.allocateCeiling(s,0,2),a=X.allocateStep(s,h3,2),h2=X.allocateStep(s,a,0);
    const higher=X.allocateCeiling(s,1,1);
    assert.equal(X.key(X.ends(higher.word).at(-1).at(-1)),X.key(h2.word));
    const b=X.allocateStep(s,a,1),before=X.grade(s,h2.word,0);X.allocateStep(s,b,1);
    const cut=s.trace.at(-1).cut,after=X.grade(s,h2.word,0);
    strictHigherDemand={before,after,cut,higherBank:higher.id};
    assert(before>cut&&after===before&&X.stats.strictSubcovariances>0);
    assert.equal(s.slots.length,0);assert.equal(X.key(s.source),sourceKey);assert.equal(X.stats.sourceSteps,0);
    X.check(s,'one-port paid local contract');
  }else{
    test=cases[Number(id)];assert(test);s=F.initialize(test.c,test.levels);
    for(const n of test.path)if(!X.step(s,n))break;
    if(test.empty)assert.equal(s.source.length,0);
  }
}catch(e){error={message:e.message,stack:e.stack};process.exitCode=1;}
console.log(JSON.stringify({caseIndex:id,test,finiteTestsOnly:true,proofDocument:'ONE-PORT-WHOLE-TBMS.zh-CN.md',
  status:error?'failed or guarded':'bounded one-port contract passed',error,strictHigherDemand,
  originalSHA256:F.originalSHA256,interfacePatches:F.patches,
  ...(s?X.report(s):{stats:X.stats,limits:X.limits})},null,2));
