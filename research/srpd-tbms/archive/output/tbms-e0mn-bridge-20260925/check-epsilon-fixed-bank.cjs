'use strict';
const assert=require('node:assert/strict');
const F=require('./epsilon-fixed-row-bank.cjs'),R=F.R;
const cases=[
  {name:'epsilon lowest branch terminates',columns:2,path:[0,0,0]},
  {name:'omega row then main copies',columns:2,path:[1,0,1,0,0]},
  {name:'two-level child terminates',columns:2,path:[2,0,0,1,0,0]},
  {name:'finite endpoint insertion',columns:2,path:[3,0,1,1]},
  {name:'coefficients and finite row matrices',columns:2,path:[2,1,1]},
  {name:'retained epsilon called at later higher index',columns:3,path:[1,0,1,4,0,0,0,0,1,6]},
  {name:'large first epsilon index',columns:2,path:[18]},
  {name:'four-column retained epsilon source',columns:4,path:[1,0,1,3]},
  {name:'deeper bounded finite prefix',columns:2,path:[3,0,1,1,1]},
  {name:'one-column initialization',columns:1,path:[]},
  {name:'five-column initialization',columns:5,path:[]},
  {name:'twelve-column initialization',columns:12,path:[]}
];
const id=Number(process.argv[2]??0),test=cases[id];assert(test);
let s,error=null;
try{
  s=F.initialize(test.columns);
  for(const n of test.path)if(!R.step(s,n))break;
  assert.equal(R.stats.ceilingAllocations??0,0,'finite top never replaced by an amplifier');
  assert(s.path.length===test.path.length||!s.source.length);
}catch(e){error={message:e.message,stack:e.stack};process.exitCode=1;}
console.log(JSON.stringify({caseIndex:id,test,finiteTestsOnly:true,
  status:error?'failed or guarded':'bounded finite-top epsilon case passed',error,
  originalSHA256:F.originalSHA256,interfacePatches:F.patches,
  ...(s?R.report(s):{stats:R.stats,limits:R.limits})},null,2));
