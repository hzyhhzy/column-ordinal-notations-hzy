'use strict';

// All finite layer counts share this actual pre-coupon state.
const assert=require('node:assert/strict');
const F=require('./weak-archive-row-bank.cjs'),R=F.R,P=R.P;
const S=require('../m13-lists-20260926/SRPD.ne-rewritten.js');
const dense=s=>Array.from({length:s.g.length},(_,j)=>Array.from(s.g[j]));
const s=F.makeSeed(3),Q=s.seedAudit.commonSeed;
const z=s.packets.at(-1).g2,K=s.K;P.trim(s,z);
let topDowns=0,cut;
for(let i=0;i<100;i++){
  s.truncate(K);cut=s.g.at(-1).at(-1);
  if(s.g[cut-1].length<K)break;
  s.down();topDowns++;assert(i+1<100,'weak archive gate navigation guard');
}
const gate=dense(s);
assert.equal(z,26);assert.equal(cut,16);assert.equal(K,15);
assert.deepEqual(gate.at(-1),Array(14).fill(25).concat(16));
const tests=[];
for(const coupons of [1,2,5,11]){
  const actual=F.initialize(3,1);R.prepareBudget(actual,coupons);
  const expected=S.expand(gate,coupons+1);expected[expected.length-1]=expected[13].slice();
  assert.deepEqual(dense(actual),expected);
  tests.push({coupons,index:coupons+1,width:expected.length,slots:actual.slots.length});
}
console.log(JSON.stringify({status:'weak archive fixed pre-coupon gate verified on four budgets',finiteTestsOnly:true,
  QCounts:S.counts(Q),gateCounts:S.counts(gate),graph:gate,cut,K,z,topDowns,tests,
  seedCertificates:s.seedAudit.certificates,rssMiB:process.memoryUsage().rss/2**20},null,2));
