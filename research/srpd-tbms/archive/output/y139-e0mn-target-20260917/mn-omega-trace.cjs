'use strict';
// Research-only local counting/unranking for normal e0MN rows <= omega.
// All auxiliary parent-column trajectories use the same last-column index m.
const assert = require('node:assert/strict');
const {M} = require('../rpd-to-e0mn-20260917/probe.cjs');
const nat = n => n ? [{exp:[],coeff:n}] : [];
const omega = [{exp:nat(1),coeff:1}];
function isOmega(a) { return a.length===1&&a[0].coeff===1&&a[0].exp.length===1&&
  a[0].exp[0].coeff===1&&!a[0].exp[0].exp.length; }
function rank(a,m) {
  if(isOmega(a))return m+1;
  assert(a.length===1&&!a[0].exp.length&&a[0].coeff<=m,'normal positive finite row');
  return a[0].coeff;
}
function skyline(col) {
  const best=new Map();
  for(const [p,u] of col)if(!best.has(p)||best.get(p)<u)best.set(p,u);
  const result=[];let high=0;
  for(const [p,u] of [...best].sort((a,b)=>b[0]-a[0]))if(u>high){result.push([p,u]);high=u;}
  return result;
}
function model(h,tick=()=>{}) {
  assert(h.length>0);const m=h.length-1;
  const columns=h.map(c=>c.map(e=>[e.a-1,rank(e.x,m)])),traces=[];
  for(let p=0;p<=m;p++) {
    let current=columns[p],steps=0n;const trace=[];
    for(;;) {
      tick();const edge=current.at(-1),top=edge?.[1]??0;
      if(trace.length)assert(trace.at(-1).top>top);
      const entry={top,steps,column:current};trace.push(entry);
      if(!edge)break;
      const [parent,u]=edge,lower=current.slice(0,-1);
      if(u>1)lower.push([parent,u-1]);
      const source=traces[parent];let lo=0,hi=source.length-1;
      while(lo<hi){tick();const mid=(lo+hi)>>1;if(source[mid].top>=u)lo=mid+1;else hi=mid;}
      entry.parent=parent;entry.lower=lower;
      current=skyline([...lower,...source[lo].column]);steps+=1n+source[lo].steps;
    }
    traces.push(trace);
  }
  function at(p,d) {
    tick();const trace=traces[p];assert(d>=0n&&d<=trace.at(-1).steps);
    let lo=0,hi=trace.length-1;
    while(lo<hi){const mid=(lo+hi+1)>>1;if(trace[mid].steps<=d)lo=mid;else hi=mid-1;}
    const entry=trace[lo];
    if(entry.steps===d)return entry.column;
    return skyline([...entry.lower,...at(entry.parent,d-entry.steps-1n)]);
  }
  return {count:traces[m].at(-1).steps+1n,traces,
    columnAtStep:d=>at(m,d).map(([p,u])=>({a:p+1,x:u===m+1?omega:nat(u)}))};
}
module.exports={M,nat,omega,isOmega,model};
