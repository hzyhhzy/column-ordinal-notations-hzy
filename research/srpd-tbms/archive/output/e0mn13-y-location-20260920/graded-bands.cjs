'use strict';

// Finite-depth graded-band protocol; paper proof in
// Y13425712-GRADED-BAND-BOUND.zh-CN.md. Bounded tests remain diagnostics,
// not a replacement for its owner-transport and closure arguments.
const assert=require('node:assert/strict'),S=require('./banded-source.cjs');
const {D,rowAncestor,mark,nextMarks}=S;
const A=require('../e0mn-y1343-greedy-20260920/abstract-greedy.cjs');
const top=[1n,3n,4n,2n,5n,7n,12n];
function inspect(g,base,d){
  const ps=D.parents(g),roots=new Set(ps.filter(p=>p.high!==null).map(p=>p.high));
  const owner=Array(g.size).fill(null);assert.equal(base.length,g.size);
  for(const [,q] of g.atoms)assert(base[q],'genuine root marked');
  for(let t=0;t<g.size;t++){
    const p=ps[t];for(let r=1;r<p.parents.length;r++)assert.equal(ps[p.parents[r]].high,null,'upper parent not tip');
    if(p.high===null)continue;const c=p.high,h=ps[c].parents.length;
    assert(!base[t]&&base[c]);assert(p.parents.every(a=>a===c)&&p.parents.length===h+1,'uniform tip');
    for(let v=c+1;v<t;v++){
      if(!h)assert.equal(ps[v].high,c,'pure zero-star band');
      let a=v;while(a>c&&ps[a].high!==c&&ps[a].parents.length)a=ps[a].parents[0];
      assert(a>c&&ps[a].high===c,'band condition');
    }
    const zero=[];
    for(let j=t+1;j<g.size;j++)if(rowAncestor(ps,t,j,0)){
      if(!h)zero.push(j);
      if(rowAncestor(ps,c,j,h)){
        assert(!roots.has(j),'no live high root in another potential');
        if(base[j])assert(ps[j].parents.length<=h+d,'finite marked depth');
        assert(ps[j].parents.length<=h+d+1,'derived body height bound');
        assert(owner[j]===null||owner[j]===c,'unique potential owner');owner[j]=c;
      }
    }
    if(!h&&zero.length){assert.deepEqual(zero,[t+1]);assert(!base[t+1]);
      assert.deepEqual(ps[t+1],{parents:[t],high:null});}
  }
  for(let j=0;j<g.size;j++)if(ps[j].high!==null)assert.equal(owner[j],null,'a uniform tip has no other owner');
  return {ps,owner,roots};
}
function expected(g,base,d,n){
  const {ps}=inspect(g,base,d),x=g.size-1,ctrl=D.G.control(g);
  const out=ps.slice(0,x).map(p=>({parents:p.parents.slice(),high:p.high}));if(!n||!ctrl)return out;
  const high=!!ctrl[0],c=ctrl[2],span=x-c,h=ps[c].parents.length,row=ps[x].parents.length-1;
  for(let b=1;b<=n;b++)for(let j=c;j<x;j++){
    const move=p=>p<c?p:p+b*span,prev=p=>p<c?p:p+(b-1)*span;
    let p={parents:ps[j].parents.map(move),high:ps[j].high===null?null:move(ps[j].high)};
    if(high){
      if(j===c)p={parents:Array(h+b).fill(c+(b-1)*span),high:null};
      else if(rowAncestor(ps,c,j,h))p.parents=ps[j].parents.slice(0,h).map(move)
        .concat(Array(b+1).fill(move(ps[j].parents[h])),ps[j].parents.slice(h+1).map(move));
    }else if(j===c)for(let u=0;u<row;u++)p.parents[u]=prev(ps[x].parents[u]);
    out.push(p);
  }
  return out;
}
function pump(s,required,extraCloser=false){
  const span=s.pos.at(-1)+(extraCloser?1n:0n)-s.anchor,need=BigInt(required)-s.anchor;
  const n=need>0n?(need+span-1n)/span:0n,delta=n*span;if(!n)return {...s,lastPump:0n};
  return {...s,pos:s.pos.map(p=>p+delta),caps:s.caps.map(a=>a.map(q=>q>s.anchor?q+delta:q)),
    anchor:s.anchor+delta,reserve:s.reserve+delta,lastPump:n};
}
function check(s){
  const {ps,owner,roots}=inspect(s.source,s.base,s.d),H=s.anchor+BigInt(s.d+2);
  assert(s.anchor>=BigInt(Math.max(0,...ps.map(p=>p.parents.length))),'anchor above ordinary heights');
  if(!s.source.size){assert.equal(s.pos.length,0);return {ps,owner,roots};}
  assert.equal(s.pos.length,1+2*s.source.size);assert.equal(s.pos[0],s.anchor);
  for(let j=0;j<ps.length;j++){
    const a=1+2*j;assert(s.pos[a]>H);assert(s.caps[a][0]>=1n&&s.caps[a+1][0]>=1n);
    for(let r=0;r<ps[j].parents.length;r++){
      const cap=s.caps[a][1+2*ps[j].parents[r]];assert(cap>=BigInt(r+1),'literal ordinary coverage');
      if(owner[j]!==null){const h=ps[owner[j]].parents.length;
        if(r>=h)assert(cap>=s.anchor+1n+BigInt(r-h),`graded coverage ${j},${r}`);}
    }
    if(!s.base[j]&&ps[j].parents.length)assert(s.caps[a][1+2*ps[j].parents.at(-1)]>=H,'body top H');
    if(ps[j].high!==null)assert(s.caps[a][1+2*ps[j].high]>=H,'high H');
  }
  return {ps,owner,roots};
}
function initialize(n){
  const values=D.Y.fs(top,n),d=n;let s={...A.initialize(values,d+4),d};
  // Initialization pumps at ONE EXTRA closing column. The representation's
  // own final auxiliary column must lie inside, not be the deleted controller.
  s=pump(s,Math.max(0,...D.parents(s.source).map(p=>p.parents.length)),true);check(s);return s;
}
function initializeFixed(n){
  const source=D.encode(D.Y.fs(top,n)),d=n,w=source.size;
  // D4[2w+1]: two extra columns after the representation's final auxiliary.
  // Pump at column 2, retain the last copy. One extra column survives.
  const z=BigInt(2*w+5),L=z-2n;
  const growth=(BigInt(d)+L-1n)/L,delta=growth*L;
  const z1=z-1n+delta,required=BigInt(Math.max(0,...D.parents(source).map(p=>p.parents.length)));
  const common=(required-1n+z1-2n)/(z1-1n),delta2=common*(z1-1n);
  const anchor=1n+delta2,Q=3n+delta+delta2;
  const pos=[anchor];for(let j=0;j<w;j++){const p=4n+2n*BigInt(j)+delta+delta2;pos.push(p,p+1n);}
  const caps=pos.map((_,j)=>Array.from({length:j},(_,p)=>p===0?1n:Q));
  const s={source,d,base:mark(source),anchor,reserve:anchor+1n,pos,caps,
    initialization:{growth,common,Q}};check(s);return s;
}
function step(s,n){
  const {ps,owner}=check(s),w=s.source.size;if(!w)return s;
  const ctrl=D.G.control(s.source),source=D.G.fs(s.source,n),base=nextMarks(s.source,s.base,n);
  assert.deepEqual(D.parents(source),expected(s.source,s.base,s.d,n),'independent general high/ordinary formula');
  if(!n||!ctrl){const width=w>1?s.pos.length-2:0;
    const t={...s,source,base,pos:s.pos.slice(0,width),caps:s.caps.slice(0,width),lastPump:0n};check(t);return t;}
  let t=s;if(ctrl[0])t=pump(t,Math.max(0,...D.parents(source).map(p=>p.parents.length)));
  t={...t,pos:t.pos.slice(0,-1),caps:t.caps.slice(0,-1).map(a=>a.slice())};
  const row=ps[w-1].parents.length-1,own=owner[w-1];let threshold;
  if(ctrl[0]||!s.base[w-1])threshold=t.anchor+BigInt(s.d+2);
  else if(own!==null&&row>=ps[own].parents.length)threshold=t.anchor+1n+BigInt(row-ps[own].parents.length);
  else threshold=BigInt(row+1);
  const cut=1+2*ctrl[2];assert(t.caps.at(-1)[cut]>=threshold,'required controller');
  t=A.copy(t,cut,n,threshold);t.source=source;t.base=base;check(t);return t;
}
module.exports={D,A,top,inspect,expected,initialize,initializeFixed,check,step,pump};
