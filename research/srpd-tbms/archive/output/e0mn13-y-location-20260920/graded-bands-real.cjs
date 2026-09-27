'use strict';
// REAL M version of the graded protocol. No rule substitutions.
const assert=require('node:assert/strict'),G=require('./graded-bands.cjs');
const F=require('../e0mn-y1343-greedy-20260920/greedy-cover.cjs');
const S=require('./banded-source.cjs');
const {M,D,nat,expose,capacity}=F;
function check(s){
  const r=G.inspect(s.source,s.base,s.d),H=s.anchor+s.d+2;
  assert(s.anchor>=Math.max(0,...r.ps.map(p=>p.parents.length)));
  assert(M.debug.isLegalExpr(s.target));
  if(!s.source.size){assert.equal(s.target.length,s.floor||0);return r;}
  assert.equal(s.target.length,s.points.at(-1)+1);
  for(let j=0;j<r.ps.length;j++){
    const a=s.points[j],p=r.ps[j];assert(a>H);
    assert(capacity(s.target,s.anchor-1,a-1)>=1&&capacity(s.target,s.anchor-1,a)>=1);
    for(let u=0;u<p.parents.length;u++){
      const cap=capacity(s.target,s.points[p.parents[u]]-1,a-1);assert(cap>=u+1);
      if(r.owner[j]!==null){const h=r.ps[r.owner[j]].parents.length;
        if(u>=h)assert(cap>=s.anchor+1+u-h,`graded ${j},${u}`);}
    }
    if(!s.base[j]&&p.parents.length)assert(capacity(s.target,s.points[p.parents.at(-1)]-1,a-1)>=H,'body H');
    if(p.high!==null)assert(capacity(s.target,s.points[p.high]-1,a-1)>=H,'high H');
  }
  return r;
}
function initialize(n,emit=()=>{}){
  const source=D.encode(D.Y.fs(G.top,n)),d=n,height=d+4,w=source.size;
  const seed=M.FS(M.debug.parseExpr('()(1:ω)'),height);let target=M.FS(seed,2*w);
  emit({kind:'FS',before:seed,after:target,n:2*w});
  let anchor=1,points=Array.from({length:w},(_,j)=>height+2*j);
  const required=Math.max(0,...D.parents(source).map(p=>p.parents.length)),span=target.length-anchor;
  const pump=Math.max(0,Math.ceil((required-anchor)/span));
  // The extra final column controls this pump; all per-column auxiliaries are
  // retained inside the bad block. FS(0) also gives the unpumped representation.
  if(pump)target=expose(target,anchor-1,nat(1),emit);
  const before=target;target=M.FS(target,pump);emit({kind:'FS',before,after:target,n:pump});
  anchor+=pump*span;points=points.map(p=>p+pump*span);
  const s={source,d,base:S.mark(source),anchor,points,target,seed};
  check(s);return s;
}
function initializeFixed(n,emit=()=>{}){
  const source=D.encode(D.Y.fs(G.top,n)),d=n,w=source.size;
  const seed=M.FS(M.debug.parseExpr('()(1:ω)'),4);let target=M.FS(seed,2*w+1);
  emit({kind:'FS',before:seed,after:target,n:2*w+1});
  const fs=k=>{const before=target;target=M.FS(target,k);emit({kind:'FS',before,after:target,n:k});};
  const span=target.length-2,growth=Math.ceil(d/span),delta=growth*span;
  if(growth)target=expose(target,1,nat(1),emit);fs(growth);
  let anchor=1,points=Array.from({length:w},(_,j)=>4+2*j+delta);
  // One extra column remains beyond the last selected auxiliary.
  assert.equal(target.length,points.at(-1)+2);
  const span2=target.length-1,required=Math.max(0,...D.parents(source).map(p=>p.parents.length));
  const common=Math.max(0,Math.ceil((required-anchor)/span2)),delta2=common*span2;
  if(common)target=expose(target,0,nat(1),emit);fs(common);
  anchor+=delta2;points=points.map(p=>p+delta2);
  const s={source,d,base:S.mark(source),anchor,points,target,seed,
    initialization:{growth,common,Q:3+delta+delta2}};check(s);return s;
}
function step(s,n,emit=()=>{}){
  const {ps,owner}=check(s),w=s.source.size;if(!w)return s;
  const c=D.G.control(s.source),source=D.G.fs(s.source,n);
  assert.deepEqual(D.parents(source),G.expected(s.source,s.base,s.d,n));
  const base=S.nextMarks(s.source,s.base,n);
  let {target,anchor}=s,points=s.points.slice(),next=points.slice(0,-1),lastPump=0;
  const fs=k=>{const before=target;target=M.FS(target,k);emit({kind:'FS',before,after:target,n:k});};
  if(n&&c){
    if(c[0]){
      const required=Math.max(0,...D.parents(source).map(p=>p.parents.length)),span=target.length-anchor;
      const k=Math.max(0,Math.ceil((required-anchor)/span)),delta=k*span;lastPump=k;
      if(k)target=expose(target,anchor-1,nat(1),emit);fs(k);
      if(k){anchor+=delta;points=points.map(p=>p+delta);}next=points.slice(0,-1);
    }else fs(0);
    const row=ps.at(-1).parents.length-1,own=owner.at(-1);let threshold;
    if(c[0]||!s.base[w-1])threshold=anchor+s.d+2;
    else if(own!==null&&row>=ps[own].parents.length)threshold=anchor+1+row-ps[own].parents.length;
    else threshold=row+1;
    const cut=c[2];target=expose(target,points[cut]-1,nat(threshold),emit);
    const span=target.length-points[cut];fs(n);
    for(let b=1;b<=n;b++)for(let j=cut;j<w-1;j++)next.push(points[j]+b*span);
  }
  const width=next.length?next.at(-1)+1:(s.floor||0);while(target.length>width)fs(0);
  const out={...s,source,base,target,points:next,anchor,lastPump};check(out);assert(M.compare(target,s.target)<0);return out;
}
module.exports={...F,G,initialize,initializeFixed,check,step};
