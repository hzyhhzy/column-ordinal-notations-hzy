'use strict';

// A storage adapter, using the existing ordinary e0MN run-length expander.
// No changes to native FS. Down/truncation are already proved reachable macros.
const assert=require('node:assert/strict');
const {M,nat}=require('../e0mn-y134258-hierarchical-20260920/ladder-cover.cjs');
const C=require('./finite-parent-capacity.cjs');
const {L}=require('./srpd-boundary-factorization.cjs');
const compress=g=>g.map(col=>col.flatMap((p,r)=>r===col.length-1||p!==col[r+1]
  ?[{a:p,x:nat(r+1)}]:[]));
const height=col=>col.at(-1)?.x[0]?.coeff??0;
function parent(col,r) {
  if(r<0||r>=height(col))return undefined;
  return col.find(e=>e.x[0].coeff>r)?.a;
}
const materialize=raw=>raw.map(col=>Array.from({length:height(col)},(_,r)=>parent(col,r)));
function full(g,index,p,h,label) {
  if(!g.rle)assert.deepEqual(g[index],Array(h).fill(p),label);
  else {
    const col=g.rle[index];
    assert.equal(height(col),h,label);
    assert(col.every(e=>e.a===p),label);
  }
}
function capacities(g) {
  if(!g.rle)return C.capacities(g);
  const raw=g.rle,cache=new Map();
  return {query(p,j) {
    if(p<1||p>=j)return 0;
    let row=cache.get(p);
    if(!row) {
      row=new Float64Array(raw.length+1);row[p]=Infinity;
      for(let v=p+1;v<=raw.length;v++)for(const e of raw[v-1])
        row[v]=Math.max(row[v],Math.min(e.x[0].coeff,row[e.a]));
      cache.set(p,row);
    }
    return row[j]??0;
  }};
}
const at=(q,p,j)=>q.query?q.query(p,j):C.at(q,p,j);
function attach(s,P,limits) {
  let raw=compress(s.g);
  const stats={nativeFS:0,zeroSteps:0,downMacroEndpoints:0,truncationMacroEndpoints:0,
    smallListDifferentials:0,smallCapDifferentials:0,maxSegments:0,maxWidth:raw.length};
  const columnViews=new WeakMap();
  function columnView(col) {
    let view=columnViews.get(col);if(view)return view;
    view=new Proxy({}, {get(_,key) {
      const h=height(col);
      if(key==='length')return h;
      if(key==='at')return i=>parent(col,i<0?h+i:i);
      if(key==='slice')return (start=0,end=h)=>Array.from({length:Math.max(0,end-start)},(_,r)=>parent(col,start+r));
      if(typeof key==='string'&&/^\d+$/.test(key))return parent(col,Number(key));
      return undefined;
    }});
    columnViews.set(col,view);return view;
  }
  const view=new Proxy({}, {get(_,key) {
    if(key==='length')return raw.length;
    if(key==='rle')return raw;
    if(key==='at')return i=>columnView(raw[i<0?raw.length+i:i]);
    if(typeof key==='string'&&/^\d+$/.test(key))return columnView(raw[Number(key)]);
    return undefined;
  }});
  function tick() {
    P.tick();
    assert(raw.length<=limits.width,'sparse native width guard');
    assert(stats.nativeFS+stats.zeroSteps+stats.downMacroEndpoints+stats.truncationMacroEndpoints<=limits.events,
      'sparse native event guard');
  }
  function validate() {
    tick();let segments=0;
    for(let j=0;j<raw.length;j++) {
      const col=raw[j],h=height(col);segments+=col.length;
      for(let k=0;k<col.length;k++) {
        const e=col[k];assert(e.x.length===1&&!e.x[0].exp.length);
        assert(e.a>=h&&e.a<j+1,'strict finite native domain');
        assert(!k||(e.a<=col[k-1].a&&e.x[0].coeff>col[k-1].x[0].coeff));
      }
    }
    assert(segments<=500000,'sparse native segment guard');
    stats.maxSegments=Math.max(stats.maxSegments,segments);
    stats.maxWidth=Math.max(stats.maxWidth,raw.length);
    if(raw.length<=90) {
      const dense=materialize(raw),a=C.capacities(dense),b=capacities(view);
      for(let j=2;j<=raw.length;j++)for(let p=1;p<j;p++)
        assert.equal(at(b,p,j),C.at(a,p,j),'sparse capacity differential');
      stats.smallCapDifferentials++;
    }
  }
  Object.defineProperty(s,'g',{get:()=>view,configurable:true});
  s.fs=n=> {
    tick();
    if(!n||!height(raw.at(-1)??[])) {
      // Native predecessor is exactly this prefix; omit only deep cloning.
      raw=raw.slice(0,-1);stats.zeroSteps++;return;
    }
    const N=raw.length,c=raw.at(-1).at(-1).a;
    assert(N-1+n*(N-c)<=limits.width,'sparse native FS preallocation');
    const before=N<=90?materialize(raw):null;
    raw=M.FS(raw,n);stats.nativeFS++;
    if(before&&raw.length<=300) {
      assert.deepEqual(materialize(raw),L.expand(before,n),'native sparse/list FS differential');
      stats.smallListDifferentials++;
    }
    validate();
  };
  s.down=()=> {
    tick();assert(height(raw.at(-1))>0);
    const N=raw.length,before=N<=90?materialize(raw):null;
    raw=M.debug.down(raw);stats.downMacroEndpoints++;
    if(before) {
      assert.deepEqual(materialize(raw),L.expand(before,1).slice(0,N),'native down is FS1 then zero steps');
      stats.smallListDifferentials++;
    }
    validate();
  };
  s.truncate=h=> {
    tick();const col=raw.at(-1),H=height(col);
    assert(h>=1&&h<=H,'sparse truncation only lowers');
    if(h===H)return;
    const prefix=col.filter(e=>e.x[0].coeff<h),p=parent(col,h-1);
    raw=raw.slice(0,-1).concat([prefix.concat([{a:p,x:nat(h)}])]);
    stats.truncationMacroEndpoints++;validate();
  };
  s.sparseStats=stats;s.validateSparse=validate;
  validate();return s;
}
module.exports={attach,capacities,at,full,materialize};
