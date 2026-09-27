'use strict';

// Parametric standard Q_k below W[k]. This is a real native trace, not a
// free replacement of a finite graph by a shifted nonstandard picture.
const assert=require('node:assert/strict');
const {L}=require('./srpd-boundary-factorization.cjs');
const {createCertifier}=require('../e0mn-y13425810-20260920/finite-local-certificate.cjs');
function makeSeed(P,M,Sparse,limits,columns,height,tick) {
  const index=Math.max(1,Math.ceil((height+2)/5)),r=5*index+2;
  let g=[[],[1],[2,2],[3,3,3],[2,2],[1]],events=0;
  const compress=a=>a.map(col=>col.flatMap((p,j)=>j===col.length-1||p!==col[j+1]
    ?[{a:p,x:[{exp:[],coeff:j+1}]}]:[]));
  const cert=createCertifier(M,{tick,maxNodes:40000});
  function move(after,event) {
    tick();assert(after.length<=limits.width&&++events<=500,'parametric seed guard');
    cert.certify({...event,before:compress(g),after:compress(after)});g=after;
  }
  const s={get g(){return g;},
    fs(n){move(L.expand(g,n),{kind:'FS',n});},
    truncate(h){assert(h>=1&&h<=g.at(-1).length);
      if(h!==g.at(-1).length)move(g.slice(0,-1).concat([g.at(-1).slice(0,h)]),{kind:'truncate',height:h});},
    down(){const c=g.at(-1),h=c.length,p=c.at(-1);assert(h>0);
      move(g.slice(0,-1).concat([c.slice(0,h-1).concat(g[p-1].slice(h-1))]),{kind:'down'});}
  };
  s.fs(index);s.fs(1);s.fs(3);P.prepare(s,r,3);s.fs(1);P.trim(s,r+9);
  const Q=g.map(c=>c.slice());
  const expected=[
    [r-1],Array(r).fill(r),Array(r+1).fill(r+1),Array(r-1).fill(r),
    Array(r).fill(r+3),Array(r+3).fill(r+4),Array(r+3).fill(r+5),
    [r+6,r+6],Array(r).fill(r+7),Array(r+8).fill(r+8)
  ];
  assert.deepEqual(Q.slice(r-1),expected,'closed form of the parametric Q_k suffix');
  s.fs(4*columns-1);assert.equal(s.g.length,r+7+4*columns);
  s.a=r+7;s.codes=[7,s.a];s.taxed=false;
  s.packets=Array.from({length:columns},(_,i)=>({point:r+8+4*i,g1:r+9+4*i,g2:r+10+4*i,g3:r+11+4*i}));
  s.archive=r+6;P.E.restore(s,s.archive);
  s.seedAudit={WIndex:index,r,background:r-1,height,columns,events,certificates:cert.stats,
    commonSeed:Q,commonCounts:L.countResult(Q).values.map(String),graph:g.map(c=>c.slice()),
    path:'Q_k=W[k][1][3], expose(5k+2,3), [1], trim(5k+11); then [4c-1], restore(5k+8,row2)'};
  Sparse.attach(s,P,limits);return s;
}
module.exports={makeSeed};
