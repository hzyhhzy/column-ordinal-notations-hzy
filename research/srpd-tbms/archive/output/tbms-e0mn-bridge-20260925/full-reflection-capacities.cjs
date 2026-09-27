'use strict';

// Exact capacity transport in one full reflection, including the temporary
// last column. One-based addresses. Requires native-compatible strict M.
const assert=require('node:assert/strict');
const F=require('./finite-parent-capacity.cjs');
function makePrediction(g){
  const N=g.length,h=g.at(-1).length;
  assert(h>0);const d=g.at(-1).at(-1),L=N-d,cap=F.capacities(g);
  function at(a,z){
    assert(1<=a&&a<z&&z<=N+L);
    if(z<N)return {value:F.at(cap,a,z),kind:'old'};
    if(z===N)return a<d
      ?{value:F.at(cap,a,d),kind:'seam external'}
      :{value:Math.min(F.at(cap,a,N),h-1),kind:'seam internal'};
    const old=z-L;
    if(a<d)return {value:F.at(cap,a,old),kind:'copy external'};
    if(a<N)return {value:Math.min(F.at(cap,a,N),h-1,F.at(cap,d,old)),kind:'cross seam'};
    if(a===N)return {value:F.at(cap,d,old),kind:'seam to copy'};
    const q=F.at(cap,a-L,old);
    return {value:q<=d?q:q+L,kind:'internal copies'};
  }
  return {N,h,d,L,cap,at};
}
module.exports={makePrediction};
