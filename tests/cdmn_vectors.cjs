"use strict";

// Bounded cross-language cases; this generator does not prove a theorem.
const {createCDMN}=require("../notations/CDMN/cdmn-core.cjs");
const {size,generator}=require("./cdmn_support.cjs");
const C=createCDMN({milliseconds:60,columns:150,events:150000,cells:400000,depth:100});
const rnd=generator(0x16fe2a33),deadline=Date.now()+15000;
function raw(base,depth) {
  return Array.from({length:1+rnd(3)},(_,j)=>{
    if(!depth||!(base+j))return [];
    const parents=[...new Set(Array.from({length:rnd(3)},()=>rnd(base+j)))].sort((a,b)=>b-a);
    return parents.map(p=>({p,r:raw(base+j,depth-1)}));
  });
}
const targets=[3000,1500,1500],counts=[0,0,0];let stops=0,sizeSkips=0;
for(let mode=0;mode<3;mode++)for(let trial=0;trial<2500&&counts[mode]<targets[mode]&&Date.now()<deadline;trial++) {
  try {
    const context=mode===2?raw(0,2):[];
    let g=mode===0?C.seed(1+rnd(6)):raw(context.length,3);
    for(let step=0;step<(mode===0?12:3)&&g.length&&counts[mode]<targets[mode];step++) {
      if(size(g,1500)>1400){sizeSkips++;break;}
      const n=rnd(5),expected=C.FS(g,n,context);
      if(size(expected,5100)>5000){sizeSkips++;break;}
      console.log(JSON.stringify({graph:g,n,context,expected}));counts[mode]++;g=expected;
    }
  }catch(e){if(/limit/.test(e.message))stops++;else throw e;}
}
console.error(JSON.stringify({emitted:counts.reduce((a,b)=>a+b,0),byMode:counts,resourceStops:stops,sizeSkips}));
if(counts.some((n,i)=>n!==targets[i]))throw Error("CDMN vector budget ended before completing its inventory");
