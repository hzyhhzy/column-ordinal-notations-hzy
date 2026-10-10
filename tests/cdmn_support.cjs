"use strict";

function size(g,cap=Infinity) {
  let total=0,stack=[g];
  while(stack.length&&total<=cap) {
    const a=stack.pop();total+=1+a.length;
    for(const c of a)for(const e of c){total++;stack.push(e.r);}
  }
  return total;
}
function columns(g){return g.length+g.reduce((s,c)=>s+c.reduce((t,e)=>t+columns(e.r),0),0);}
// One hereditary right trim (the legacy zero rule), not current FS(g, 0).
function trim(g) {
  if(!g.length||!g.at(-1).length)return g.slice(0,-1);
  const col=g.at(-1),old=col.at(-1),row=trim(old.r);
  return [...g.slice(0,-1),[...col.slice(0,-1),...(row.length?[{p:old.p,r:row}]:[])]];
}
// Bounded, explicit witnessed descent. An exhausted budget is unknown, not false.
function witness(C,start,target,{steps=160,indices=12,nodes=4000,deadline=Date.now()+1000}={}) {
  let cursor=start;const route=[];
  while(Date.now()<deadline&&route.length<=steps) {
    const order=C.cmp(cursor,target);
    if(!order)return {found:true,route};
    if(order<0||route.length===steps||size(cursor,nodes)>nodes)break;
    let next;
    for(let n=0;n<indices;n++) {
      const child=C.FS(cursor,n);
      if(C.cmp(child,target)>=0){next=child;route.push(n);break;}
    }
    if(!next)break;
    cursor=next;
  }
  return {found:false,route};
}
function generator(seed) {
  let state=seed>>>0;
  return n=>{state=(Math.imul(state,1664525)+1013904223)>>>0;return(state>>>8)%n;};
}
module.exports={size,columns,trim,witness,generator};
