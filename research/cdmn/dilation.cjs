"use strict";

// A mathematical translation, not a modified CDMN rule or a standardness claim.
// f(i)=offset+factor*i; insert factor-1 empty columns between source columns.
function dilate(g,factor=1,offset=0,finalPadding=false){
  if(!Number.isInteger(factor)||factor<1)throw Error("bad dilation");
  const out=[];
  for(let j=0;j<g.length;j++){
    out.push(g[j].map(e=>({p:offset+factor*e.p,r:dilate(e.r,factor,offset)})));
    if(j+1<g.length||finalPadding)for(let t=1;t<factor;t++)out.push([]);
  }
  return out;
}
function undilate(g,factor,offset){
  if(!g.length)return [];
  if((g.length-1)%factor)return null;
  const out=[];
  for(let j=0;j<g.length;j++){
    if(j%factor){if(g[j].length)return null;continue;}
    const col=[];
    for(const e of g[j]){
      if(e.p<offset||(e.p-offset)%factor)return null;
      const r=undilate(e.r,factor,offset);if(r===null)return null;
      col.push({p:(e.p-offset)/factor,r});
    }
    out.push(col);
  }
  return out;
}
module.exports={dilate,undilate};
