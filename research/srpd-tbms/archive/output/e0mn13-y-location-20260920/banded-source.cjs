'use strict';

// A marked source class, checked against the original numerical Y.
// Marks are inherited under copy; they are not recomputed after a step.
const assert=require('node:assert/strict'),D=require('./direct-source.cjs');
function rowAncestor(ps,p,j,row){
  let a=j;while(a>p&&ps[a].parents.length>row)a=ps[a].parents[row];return a===p;
}
function mark(g){const b=Array(g.size).fill(false);for(const [,q] of g.atoms)b[q]=true;return b;}
function inspect(g,base){
  const ps=D.parents(g);assert.equal(base.length,g.size);
  for(const [,q] of g.atoms)assert(base[q],'genuine root is marked');
  for(let j=0;j<g.size;j++){
    const p=ps[j];
    for(let r=1;r<p.parents.length;r++)assert.equal(ps[p.parents[r]].high,null,'upper parent is not a tip');
    if(p.high===null)continue;
    const c=p.high,h=ps[c].parents.length;
    assert(!base[j]&&base[c],'tips unmarked, their roots marked');
    assert(p.parents.every(v=>v===c)&&p.parents.length===h+1,'uniform high tip');
    for(let v=c+1;v<j;v++){
      if(!h)assert.equal(ps[v].high,c,'height-zero star has only pure tips inside');
      let a=v;while(a>c&&ps[a].high!==c&&ps[a].parents.length)a=ps[a].parents[0];
      assert(a>c&&ps[a].high===c,'star interval is a band of same-root tip subtrees');
    }
    const zeroDesc=[];
    for(let v=j+1;v<g.size;v++)if(rowAncestor(ps,j,v,0)){
      if(!h)zeroDesc.push(v);
      if(rowAncestor(ps,c,v,h)){
        assert(!base[v],'no marked root in tip potential');
        // Consequence of root marking and the no-upper-tip condition. Keep it
        // explicit as an independently checked finite version of the lemma.
        assert.equal(ps[v].parents.length,h+1,'potential has exactly one live upper row');
      }
    }
    if(!h&&zeroDesc.length){
      assert.deepEqual(zeroDesc,[j+1],'zero tip has at most one immediate leaf');
      assert(!base[j+1]);assert.deepEqual(ps[j+1],{parents:[j],high:null});
    }
  }
  return ps;
}
function nextMarks(g,base,n){
  const x=g.size-1,ctrl=D.G.control(g),out=base.slice(0,x);
  if(n&&ctrl)for(let b=1;b<=n;b++)out.push(...base.slice(ctrl[2],x));
  return out;
}
function expected(g,base,n){
  const ps=inspect(g,base),x=g.size-1,out=ps.slice(0,x).map(p=>({parents:p.parents.slice(),high:p.high}));
  const ctrl=D.G.control(g);if(!n||!ctrl)return out;
  const high=!!ctrl[0],cut=ctrl[2],span=x-cut,row=ps[x].parents.length-1,h=ps[cut].parents.length;
  for(let b=1;b<=n;b++)for(let j=cut;j<x;j++){
    const move=p=>p<cut?p:p+b*span,previous=p=>p<cut?p:p+(b-1)*span;
    let p={parents:ps[j].parents.map(move),high:ps[j].high===null?null:move(ps[j].high)};
    if(high){
      if(j===cut)p={parents:Array(h+b).fill(cut+(b-1)*span),high:null};
      else if(rowAncestor(ps,cut,j,h)){
        assert(!base[j]&&ps[j].parents.length===h+1,'only one-row unmarked columns ascend');
        p.parents=ps[j].parents.slice(0,h).map(move).concat(Array(b+1).fill(move(ps[j].parents[h])));
      }
    }else if(j===cut)for(let u=0;u<row;u++)p.parents[u]=previous(ps[x].parents[u]);
    out.push(p);
  }
  return out;
}
module.exports={D,rowAncestor,mark,inspect,nextMarks,expected};
