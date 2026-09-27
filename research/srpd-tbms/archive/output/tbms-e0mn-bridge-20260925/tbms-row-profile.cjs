'use strict';

// Native finite macros on nonincreasing TBMS columns whose row labels are
// ordinary monomials below epsilon_0. A profile records numeric values and
// cumulative ordinal endpoints, forgetting redundant constant subdivisions.
const assert=require('node:assert/strict');

function makeProfileTools(C,options={}) {
  const B=C.B,tick=options.tick??(()=>{}),maxEvents=options.maxEvents??12000,
    maxWidth=options.maxWidth??256,maxIndex=options.maxIndex??128;
  const stats={events:0,probes:0,localDowns:0,truncations:0,potentialChecks:0};
  const same=(a,b)=>JSON.stringify(a)===JSON.stringify(b);
  const cmp=(a,b)=>B.vertical_compare(a,b);
  function profile(expr) {
    return Array.from(expr,col=>{
      const ends=B.column_verticals(col),out=[];
      col.forEach(([value],r)=>{
        if(out.length&&out.at(-1).value===value)out.at(-1).end=ends[r];
        else out.push({value,end:ends[r]});
      });
      return out;
    });
  }
  function height(expr) {return B.column_verticals(expr.at(-1)??[]).at(-1)??[];}
  function guard(){tick();if(stats.events+stats.probes>=maxEvents){const e=Error('macro event guard');e.name='BudgetStop';throw e;}}
  function fs(expr,n,probe=false) {
    guard();const out=C.sourceFS(expr,n);
    if(out.length>maxWidth){const e=Error('macro width guard');e.name='BudgetStop';throw e;}
    if(probe)stats.probes++;else stats.events++;
    return out;
  }
  function deleteLast(expr) {
    let out=expr;
    while(out.at(-1)?.length&&!B.is_one(out.at(-1).at(-1)[1]))out=fs(out,0);
    return fs(out,0);
  }
  function localDown(expr) {
    assert(expr.at(-1)?.length&&B.is_one(expr.at(-1).at(-1)[1]));
    const width=expr.length;
    let out=fs(expr,1);
    while(out.length>width)out=deleteLast(out);
    assert.equal(out.length,width);stats.localDowns++;
    return out;
  }
  function potential(expr,V) {
    const col=expr.at(-1),ends=B.column_verticals(col),out=[];
    for(let v=V;v>=1;v--){let end=[];for(let i=0;i<col.length&&col[i][0]>=v;i++)end=ends[i];out.push(end);}
    return out;
  }
  function truncateLast(expr,gamma) {
    let out=expr;
    assert(out.length&&cmp(height(out),gamma)>=0);
    const original=profile(expr),V=expr.at(-1)[0]?.[0]??0;
    let oldPotential=potential(out,V);
    while(cmp(height(out),gamma)>0) {
      guard();
      if(B.is_one(out.at(-1).at(-1)[1]))out=localDown(out);
      else {
        let found=false;
        for(let n=0;n<=maxIndex;n++) {
          const candidate=fs(out,n,true);
          if(cmp(height(candidate),gamma)>=0){out=candidate;stats.events++;found=true;break;}
        }
        if(!found){const e=Error('macro index guard');e.name='BudgetStop';throw e;}
      }
      const next=potential(out,V);let order=0;
      for(let i=0;i<V&&!order;i++)order=cmp(next[i],oldPotential[i]);
      assert(order<0,'fixed-prefix threshold-height tuple strictly decreases');
      assert(cmp(height(out),gamma)>=0,'truncation must not overshoot');
      stats.potentialChecks++;oldPotential=next;
    }
    const expectedLast=[];
    if(gamma.length)for(const segment of original.at(-1)) {
      expectedLast.push({value:segment.value,end:cmp(segment.end,gamma)<0?segment.end:gamma});
      if(cmp(segment.end,gamma)>=0)break;
    }
    const expected=original.slice(0,-1).concat([expectedLast]);
    assert(same(profile(out),expected),'the requested profile truncation is exact');
    stats.truncations++;return out;
  }
  return {profile,height,cmp,fs,deleteLast,localDown,truncateLast,stats};
}

module.exports={makeProfileTools};
