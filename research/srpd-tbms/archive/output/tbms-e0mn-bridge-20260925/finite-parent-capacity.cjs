'use strict';

// One-based capacity: largest row on which a is an ancestor of j.
// Requires nested parent forests. The return table uses zero-based JS indices.
function capacities(g) {
  const table=[];
  for(let j=0;j<g.length;j++) {
    const row=new Uint32Array(j);
    for(let r=0;r<g[j].length;r++) {
      const p=g[j][r];
      if(r+1<g[j].length&&g[j][r+1]===p)continue;
      row[p-1]=Math.max(row[p-1],r+1);
      for(let a=0;a<p-1;a++)row[a]=Math.max(row[a],Math.min(r+1,table[p-1][a]));
    }
    table.push(row);
  }
  return table;
}
const at=(table,a,j)=>a>=1&&a<j?(table[j-1][a-1]??0):0;
const shiftedCapacity=(q,cut,span)=>q<=cut?q:q+span;
module.exports={capacities,at,shiftedCapacity};
