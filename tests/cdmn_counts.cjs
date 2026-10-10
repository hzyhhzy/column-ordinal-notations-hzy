"use strict";

// Independent bounded replay of the positive-index seam, not of the DP formula.
const assert = require("node:assert/strict"), fs = require("node:fs"), path = require("node:path");
const {createCDMN} = require("../notations/CDMN/cdmn-core.cjs");
const {generator} = require("./cdmn_support.cjs");
let N;
new Function("register_notation", fs.readFileSync(path.join(__dirname,"../notations/CDMN/CDMN.ne-rewritten.js"),"utf8"))(x => { N=x; });
const C = createCDMN({milliseconds:80,events:300000,cells:600000,columns:1200,depth:150});
const view=N.display_equiv.count, span=s=>'<span style="font-family:inherit;white-space:normal">'+s+'</span>';
assert.equal(view.name,"计数序列"); assert.equal(view.from_display,undefined);
for(const [input,text] of [
  ["0","0"],["[]","1"],["[][]","1,1"],["S1","1,2"],
  ["()(1^2)","1,3"],["()(1^3)","1,4"],
  ["[][0:2][1:2]","1,3,7"],
  ["[][0:2][1:1;0:2]","1,3,6"],
  ["[][0:3][1:2;0:1]","1,4,10"]
]) {
  assert.equal(view.plain(input),text);assert.equal(view.html(input),span(text));assert.equal(view.latex(input),text);
}
for(const input of ["S2","S3[2][2]","[][0:1][][1:[][2:1]]","Limit"]) {
  for(const mode of ["plain","html","latex"])assert.equal(view[mode](input),N.display[mode](input));
  assert.equal(N.debug.counts(input).values,null);
}
assert.equal(N.debug.counts("S2").reason,"nested-rows");
assert.equal(N.debug.counts("Limit").reason,"top");
assert.equal(N.debug.counts("()(1^3)",{events:0}).reason,"resource-limit");
assert.deepEqual(N.debug.counts("()(1^3)").values,[1n,4n]);
assert.equal(N.FS("()(1^3)",2),"[][0:2][1:2]");

const natural=h=>Array.from({length:h},()=>[]);
function chain(width,h) {return Array.from({length:width},(_,j)=>j?[{p:j-1,r:natural(h)}]:[]);}
for(const h of [1,2,3,8]) {
  const values=N.debug.counts(N.debug.format(chain(55,h))).values;
  assert(values);
  for(let j=0;j<values.length;j++) {
    const expected=h===1?BigInt(j+1):(BigInt(h)**BigInt(j+1)-1n)/BigInt(h-1);
    assert.equal(values[j],expected);
  }
}
assert(N.debug.counts(N.debug.format(chain(55,3))).values.at(-1)>2n**63n);
const tooCostly=N.debug.format(chain(40,1200));
assert.equal(N.debug.counts(tooCostly).reason,"resource-limit");
for(const mode of ["plain","html","latex"])assert.equal(view[mode](tooCostly),N.display[mode](tooCostly));
assert.equal(N.FS("[][0:2][1:2]",0),"[][0:2]");
assert.equal(view.plain(N.FS("[][0:2][1:2]",0)),"1,3");

const started=Date.now(), deadline=started+18000, random=generator(0x792847af);
const report={graphs:0,naiveColumns:0,naiveSteps:0,firstSeamChecks:0,zeroChecks:0,stepStops:0};
function naive(g) {
  const values=[];
  for(let j=0;j<g.length;j++) {
    const prefix=g.slice(0,j);let col=g[j],steps=1n;
    while(col.length) {
      if(steps>10000n||report.naiveSteps>=600000||Date.now()>deadline){report.stepStops++;return null;}
      col=C.FS([...prefix,col],1)[j];steps++;report.naiveSteps++;
    }
    values.push(steps);report.naiveColumns++;
  }
  return values;
}
for(let trial=0;trial<1200&&Date.now()<deadline;trial++) {
  const width=1+random(9),g=[];
  for(let j=0;j<width;j++) {
    const col=[];for(let p=j-1;p>=0;p--)if(random(4)===0)col.push({p,r:natural(1+random(4))});
    g.push(col);
  }
  const raw=N.debug.format(g), exact=N.debug.counts(raw).values, replay=naive(g);
  assert(exact); if(replay)assert.deepEqual(exact,replay); report.graphs++;
  const x=g.length-1;
  for(let n=1;n<=3;n++) {
    const h=C.FS(g,n),counts=N.debug.counts(N.debug.format(h)).values;
    assert(counts);
    assert.deepEqual(counts.slice(0,x),exact.slice(0,x));
    if(g[x].length)assert.equal(counts[x],exact[x]-1n);
    else assert.equal(counts.length,x);
    report.firstSeamChecks++;
  }
  const zero=C.FS(g,0),zc=N.debug.counts(N.debug.format(zero)).values;
  assert.deepEqual(zc.slice(0,x),exact.slice(0,x));
  assert.equal(zc.length,x); // Every natural-row graph is a copy-layer or successor case.
  report.zeroChecks++;
}
assert(report.graphs>=1000);assert(report.naiveColumns>=4000);assert.equal(report.stepStops,0);
report.elapsedMs=Date.now()-started;report.rssMiB=process.memoryUsage().rss/1048576;
report.scope="Exact finite-row count DP versus bounded actual seam replay; no well-ordering or live-browser claim.";
console.log(JSON.stringify(report,null,2));
