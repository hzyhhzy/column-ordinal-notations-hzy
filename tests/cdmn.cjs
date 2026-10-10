"use strict";

const assert=require("node:assert/strict"),fs=require("node:fs"),path=require("node:path");
const {createCDMN}=require("../notations/CDMN/cdmn-core.cjs");
const {dilate}=require("../research/cdmn/dilation.cjs");
const {size,columns,trim,witness,generator}=require("./cdmn_support.cjs");
let N;
new Function("register_notation",fs.readFileSync(path.join(__dirname,"../notations/CDMN/CDMN.ne-rewritten.js"),"utf8"))(x=>{assert(!N);N=x;});
const C=createCDMN({milliseconds:100,events:450000,cells:1000000,columns:1200,depth:150});
assert.equal(N.name,"CDMN");assert.equal(N.simple_name,"CDMN");assert(N.id.startsWith("cdmn-"));
assert.equal(N.display.plain("Limit"),"Limit of CDMN");assert.equal(N.FS("Limit",0),"[]");
assert.equal(N.FS("[]",2),"0");assert.equal(N.compare("0","[]"),-1);
assert.equal(N.FS_alter,N.FS);assert.equal(N.FS_short,N.FS);
assert.equal(N.id,"cdmn-prefix-fs-unshifted-20261009");
// Zero acts at the active copy layer, not at the deepest empty syntax column.
assert.equal(N.FS("S2",0),"[][]");
assert.equal(N.FS("S2",1),"[][0:1]");
assert.equal(N.FS("S2",2),"[][0:2]");
assert.equal(N.FS("()(1^2)",0),"[]");
assert.equal(N.FS("()(1^2)",1),"[][0:1]");
assert.equal(N.FS("()(1^2)",2),"[][0:1][1:1]");
assert.equal(N.FS("[][0:2][1:2]",0),"[][0:2]");
assert.equal(N.FS("[][0:2][1:2]",1),"[][0:2][1:1;0:2]");
assert.equal(N.FS("[][0:2][1:1;0:2]",0),"[][0:2]");
assert.equal(N.display.name,"BTBMS式");
assert.deepEqual(Object.values(N.display_equiv).map(v=>v.name),["列表","完整列表","计数序列"]);
for(const input of ["[0:1]","[][0:0]","[][1:1]","[][][1:1;1:2]","@1=[0:1] | [][0:@1]","[][0:1]garbage"])
  assert.throws(()=>N.display.from_display(input));
assert.throws(()=>N.FS("S2",-1));assert.throws(()=>N.FS("S2",0.5));
assert.throws(()=>N.display.from_display("[][0:1201]"));
for(const input of ["(1)","()(0)","()(2)","()(1^0)","()(1^)","()(1^{2)","()(1^2})",
  "()(1^[])","()(1^2,)","()()(2,2^2)","()(1^1201)","()(9007199254740992)","()(1)<script>"])
  assert.throws(()=>N.display.from_display(input));
const displayCases=[
  ["0","0","0","0"],
  ["[]","()","()","()"],
  ["[][]","()()","()()","()()"],
  ["S1","()(1)","()(1)","()(1)"],
  ["S2","()(1^(1))","()(1<sup>(1)</sup>)","()(1^{(1)})"],
  ["[][0:3][1:2;0:1]","()(1^3)(2^2,1)","()(1<sup>3</sup>)(2<sup>2</sup>,1)","()(1^{3})(2^{2},1)"],
  ["S3[2][2]","()(1^(1)(2))","()(1<sup>(1)(2)</sup>)","()(1^{(1)(2)})"],
];
for(const [input,text,html,latex] of displayCases) {
  assert.equal(N.display.plain(input),text);
  assert.equal(N.display.html(input),'<span style="font-family:inherit;white-space:normal">'+html+'</span>');
  assert.equal(N.display.latex(input),latex);
  assert.equal(N.compare(N.display.from_display(text),input),0);
  assert.equal(N.compare(N.display.from_display(latex),input),0);
}
assert.equal(N.display.from_display(" () (1^{3}) (2^{2},1^1) "),"[][0:3][1:2;0:1]");
assert.equal(N.display.plain("()(1^1)"),"()(1)");
assert.equal(N.display.from_display("()(1^())"),"[][0:1]");
assert.equal(N.FS("()(1^(1))",3),N.FS("S2",3));
assert.equal(N.is_limit("()(1^(1))"),N.is_limit("S2"));
const fixtures=JSON.parse(fs.readFileSync(path.join(__dirname,"../notations/CDMN/fixtures/regressions.json"),"utf8"));
for(const f of fixtures){assert.equal(N.display_equiv.list.plain(f.input),f.text);assert.deepEqual(N.debug.parse(f.input),f.graph);}

// Current research entrances: literal endpoints and complete finite witnesses.
// These checks do not prove the claims about entire cones below these graphs.
const adjacentReader="()(1^(1)())", adjacentRaw="[][0:[0:1][]]";
assert.equal(N.display.from_display(adjacentReader),adjacentRaw);
function follow(g,route) {
  for(const n of route) {
    const next=C.FS(g,n);assert(C.isLegal(next));assert.equal(C.cmp(next,g),-1);g=next;
  }
  return g;
}
const adjacent=N.debug.parse(adjacentRaw);
assert.deepEqual(follow(C.seed(3),[2,2,1,1,0]),adjacent);
for(let n=0;n<=8;n++) {
  const expected=[[],...Array.from({length:n},(_,j)=>[{p:j,r:[[{p:j,r:[[]]}]]}])];
  assert.deepEqual(C.FS(adjacent,n),expected);
  assert.equal(N.FS(adjacentReader,n),N.debug.format(expected));
}
const c2=C.FS(adjacent,2);
assert.equal(N.display.plain(N.debug.format(c2)),"()(1^(1))(2^(2))");
for(const [text,route] of [
  ["()(1^(1))(1)(3^(1))(3)",[1,0,1,1,0,1,2,1,0,0,0,1,2,1,0,1,0,0,0,1,0,1,1,0,1,0,0,0,0,1,0,0]],
  ["()(1^(1))(1)(3^(1))(3^2)(5,3)(6^(1))",[1,0,1,1,0,1,2,1,0,0,0,1,2,1,0,1,0,0,0,1,0,1,1,0,1,0,0,0,1,2,1,1,0,0,1,0,0,1,1,0]]
]) {
  const endpoint=follow(c2,route);
  assert.deepEqual(endpoint,N.debug.parse(text));
  assert.equal(N.display.plain(N.debug.format(endpoint)),text);
}

function dilationPlan(g,n,d) {
  if(!g.length)return [];
  if(!n||!g.at(-1).length)return Array(columns(dilate(g,d))-columns(dilate(C.prune(g),d))).fill(0);
  const r=g.at(-1).at(-1).r;
  if(r.at(-1).length)return dilationPlan(r,n,d);
  return [...Array(r.length>1?d-1:0).fill(0),n,...Array(d-1).fill(0)];
}
const rnd=generator(0x81dcbaf3),start=Date.now(),deadline=start+20000;
const report={expansions:0,displayRoundTrips:0,legacyZeroPaths:0,outerPrefixPairs:0,
  retreatPairs:0,retreatUnknown:0,retreatWitnessSteps:0,dilationMacros:0,
  dilationUnknown:0,dilationWitnessSteps:0,resourceStops:0,sizeStops:0};
for(let trial=0;trial<800&&Date.now()<deadline;trial++) {
  let g=C.seed(1+rnd(6)),s=N.debug.format(g);
  try {
    for(let j=0;j<18&&g.length&&Date.now()<deadline;j++) {
      const oldSize=size(g,2600);if(oldSize>2500){report.sizeStops++;break;}
      for(const view of [N.display,...Object.values(N.display_equiv)].filter(v=>v.from_display)) {
        const t=view.plain(s);assert.equal(N.compare(view.from_display(t),s),0);
        assert.equal(view.from_display(t),s);
        assert(!t.includes("@"));assert.equal(typeof view.html(s),"string");assert.equal(typeof view.latex(s),"string");
        report.displayRoundTrips++;
      }
      const n=rnd(4),h=C.FS(g,n),t=N.FS(s,n);
      assert.deepEqual(N.debug.parse(t),h);assert(C.isLegal(h));assert.equal(C.cmp(h,g),-1);
      if(n)assert(size(h)<=(n+1)*oldSize);
      const zero=C.prune(g);
      assert(columns(zero)<columns(g));
      // The new zero is still exactly a finite sequence of hereditary trims.
      let trimmed=g;
      for(let k=0;k<columns(g)-columns(zero);k++)trimmed=trim(trimmed);
      assert.deepEqual(trimmed,zero);report.legacyZeroPaths++;
      if(g.at(-1).length&&!g.at(-1).at(-1).r.at(-1).length) {
        assert.deepEqual(zero,g.slice(0,-1));
        const next=C.FS(g,n+1);
        assert.deepEqual(next.slice(0,h.length),h);report.outerPrefixPairs++;
      } else if(g.at(-1).length)assert.equal(zero.length,g.length);
      if(oldSize<180&&report.retreatPairs<800) {
        let above=C.FS(g,n+1);const steps=columns(above)-columns(h);assert(steps>=0);
        for(let k=0;k<steps;k++)above=trim(above);
        assert.deepEqual(above,h);
        const result=witness(C,C.FS(g,n+1),h,{deadline});
        if(result.found) {
          let replay=C.FS(g,n+1);for(const index of result.route)replay=C.FS(replay,index);
          assert.deepEqual(replay,h);report.retreatPairs++;report.retreatWitnessSteps+=result.route.length;
        } else report.retreatUnknown++;
      }
      if(oldSize<220&&report.dilationMacros<1000) {
        const d=2+rnd(2);let stretched=dilate(g,d),replay=stretched,complete=true;
        for(const i of dilationPlan(g,n,d)) {
          const expected=i?C.FS(stretched,i):trim(stretched);
          if(complete) {
            const result=i?{found:true,route:[i]}:witness(C,replay,expected,{deadline});
            if(result.found) {
              for(const index of result.route)replay=C.FS(replay,index);
              assert.deepEqual(replay,expected);report.dilationWitnessSteps+=result.route.length;
            } else complete=false;
          }
          stretched=expected;
        }
        assert.deepEqual(stretched,dilate(h,d));
        if(complete){assert.deepEqual(replay,dilate(h,d));report.dilationMacros++;}
        else report.dilationUnknown++;
      }
      g=h;s=t;report.expansions++;
    }
  }catch(e){if(/limit|上限/.test(e.message))report.resourceStops++;else throw e;}
}
assert(report.expansions>=4000,"insufficient bounded coverage");
assert(report.retreatPairs>=100&&report.dilationMacros>=100,"insufficient witnessed path coverage");
const cache=N.debug.cacheStatus();assert(cache.entries<=32&&cache.nodes<=80000&&cache.characters<=650000);
report.elapsedMs=Date.now()-start;report.rssMiB=process.memoryUsage().rss/1048576;
report.scope="Finite implementation checks. Legacy trim identities are separate from current FS; retreat/dilation counts require explicit current-step replays, with budget misses recorded as unknown. Not a universal reachability, well-ordering, Lean or live-browser certificate.";
console.log(JSON.stringify(report,null,2));
