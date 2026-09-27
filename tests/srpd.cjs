'use strict';

// Finite implementation checks, not an all-domain comparison theorem.
// No private workspace, upstream checkout, network or third-party package.
const assert=require('node:assert/strict'),fs=require('node:fs'),path=require('node:path');
const root=path.join(__dirname,'..'),dir=path.join(root,'notations/SRPD');
const P=require(path.join(dir,'SRPD.ne-rewritten.js'));
function load(relative){let r;new Function('register_notation',fs.readFileSync(path.join(root,relative),'utf8'))(n=>r=n);return r;}
const R=load('notations/RPD/RPD-mountain.ne-rewritten.js');
const variants=['ARD','ARD2'].map(name=>({name,r:load(`notations/${name}/${name}.ne-rewritten.js`)}));
const N=load('notations/SRPD/SRPD.ne-rewritten.js');
const started=Date.now(),limits={ms:30000,rssMiB:650,width:27,states:1200,queue:1700};
const report={states:0,steps:0,rawGraphs:0,rawSteps:0,rawCountPairs:0,countPairs:0,
  orderPairs:0,localSteps:0,widthSkipped:0,heightRoundTrips:0,heightRawSupported:0,heightRawRejected:0,
  ardSteps:0,ard2Steps:0,endpointPairs:0},cases=[];
function tick(){assert(Date.now()-started<limits.ms,'SRPD test time guard');assert(process.memoryUsage().rss<limits.rssMiB*2**20,'SRPD test RSS guard');}
function project(raw){return R.debug.adjacency(raw).map(col=>{
  const list=[];let high=-1;
  for(const[k,p,q]of col){assert.equal(k,'0');const row=Number(q);
    if(row>high){list.push(...Array(row-high).fill(Number(p)));high=row;}}
  return list;
}).slice(1);}
function liftText(g){return '[]'+g.map(col=>'['+col.flatMap((p,t)=>t===col.length-1||col[t+1]!==p?[`(0,${p},${t})`]:[]).join(',')+']').join('');}
const toRPD=g=>R.display.from_display(liftText(g));
function legalColumns(j){const out=[[]];for(let h=1;h<=j;h++){
  function add(prefix,maximum){if(prefix.length===h){out.push(prefix);return;}
    for(let p=h-1;p<=maximum;p++)add(prefix.concat(p),p);}
  add([],j-1);
}return out;}
async function main(){
  assert.equal(N.name,'SRPD');assert.equal(N.id,'srpd-implicit-root-v02');
  assert.deepEqual(Object.keys(N.display_equiv),['计数序列','层级列表']);
  assert.equal(N.display.plain('Limit'),'[0]');assert.equal(N.display_equiv['计数序列'].plain('Limit[4]'),'1,2,4,8');
  const heights=N.display_equiv['层级列表'];
  assert.equal(heights.plain('Limit[4]'),'[][1][2,1][3,2,1]');
  assert.deepEqual(P.parse('Limit of SRPD[4]'),P.parse('RPD0[4]'));
  assert.deepEqual(heights.from_display('SRPD[4]'),P.parse('Limit[4]'));
  assert.throws(()=>P.parse('[][0,0]'));assert.throws(()=>heights.from_display('[][3]'));
  const ambiguous=[[],[1],[1],[2]],canonical=[[],[1],[1],[3]];
  assert.deepEqual(P.heightGraph(ambiguous),P.heightGraph(canonical));assert.throws(()=>heights.plain(ambiguous));
  assert.deepEqual(heights.from_display(heights.plain(canonical)),canonical);
  const witness=require(path.join(dir,'fixtures/height-naive-counterexample.json'));
  let reached=P.INITIAL;for(const n of witness.path){tick();reached=P.expand(reached,n);}
  assert.deepEqual(reached,witness.graph.slice(1));assert.deepEqual(P.heightGraph(reached),witness.heights.slice(1));
  assert.deepEqual(heights.from_display(heights.plain(reached)),reached);
  assert.notEqual(witness.firstDifference.correctParent,witness.firstDifference.naiveParent);
  const completion=require(path.join(dir,'fixtures/completion-counterexample.json'));
  reached=P.INITIAL;for(const n of completion.path)reached=P.expand(reached,n);
  assert.deepEqual(reached,completion.graph);assert.deepEqual(P.expand(reached,1),completion.child);
  report.fixturePaths=[witness.path.length,completion.path.length];
  let raw=[[]];for(let j=1;j<=4;j++)raw=raw.flatMap(g=>legalColumns(j).map(c=>g.concat([c])));
  for(const g of raw){tick();const r=toRPD(g);assert.deepEqual(project(r),g);
    assert.deepEqual(P.countResult(g).values.map(String),R.debug.column_numbers(r).slice(1));report.rawCountPairs++;
    for(let n=0;n<4;n++){assert.deepEqual(P.expand(g,n),project(R.FS(r,n)));report.rawSteps++;}
    const h=P.heightGraph(g),recovered=P.parentsFromHeights(h);
    if(P.compare(recovered,g)===0){assert.deepEqual(heights.from_display(heights.plain(g)),g);report.heightRawSupported++;}
    else{assert.throws(()=>heights.plain(g));report.heightRawRejected++;}
    report.rawGraphs++;
  }
  assert.equal(report.rawGraphs,1024);assert.equal(report.heightRawSupported,388);assert.equal(report.heightRawRejected,636);
  for(let n=0;n<=25;n++){
    const g=P.expand(P.INITIAL,n);assert.deepEqual(g,project(R.FS(R.FS('Limit',0),n)));
    assert.deepEqual(g,Array.from({length:n},(_,i)=>Array(i).fill(i)));
    for(const {r} of variants){const e=r.display.from_display('[][][(0,1,1)]');
      assert.equal(r.display.plain(r.FS(e,n)),liftText(P.expand(P.INITIAL,n+1)));report.endpointPairs++;}
  }
  const queue=[{g:P.INITIAL,r:R.FS('Limit',0)}],seen=new Set([JSON.stringify(P.INITIAL)]),checked=[];
  for(let i=0;i<queue.length&&i<limits.states;i++){
    await new Promise(setImmediate);tick();const {g,r}=queue[i],unchanged=JSON.stringify(g),counts=P.countResult(g).values;
    assert.deepEqual(g,project(r));assert.deepEqual(counts.map(String),R.debug.column_numbers(r).slice(1));report.countPairs++;
    assert.deepEqual(heights.from_display(heights.plain(g)),g);report.heightRoundTrips++;
    if(i>0)for(const col of g)assert(col.every(p=>col.length<=p),'strict descendant height bound');
    if(g.at(-1)?.length){const c=g.at(-1),p=c.at(-1),lower=g.slice(0,-1).concat([c.slice(0,-1).concat(P.parentColumn(g,p).slice(c.length-1))]);
      assert.deepEqual(lower,project(R.debug.first_column_step(r)));report.localSteps++;}
    const children=[];
    for(const n of [0,1,2,4]){
      const span=g.at(-1)?.length?g.length-g.at(-1).at(-1):0;
      if(n&&span&&g.length-1+n*span>limits.width){report.widthSkipped++;continue;}
      const child=P.expand(g,n),rc=R.FS(r,n);P.check(child);assert.deepEqual(child,project(rc));report.steps++;
      assert.deepEqual(heights.from_display(heights.plain(child)),child);report.heightRoundTrips++;
      if(g.length)assert(P.compare(child,g)<0);
      if(children.length)assert.deepEqual(child.slice(0,children.at(-1).graph.length),children.at(-1).graph);
      if(i>0&&g.length)for(const {name,r:a} of variants){
        const actual=a.FS(a.display.from_display(liftText(g)),n);
        assert.equal(a.display.plain(actual),liftText(child),name+' strict finite-row commutation');
        report[name==='ARD'?'ardSteps':'ard2Steps']++;
      }
      children.push({n,graph:child});
      const k=JSON.stringify(child);if(!seen.has(k)&&queue.length<limits.queue){seen.add(k);queue.push({g:child,r:rc});}
    }
    if(i%7===0&&cases.length<150)cases.push({graph:g,counts:counts.map(String),children});
    assert.equal(JSON.stringify(g),unchanged);checked.push({g,r});report.states++;
  }
  for(let i=0;i<4000;i++){if(i%64===0){await new Promise(setImmediate);tick();}
    const a=checked[(i*73+3)%checked.length],b=checked[(i*197+7)%checked.length];
    assert.equal(P.compare(a.g,b.g),Math.sign(R.compare(a.r,b.r)));report.orderPairs++;}
  report.uncheckedQueued=queue.length-report.states;report.pythonCases=cases.length;
  if(process.argv.includes('--python-cases')){console.log(JSON.stringify(cases));return;}
  console.log(JSON.stringify({scope:'bounded packaged SRPD/RPD raw correspondence, ARD/ARD2 strict low-cone correspondence, views and exact counts',
    noLeanOrUniversalProof:true,limits,...report,elapsedMs:Date.now()-started,rssMiB:process.memoryUsage().rss/2**20},null,2));
}
main().catch(e=>{console.error(e);process.exitCode=1;});
