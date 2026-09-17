/* Independent full-root JS oracle plus optional Python-vector cross-checks.
   Run node --max-old-space-size=256 tests/ard2_ner.cjs [vectors.json].
   One process, 25 seconds, 64 columns, 100,000 atoms. No network/file writes. */
'use strict';
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm');
const assert=require('node:assert/strict');
const started=Date.now(),scope=vm.createContext({queueMicrotask});
scope.register_notation=n=>{assert(!scope.ne);scope.ne=n;};
vm.runInContext(fs.readFileSync(path.join(__dirname,'../notations/ARD2/ARD2.ne-rewritten.js'),'utf8'),scope,{timeout:1200});
async function call(code,args) {
  await Promise.resolve();assert(Date.now()-started<25000,'25-second test deadline');
  assert(process.memoryUsage().rss<512*1048576,'512 MiB RSS ceiling');
  scope.args=args;return vm.runInContext(code,scope,{timeout:1500});
}
const native=x=>JSON.parse(JSON.stringify(x));
const key=e=>[e[1],e[0],e[2]];
function cmp(a,b){for(let i=0;i<3;i++)if(a[i]!==b[i])return a[i]-b[i];return 0;}
function norm(cols){return cols.map(col=>{
  // Independent dominance definition, not the production record-high scan.
  const unique=[...new Map(col.map(e=>[e.join(','),e])).values()];
  return unique.filter(([k,p,q],i)=>!unique.some(([K,P,Q],j)=>j!==i&&P>=p&&(K>k||K===k&&Q>=q)))
    .sort((a,b)=>-cmp(key(a),key(b)));
});}
const text=cols=>cols.length?norm(cols).map(c=>'['+c.map(e=>'('+e.join(',')+')').join(',')+']').join(''):'∅';
function atomic(cols,n){
  if(!cols.length||!n||!cols.at(-1).length)return cols.slice(0,-1);
  const x=cols.length-1,atoms=[];
  cols.forEach((col,j)=>col.forEach(([k,p,q])=>{for(let r=0;r<=q;r++)atoms.push([k,r,p,j]);}));
  const [K,r,c]=atoms.filter(e=>e[3]===x).sort((a,b)=>-cmp(a,b))[0],L=x-c;
  assert(x+n*L<=64);const result=new Map();
  function add(k,q,p,j){const e=[k,q,p,j];result.set(e.join(','),e);assert(result.size<=100000);}
  for(let b=0;b<=n;b++){
    const move=i=>i<c?i:i+b*L;
    for(const [k,q,p,j] of atoms){
      if(j<x)for(let u=0;u<=move(q);u++)add(move(k),u,move(p),move(j));
      else if(b<n)for(let u=0;u<=move(q);u++)if(k<K||k===K&&u<move(r))add(move(k),u,move(p),move(x));
    }
    if(b<n)for(let h=0;h<move(K);h++)for(let q=0;q<=move(x);q++)add(h,q,move(c),move(x));
  }
  const answer=Array.from({length:x+n*L},()=>[]);
  for(const [k,q,p,j] of result.values())answer[j].push([k,p,q]);return norm(answer);
}
let state=0x37a114a9;
function random(n){state^=state<<13;state^=state>>>17;state^=state<<5;return (state>>>0)%n;}
async function main(){
  assert.equal(scope.ne.id,'ard2-skyline-v02');assert.equal(scope.ne.name,'ARD2');
  // Both versions can coexist; legacy names/paths changed, not its rule.
  const legacyScope=vm.createContext({queueMicrotask});
  legacyScope.register_notation=n=>{assert(!legacyScope.ne);legacyScope.ne=n;};
  vm.runInContext(fs.readFileSync(path.join(__dirname,'../notations/ARD2-legacy/ARD2-legacy.ne-rewritten.js'),'utf8'),legacyScope,{timeout:1200});
  assert.equal(legacyScope.ne.id,'ard2-legacy-v01');
  assert.equal(legacyScope.ne.name,'ARD2-legacy');
  assert.equal(vm.runInContext('ne.FS("A2",1)',legacyScope,{timeout:1500}),'[][(1,0,0),(0,0,1)]');
  assert.equal(vm.runInContext('ne.display.plain("Limit of ARD2-legacy")',legacyScope,{timeout:1500}),'Limit of ARD2-legacy');
  for(let j=0;j<=5;j++)for(let n=0;n<=3;n++){
    legacyScope.args={j,n};
    const old=vm.runInContext('ne.FS("A"+args.j,args.n)',legacyScope,{timeout:1500});
    assert.equal(await call('ne.display.plain(args)',old),await call('ne.FS("A"+args.j,args.n)',{j,n}));
  }
  let graphs=0,steps=0,pythonSteps=0,comparisons=0,countCases=0;
  const samples=[];
  for(let n=0;n<9;n++)samples.push(Array.from({length:n},(_,j)=>j?[[j,j-1,j]]:[]));
  for(let t=0;t<240;t++)samples.push(Array.from({length:random(9)},(_,j)=>
    Array.from({length:random(j*2+1)},()=>[random(j+1),random(j),random(j+1)])));
  for(const input of samples){
    const raw=text(input),cols=norm(input),outs=[];
    assert.equal(await call('ne.display.plain(args)',raw),raw);
    for(let n=0;n<4;n++){
      const expected=text(atomic(cols,n)),result=await call('ne.FS(args.raw,args.n)',{raw,n});
      assert.equal(result,expected);outs.push(result);steps++;
      assert.equal(await call('ne.FS(args.raw,BigInt(args.n))',{raw,n}),result);
      assert.equal(await call('ne.compare(args.a,args.b)',{a:result,b:raw}),cols.length?-1:0);
    }
    for(let n=1;n<4;n++)assert(outs[n].startsWith(outs[n-1]==='∅'?'':outs[n-1]));
    graphs++;
  }
  assert.equal(await call('ne.FS("A2",1)'),'[][(1,0,0)]');
  const values=await call('ne.debug.counts("A5").map(String)');
  assert.deepEqual(Array.from(values),['1','5','55','969','23751']);countCases++;
  assert(await call('ne.debug.counts("A3").every(x=>typeof x==="bigint")'));
  for(const raw of ['[(0,0,0)]','[][(2,0,0)]','[][(0,0,2)]','[][(0,1,0)]','A3[-1]'])
    await assert.rejects(call('ne.display.plain(args)',raw));
  await assert.rejects(call('ne.debug.counts("A3",{maxWork:1})'),/超限/);
  assert.deepEqual(native(await call('(()=>{try{ne.debug.counts("A3",{maxWork:1});}catch(e){}return [ne.FS("A2",1),ne.compare("A1","A2")];})()')),
    ['[][(1,0,0)]',-1]);
  if(process.argv[2]){
    const payload=fs.readFileSync(process.argv[2]==='--stdin'?0:process.argv[2],'utf8');assert(payload.length<4000000);
    const data=JSON.parse(payload);assert(data.cases.length<=250&&data.comparisons.length<=1000&&data.counts.length<=30);
    for(const item of data.cases)for(let n=0;n<item.outputs.length;n++){
      assert.equal(await call('ne.FS(args.raw,args.n)',{raw:item.raw,n}),item.outputs[n]);pythonSteps++;
    }
    for(const item of data.comparisons){assert.equal(await call('ne.compare(args.a,args.b)',item),item.expected);comparisons++;}
    for(const item of data.counts){assert.deepEqual(Array.from(await call('ne.debug.counts(args).map(String)',item.raw)),item.expected);countCases++;}
  }
  console.log(JSON.stringify({ok:true,graphs,atomicSteps:steps,pythonSteps,comparisons,countCases,
    milliseconds:Date.now()-started,rssMiB:Math.ceil(process.memoryUsage().rss/1048576),processes:1}));
}
main().catch(error=>{console.error(error);process.exitCode=1;});
