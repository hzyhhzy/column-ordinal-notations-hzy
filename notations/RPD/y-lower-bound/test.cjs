'use strict';

// Portable packaging/behavior regression. No research checkout, network,
// browser settings, package install or Lean build is needed.
const assert=require('node:assert/strict');
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm');
const crypto=require('node:crypto');
const started=Date.now(),deadline=started+12000;
function guard(){if(Date.now()>deadline)throw Error('12-second package test deadline');}
function load(source){
  const definitions=[];
  vm.runInNewContext(source,{register_notation:n=>definitions.push(n)},{timeout:1000});
  assert.equal(definitions.length,1);return definitions[0];
}
const source=fs.readFileSync(path.join(__dirname,'RPD-with-Y-bound.ne-rewritten.js'),'utf8');
const baseSource=fs.readFileSync(path.join(__dirname,'../RPD-mountain.ne-rewritten.js'),'utf8');
const notation=load(source),base=load(baseSource);
assert.equal(notation.id,'rpd-with-y-lower-bound-v1');
assert.notEqual(notation.id,base.id);
assert.deepEqual(Object.keys(notation.display_equiv),Object.keys(base.display_equiv));
assert.equal(Object.keys(notation.display_equiv).length,6);
assert.equal(notation.FS,notation.FS_alter);assert.equal(notation.FS,notation.FS_short);

let fsChecks=0,compareChecks=0,displayChecks=0,strongBounds=0;
const queue=[0,1,2].map(k=>base.FS('Limit',k)),seen=new Set(queue);
for(let i=0;i<queue.length&&i<50;i++){
  guard();const raw=queue[i];
  assert.equal(notation.is_limit(raw),base.is_limit(raw));
  assert.equal(notation.compare(raw,'Limit'),base.compare(raw,'Limit'));compareChecks++;
  for(const n of [0,1,2]){
    const next=base.FS(raw,n);assert.equal(notation.FS(raw,n),next);fsChecks++;
    const graph=base.debug.graph(next);
    if(queue.length<50&&Number(graph.size)<=12&&graph.atoms.length<=140&&!seen.has(next)){
      seen.add(next);queue.push(next);
    }
  }
}

function checkBound(list,word){
  guard();const raw=notation.display.from_display(list),bound=notation.debug.annotation(raw);
  assert.equal(bound.status,'lower-bound',bound.detail);
  assert.equal(bound.sequence.join(','),word);
  assert.equal(bound.sequence.join(','),bound.certificate.word.join(','));
  assert.equal(bound.certificateVerified,true);
  assert.equal(bound.proofStatus,'paper-lemmas-not-end-to-end-Lean');
  assert(bound.svg.includes('<svg')&&!/NaN|undefined/.test(bound.svg));strongBounds++;
  for(const spec of [notation.display,...Object.values(notation.display_equiv)]){
    const plain=spec.plain(raw),html=spec.html(raw);
    assert(plain.includes(' ≥ Y【')&&html.includes('≥ Y【')&&html.includes('<svg'));
    if(spec.from_display)assert.equal(spec.from_display(plain),raw);
    displayChecks++;
  }
  for(const n of [0,1,2]){assert.equal(notation.FS(raw,n),base.FS(raw,n));fsChecks++;}
}
checkBound('[][][(0,1,0)][(0,2,1)][(0,3,2)]','1,2,5,3,5,4');
for(const k of [2,3,4]){
  const unit=Array.from({length:k+1},(_,i)=>`(${k-i},1,1)`).join(',');
  checkBound(`[][][${unit}][(0,1,0)][(0,3,1)][(0,4,2)]`,`1,${k+2},2,5,3,5,4`);
}
const wide=notation.display.from_display('[]'.repeat(65));
assert.equal(notation.debug.annotation(wide).status,'unknown');
assert.equal(notation.FS(wide,0),base.FS(wide,0));
assert.equal(notation.debug.annotation('Limit').text,'Limit');
const cache=notation.debug.annotation_cache_stats();
assert(cache.hits>0&&cache.entries<=cache.maxEntries&&cache.chars<=cache.maxChars);
guard();
console.log(JSON.stringify({status:'passed',fsChecks,compareChecks,strongBounds,displayChecks,
  equivalentViews:6,sha256:crypto.createHash('sha256').update(source).digest('hex'),
  elapsedMs:Date.now()-started,rssMiB:+(process.memoryUsage().rss/1048576).toFixed(1)},null,2));
