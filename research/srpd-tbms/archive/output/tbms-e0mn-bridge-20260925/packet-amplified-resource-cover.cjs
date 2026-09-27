'use strict';

// Research extension of packet-graded-resource-cover.cjs: one persistent
// self-amplifying resource template, and arbitrarily high finite graded banks.
// The predecessor implementation is kept unchanged. Native notation rules
// are unchanged; bounded checks do not substitute for the all-future proof.
const assert = require('node:assert/strict');
const P = require('./packet-main-cover.cjs');
const Sparse = require('./packet-sparse-native-state.cjs');
const {L} = require('./srpd-boundary-factorization.cjs');
const {createCertifier} = require('../e0mn-y13425810-20260920/finite-local-certificate.cjs');
const {makeCover} = require('./epsilon-row-cover.cjs');
const started = Date.now();
const limits = {ms:20000,rssMiB:650,width:30000,downTransientWidth:60000,
  events:160000,pairs:4000000,nodes:140,sourceWidth:24,steps:35,navigation:500,
  index:64,wordLength:100,nativeWidth:90};
Object.assign(P.limits, limits, {logicalWidth:limits.sourceWidth});
Object.assign(P.E.limits, limits, {states:2000,restore:limits.navigation});
const stats = {checks:0,bankPairs:0,ports:0,mainSegments:0,sourceSteps:0,
  activations:0,allocations:0,prefixRestores:0,tailSplits:0,prefixChildren:0,
  topDowns:0,units:0,limits:0,deletes:0,maxWidth:0,maxNodes:0,
  templateAllocations:0,templateAmplifications:0,activeContinuations:0};
function tick() {
  P.tick();
  assert(Date.now()-started<limits.ms, 'graded time guard');
  assert(process.memoryUsage().rss<limits.rssMiB*2**20, 'graded RSS guard');
  assert(stats.bankPairs<limits.pairs, 'graded pair guard');
  assert(stats.sourceSteps<=limits.steps, 'graded source-step guard');
}
const native = makeCover({tick,maxWidth:limits.sourceWidth});
const {B,M,cmp,eq,rowOrdinal,endpoints,sourceFS} = native;
const key = a => JSON.stringify(a);
const clone = a => JSON.parse(JSON.stringify(a));
const add = M.debug.ordAdd;
const power = exp => [{exp:clone(exp),coeff:1}];
const nat = n => n ? [{exp:[],coeff:n}] : [];
function word(delta) {
  const out=[];
  for(const t of delta) {
    assert(!t.exp.length || (t.exp.length===1 && !t.exp[0].exp.length),
      'bank exponent is a finite polynomial in omega');
    const d=t.exp.length?t.exp[0].coeff:0;
    assert(Number.isSafeInteger(d) && d>=0 && d<=100, 'finite bank level guard');
    assert(t.coeff<=limits.wordLength, 'word coefficient guard');
    for(let i=0;i<t.coeff;i++)out.push(d);
  }
  assert(out.length<=limits.wordLength, 'bank word length guard');
  return out;
}
function ordinalWord(w) {
  let a=[];
  for(const d of w)a=add(a,power(nat(d)));
  return a;
}
function allNodes(root) {
  const out=[];
  function visit(v) {out.push(v);v.children.forEach(visit);}
  visit(root);return out;
}
const end = v => add(v.base,power(v.exp));
function grade(s,a) {
  if(!a.length)return 7;
  const v=s.byEnd.get(key(a));
  assert(v, 'unregistered cumulative endpoint');
  return v.bank.at(-1)+1;
}
function activeBank(s) {return s.active.node.bank.slice(0,s.active.length);}
function bindActive(s,v,length=v.bank.length) {
  assert(length>=1 && length<=v.bank.length);
  s.active={node:v,length};s.archive=v.bank[length-1];
}
function restore(s,v=s.active.node,length=s.active.length) {
  bindActive(s,v,length);P.E.restore(s,s.archive);
}
function transport(s,cut,delta) {
  const move=p=>p>=cut?p+delta:p;
  s.a=move(s.a);s.codes=s.codes.map(q=>q>cut?q+delta:q);
  s.warm.at=move(s.warm.at);s.warm.points=s.warm.points.map(move);
  s.packets=s.packets.map(p=>Object.fromEntries(Object.entries(p).map(
    ([k,v])=>[k,typeof v==='number'?move(v):v])));
  for(const v of allNodes(s.root))v.bank=v.bank.map(move);
  if(s.root.high>cut)s.root.high+=delta;
}
function bankCover(q,bank,w,label) {
  assert.equal(bank.length,w.length+1,label+': bank width');
  for(let j=1;j<bank.length;j++)for(let i=0;i<j;i++) {
    const actual=Sparse.at(q,bank[i],bank[j]),need=4+w[j-1];
    assert(actual>=need,`${label}: (${i},${j}) capacity ${actual} needs ${need}`);
    stats.bankPairs++;
  }
}
function check(s,label='state') {
  tick();stats.checks++;
  const N=s.g.length,q=Sparse.capacities(s.g),K=s.codes.at(-1);
  stats.maxWidth=Math.max(stats.maxWidth,N);
  assert(N<=limits.width,label+': width');
  if(!s.source.length)return;
  const nodes=allNodes(s.root);
  assert(nodes.length<=limits.nodes,'graded node guard');
  stats.maxNodes=Math.max(stats.maxNodes,nodes.length);
  assert.equal(s.packets.length,s.source.length,label+': source representatives');
  assert.equal(K,s.warm.at+1);assert.equal(K,s.a);
  assert.equal(s.packets[0].point,s.a+1);
  assert.equal(s.g[s.a-1].length,2,label+': private root height');
  assert.equal(s.g[s.a-1][0],s.g[s.a-1][1],label+': private unit column');
  assert(Sparse.at(q,s.warm.at,s.a)>=2,label+': master port');
  assert(Sparse.at(q,s.warm.points[0],s.warm.at)>=6,label+': master bank');
  assert.equal(s.root.bank.at(-1),s.warm.at,label+': top bank/master share');
  const ends=[];
  for(const v of nodes) {
    if(v!==s.root)assert.deepEqual(ordinalWord(v.word),v.exp,label+': word represents exponent');
    assert(v.bank.every((p,i)=>p>=7&&p<s.a&&(!i||v.bank[i-1]<p)),label+': bank address order');
    if(v===s.root)templateCover(q,v.bank,v.high,label+' infinite template');
    else bankCover(q,v.bank,v.word,label+' bank '+v.id);
    for(const p of v.bank) {
      assert(Sparse.at(q,p,s.a)>=2,label+': all bank points callable');stats.ports++;
    }
    let base=v.base,previous=grade(s,v.base);
    for(const child of v.children) {
      assert(eq(child.base,base),label+': contiguous child intervals');
      assert(cmp(child.exp,v.exp)<0,label+': child exponent decreases');
      assert(previous<=child.bank[0],label+': child follows previous endpoint');
      assert(child.bank.at(-1)<v.bank[0],label+': all child banks before parent');
      base=end(child);previous=grade(s,base);
    }
    assert(cmp(base,end(v))<0,label+': children below parent endpoint');
    let prefix=[];
    for(const term of end(v))for(let k=0;k<term.coeff;k++) {
      grade(s,prefix);prefix=add(prefix,power(term.exp));
    }
    assert(s.byEnd.get(key(end(v)))===v,label+': endpoint map identity');
    ends.push({a:end(v),code:v.bank.at(-1)+1});
  }
  ends.sort((a,b)=>cmp(a.a,b.a));
  for(let i=1;i<ends.length;i++)assert(ends[i-1].code<ends[i].code,label+': all endpoint codes');
  const packetNodes=new Set(s.packets.flatMap(p=>Object.values(p).filter(Number.isInteger)));
  for(let j=0;j<s.packets.length;j++) {
    const p=s.packets[j],last=j===s.packets.length-1;
    assert.equal(p.g1,p.point+1);assert.equal(p.g2,p.point+2);
    if(p.g3!==null)assert.equal(p.g3,p.point+3);
    if(j)assert(s.packets[j-1].g2<p.point);
    Sparse.full(s.g,p.g1-1,p.point,K,label+': first guard');
    if(!last||!s.taxed)Sparse.full(s.g,p.g2-1,p.g1,K,label+': second guard');
    if(!last)Sparse.full(s.g,p.g3-1,p.g2,K,label+': third guard');
    assert(s.g[p.point-1].length<=K,label+': main height bound');
    if(s.g[p.point-1].length===K)assert(packetNodes.has(s.g[p.point-1][K-1]),label+': top parent type');
    assert(Sparse.at(q,s.a,p.point)>=2,label+': main private port');
    for(const v of nodes)assert(Sparse.at(q,v.bank.at(-1),p.g1)>=2,label+': archive to main guard');
  }
  const E=endpoints(s.source),V=s.source.map(B.column_verticals),parents=B.parents(s.source,V);
  const pairs=[];
  for(let j=0;j<E.length;j++)for(let k=0;k<E[j].length;k++)pairs.push({e:E[j][k],v:V[j][k]});
  pairs.sort((a,b)=>cmp(a.e,b.e));
  for(let i=1;i<pairs.length;i++)assert.equal(Math.sign(B.vertical_compare(pairs[i-1].v,pairs[i].v)),
    cmp(pairs[i-1].e,pairs[i].e),label+': native vertical order');
  for(let j=0;j<s.source.length;j++) {
    assert.equal(E[j].length,parents[j].length);
    for(let k=0;k<E[j].length;k++) {
      const c=parents[j][k][0];assert(c>=0&&c<j);
      assert(Sparse.at(q,s.packets[c].point,s.packets[j].point)>=grade(s,E[j][k]),label+': native main parent');
      stats.mainSegments++;
    }
  }
  assert.equal(s.archive,s.active.node.bank[s.active.length-1]);
  assert.deepEqual(s.g.at(-1).slice(1),s.g[s.archive-1].slice(1),label+': restored archive tail');
  assert.equal(Sparse.at(q,s.a,N),1,label+': private work separation');
  assert(Sparse.at(q,s.packets.at(-1).g1,N)>=1,label+': work reload access');
  const active=activeBank(s);active[active.length-1]=N;
  if(s.active.node===s.root) {
    assert.equal(s.active.length,4,'whole infinite template stays active');
    templateCover(q,active,s.root.high,label+': active template');
  } else bankCover(q,active,s.active.node.word.slice(0,s.active.length-1),label+': active cover');
  if(N<=limits.nativeWidth)P.E.native(s.g.rle?Sparse.materialize(s.g.rle):s.g);
}
function templateCover(q,bank,high,label) {
  assert.equal(bank.length,4);
  const [r,u,v,e]=bank;
  assert(high>r && high<=u,label+': high internal capacity exceeds generator root');
  for(const p of [u,v,e])assert(Sparse.at(q,r,p)>=6,label+': root background');
  assert(Sparse.at(q,u,v)>=high,label+': high internal pair');
  assert(Sparse.at(q,u,e)>=3 && Sparse.at(q,v,e)>=3,label+': both pair points before archive');
  stats.bankPairs+=6;
}
let seedAudit;
function makeSeed(columns) {
  assert(Number.isInteger(columns)&&columns>=1&&columns<=8,'initial source width guard');
  let g=[[],[1],[2,2],[3,3,3],[2,2],[1]];
  const compress=g=>g.map(col=>col.flatMap((p,i)=>i+1===col.length||p!==col[i+1]
    ?[{a:p,x:nat(i+1)}]:[]));
  const cert=createCertifier(M,{tick,maxNodes:40000});
  let events=0;
  function move(after,event) {
    tick();assert(after.length<=limits.width,'seed width guard');
    assert(++events<=200,'seed event guard');
    cert.certify({...event,before:compress(g),after:compress(after)});g=after;
  }
  const s={get g(){return g;},
    fs(n){move(L.expand(g,n),{kind:'FS',n});},
    truncate(h) {
      assert(h>=1&&h<=g.at(-1).length);
      if(h!==g.at(-1).length)move(g.slice(0,-1).concat([g.at(-1).slice(0,h)]),
        {kind:'truncate',height:h});
    },
    down() {
      const col=g.at(-1),h=col.length,c=col.at(-1);assert(h>0);
      move(g.slice(0,-1).concat([col.slice(0,h-1).concat(g[c-1].slice(h-1))]),{kind:'down'});
    }};
  s.fs(1);s.fs(1);s.fs(3);
  P.prepare(s,7,3);s.fs(1);P.trim(s,16);
  const commonSeed=g.map(col=>col.slice());
  s.fs(4*columns-1);
  assert.equal(s.g.length,14+4*columns);
  s.a=14;s.codes=[7,14];s.taxed=false;
  s.warm={at:13,points:[7,11,12,13]};
  s.packets=Array.from({length:columns},(_,i)=>({point:15+4*i,g1:16+4*i,g2:17+4*i,g3:18+4*i}));
  s.archive=13;P.E.restore(s,13);
  seedAudit={events,certificates:cert.stats,commonSeed,
    commonCounts:L.countResult(commonSeed).values.map(String),columns,index:4*columns-1,
    graph:g.map(col=>col.slice()),
    counts:L.countResult(g).values.map(String),
    path:'Q = W[1][1][3], expose(7,3), [1], trim(16); then [4*columns-1], restore(13,row2)'};
  return s;
}
function initialize(columns=2) {
  const s=makeSeed(columns),base=B.from_display('()(1^()(1)(2)(3))');
  s.source=[[],...Array.from({length:columns-1},(_,j)=>[[j+1,clone(base[1][0][1])]])];
  const exp=clone(rowOrdinal(base[1][0][1])[0].exp);
  s.root={id:0,base:[],exp,word:null,bank:[7,11,12,13],high:10,children:[]};
  assert(eq(exp,power(power(nat(1)))),'infinite template means exponent omega^omega');
  s.byEnd=new Map([[key(end(s.root)),s.root]]);
  s.path=[];s.allocationTrace=[];bindActive(s,s.root);
  check(s,'fixed amplified seed initialization');
  if(!process.argv.includes('--dense'))Sparse.attach(s,P,limits);
  return s;
}
function sourceForWord(w) {
  const depths=[0];
  for(const d of w) {depths.push(1);for(let k=0;k<d;k++)depths.push(2);}
  const h=depths.map(d=>d?[[d,B.ONE()]]:[]);
  assert(eq(rowOrdinal(h),power(ordinalWord(w))),'local one-row label decoding');
  return [[],[[1,h]]];
}
function activate(s,v) {
  check(s,'before activation');assert(!s.taxed,'one activation per source step');
  const e=v.bank.at(-1),K=s.codes.at(-1),z=s.packets.at(-1).g2;
  P.trim(s,z);
  for(let i=0;i<limits.navigation;i++) {
    s.truncate(K);const c=s.g.at(-1).at(-1);
    if(s.g[c-1].length<K)break;
    s.down();stats.topDowns++;
    assert(i+1<limits.navigation,'master navigation guard');
  }
  s.truncate(K);const c=s.g.at(-1).at(-1);
  assert(s.packets.some(p=>p.point===c),'activation terminates at a main point');
  assert(z-1+3*(z-c)<=limits.width,'activation helper width guard');
  s.fs(3);P.trim(s,z+2);
  P.prepare(s,e,2);const N=s.g.length,D=N-e;
  assert(N-1+D<=limits.width,'activation copy width guard');
  s.fs(1);transport(s,e,D);s.packets.at(-1).g3=null;s.taxed=true;
  restore(s,v,v.bank.length);stats.activations++;check(s,'after activation');
}
function allocate(s,v,exp,count) {
  if(v===s.root)return allocateInfinite(s,exp,count);
  const target=word(exp),oldWord=v.word;
  assert(cmp(exp,v.exp)<0&&count>=1&&Number.isSafeInteger(count));
  assert(allNodes(s.root).length+count<=limits.nodes,'new node guard');
  const trace={sourceStep:s.path.length,parent:v.id,parentWord:oldWord.slice(),
    word:target.slice(),count,oldChildren:v.children.length};
  let common=0;
  while(common<Math.min(oldWord.length,target.length)&&oldWord[common]===target[common])common++;
  const isPrefix=common===target.length;
  assert(isPrefix?target.length<oldWord.length:oldWord[common]>target[common]);
  if(s.taxed && s.active.node===v && s.active.length===v.bank.length) {
    stats.activeContinuations++;
  } else activate(s,v);
  if(!isPrefix&&common+2<v.bank.length) {
    // Every prefix archive has a low port; read it from the currently active
    // bank, without obtaining a new main spare or changing any stored bank.
    restore(s,v,common+2);stats.prefixRestores++;
    check(s,'after prefix restore');
  }
  const bank=v.bank.slice(),r=bank[0],N=s.g.length,D=N-r,t=s.a+2;
  const tail=isPrefix?0:target.length-common;
  const blocksPerChild=isPrefix?1:tail+1;
  const blocks=count*blocksPerChild;
  const row=isPrefix?4:4+oldWord[common];
  assert(N-1+(blocks+1)*D<=limits.width,'graded allocation width guard');
  P.prepare(s,r,row);s.fs(blocks+1);transport(s,r,blocks*D);
  let base=v.children.at(-1)?end(v.children.at(-1)):v.base;
  for(let i=0;i<count;i++) {
    const offset=i*blocksPerChild;
    const points=isPrefix?bank.slice(0,target.length+1).map(p=>p+offset*D):
      bank.slice(0,common+1).map(p=>p+offset*D).concat(
        Array.from({length:tail},(_,j)=>r+(offset+j+1)*D));
    const child={id:s.byEnd.size,base:clone(base),exp:clone(exp),word:target.slice(),bank:points,children:[]};
    assert(!s.byEnd.has(key(end(child))),'new endpoint is fresh');
    v.children.push(child);s.byEnd.set(key(end(child)),child);base=end(child);
  }
  P.trim(s,t+(blocks+1)*D);
  const child=v.children.at(-1);restore(s,child,child.bank.length);
  stats.allocations++;stats[isPrefix?'prefixChildren':'tailSplits']+=count;
  s.allocationTrace.push({...trace,common,isPrefix,tail,row,blocks,width:s.g.length});
  check(s,'after graded allocation');
}
function allocateInfinite(s,exp,count) {
  const target=word(exp);
  assert(Number.isSafeInteger(count)&&count>=1);
  if(target.length!==1) {
    // A larger finite interval is inserted first, then its ACTIVE resource
    // refines directly. There is no second paid return or target reset.
    const high=ordinalWord([target.length?target[0]+1:0]);
    allocateInfinite(s,high,1);
    const temp=s.root.children.at(-1);
    allocate(s,temp,exp,count);return;
  }
  const degree=target[0],v=s.root;
  assert(allNodes(v).length+count<=limits.nodes,'template node guard');
  activate(s,v);
  const [r,u,w,e]=v.bank,H=v.high,N=s.g.length,D=N-r,t=s.a+2;
  const first=Math.max(0,Math.ceil((4+degree-H)/D)),blocks=first+count;
  assert(N-1+(blocks+1)*D<=limits.width,'template amplification width guard');
  const trace={sourceStep:s.path.length,parent:v.id,template:true,degree,count,
    oldChildren:v.children.length,root:r,pair:[u,w],oldHigh:H,span:D,first,blocks};
  P.prepare(s,r,6);s.fs(blocks+1);transport(s,r,blocks*D);
  let base=v.children.at(-1)?end(v.children.at(-1)):v.base;
  for(let i=0;i<count;i++) {
    const offset=first+i,points=[u+offset*D,w+offset*D];
    const child={id:s.byEnd.size,base:clone(base),exp:clone(exp),word:[degree],bank:points,children:[]};
    assert(!s.byEnd.has(key(end(child))),'fresh finite template endpoint');
    v.children.push(child);s.byEnd.set(key(end(child)),child);base=end(child);
  }
  P.trim(s,t+(blocks+1)*D);
  const child=v.children.at(-1);restore(s,child,child.bank.length);
  stats.allocations++;stats.templateAllocations++;if(first)stats.templateAmplifications++;
  s.allocationTrace.push({...trace,width:s.g.length});
  check(s,'after template allocation');
}
function ensure(s,a) {
  if(!a.length||s.byEnd.has(key(a))){grade(s,a);return;}
  let v=s.root;
  for(;;) {
    assert(cmp(v.base,a)<0&&cmp(a,end(v))<0,'requested point is internal');
    const child=v.children.find(c=>cmp(a,end(c))<=0);
    if(!child)break;v=child;
  }
  const base=v.children.at(-1)?end(v.children.at(-1)):v.base;
  const diff=M.debug.ordRightDiff(base,a);
  assert.equal(diff.length,1,'one new exponent at the main dictionary level');
  allocate(s,v,clone(diff[0].exp),diff[0].coeff);
  assert(eq(end(v.children.at(-1)),a),'allocation reaches requested point');
}
function payLimitMain(s,alphaNew,sourceParent) {
  const last=s.packets.at(-1),point=s.packets[sourceParent].point;
  P.trim(s,last.point);P.prepare(s,point,grade(s,alphaNew)+1);
  assert(last.point-point>=4,'healthy source cut packet');
  s.fs(1);P.trim(s,last.point+3);
  last.g1=last.point+1;last.g2=last.point+2;last.g3=last.point+3;
  s.taxed=false;restore(s);
}
function initializeLocal(w) {
  // A separately labelled local-contract experiment, not an assertion that
  // the artificial source switch below is one native TBMS step. The TARGET
  // starts from the same standard G and every target operation is genuine.
  const s=initialize(),exp=ordinalWord(w);
  assert(cmp(exp,s.root.exp)<0,'local word is below the root');
  allocate(s,s.root,exp,1);
  const child=s.byEnd.get(key(power(exp)));assert(child,'local target endpoint');
  payLimitMain(s,end(child),0);
  s.source=sourceForWord(w);s.localContractInitialization=true;
  check(s,'local contract initialization');return {s,node:child};
}
function reload(s) {
  P.prepare(s,s.packets.at(-1).g1,1,true);
  Sparse.full(s.g,s.g.length-1,s.packets.at(-1).point,s.codes.at(-1),'full main reload');
}
function step(s,n) {
  assert(Number.isInteger(n)&&n>=0&&n<=limits.index,'source index guard');
  check(s,'before source step');assert(s.source.length,'nonempty source');
  const old=s.source,next=sourceFS(old,n),col=old.at(-1);
  const kind=!col.length?'delete':B.is_one(col.at(-1)[1])?'unit':'limit';
  stats.sourceSteps++;
  if(kind==='delete'||(kind==='unit'&&!n)) {
    if(next.length) {
      P.trim(s,s.packets.at(-2).g3);s.packets.pop();s.taxed=false;restore(s);
    } else {s.fs(0);s.packets=[];}
    stats.deletes++;
  } else {
    const x=old.length-1,parents=B.parents(old,old.map(B.column_verticals));
    const c=parents[x].at(-1)[0],E=endpoints(old),alpha=E[x].at(-1);
    if(kind==='limit') {
      const En=endpoints(next),alphaNew=En[x].at(-1),beforeAlloc=stats.allocations;
      const beta=E[x].at(-2)??[];
      assert(eq(alphaNew,add(beta,M.debug.ordFS(rowOrdinal(col.at(-1)[1]),n+1))),
        'native label FS matches one-row CNF');
      ensure(s,alphaNew);
      assert(stats.allocations-beforeAlloc<=2,'at most two forward allocations per source step');
      for(const a of En[x])grade(s,a);
      assert(grade(s,alphaNew)<grade(s,alpha),'strict new endpoint code');
      const Pn=B.parents(next,next.map(B.column_verticals));
      for(const parent of Pn[x].slice(col.length-1))assert.equal(parent[0],c,'unchanged native limit parent');
      payLimitMain(s,alphaNew,c);stats.limits++;
    } else {
      const beta=E[x].at(-2)??[],row=grade(s,beta)+1;
      assert(row<=grade(s,alpha),'unit threshold');
      const oldEnds=new Set(E.flat().map(key));
      for(const a of endpoints(next).flat())assert(oldEnds.has(key(a)),'unit step does not add endpoints');
      reload(s);const packets=s.packets.map(p=>({...p})),point=packets[c].point;
      P.prepare(s,point,row);const N=s.g.length,D=N-point;
      assert(N-1+n*D<=limits.width,'main unit width guard');s.fs(n);
      s.packets=packets.slice(0,-1);
      for(let i=1;i<=n;i++)for(const p of packets.slice(c,-1))
        s.packets.push(Object.fromEntries(Object.entries(p).map(([k,v])=>[k,v+i*D])));
      P.trim(s,s.packets.at(-1).g3);s.taxed=false;restore(s);stats.units++;
    }
  }
  s.source=next;s.path.push(n);check(s,'after source step');return !!next.length;
}
function report(s) {
  return {path:s.path,source:B.display(s.source),width:s.g.length,master:s.codes.at(-1),seedAudit,
    nodes:allNodes(s.root).map(v=>({id:v.id,word:v.word,base:v.base,bank:v.bank,
      end:end(v),code:v.bank.at(-1)+1})),allocationTrace:s.allocationTrace,stats,
    sparseStats:s.sparseStats,limits,elapsedMs:Date.now()-started,
    rssMiB:process.memoryUsage().rss/2**20};
}
module.exports={initialize,step,check,ensure,allocate,activate,report,limits,stats,
  P,B,M,cmp,eq,key,word,ordinalWord,endpoints,grade,allNodes,end,initializeLocal,sourceForWord,sourceFS};
if(require.main===module) {
  let s;
  try {
    const path=(process.argv[2]??'0,0,0,0,1,0,0').split(',').filter(Boolean).map(Number);
    s=initialize();
    for(const n of path)if(!step(s,n))break;
    console.log(JSON.stringify({status:'bounded checks passed; not by itself a proof',...report(s)},null,2));
  } catch(error) {
    console.log(JSON.stringify({status:'failed or guarded',error:error.message,stack:error.stack,
      ...(s?report(s):{stats,limits,elapsedMs:Date.now()-started})},null,2));
    process.exitCode=1;
  }
}


