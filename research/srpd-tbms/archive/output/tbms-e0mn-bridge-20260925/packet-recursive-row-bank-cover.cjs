'use strict';

// Bounded multi-level research prototype. The all-future PAPER argument is in
// RECURSIVE-ENDPOINT-CLOSURE and RECURSIVE-ROW-BANK-BOUND; tests are not that proof.
// Uses native recursive row graphs and explicitly paid initialization.
// A row endpoint is its actual BMS/TBMS graph,
// not an assigned epsilon/CNF ordinal. All source and target rules unchanged.
// Smaller endpoint banks may stay in the old prefix while larger ones use
// later copies. Main row codes need subcovariance, not equality.
const assert=require('node:assert/strict');
const Initial=require('./packet-amplified-resource-cover.cjs');
const Sparse=require('./packet-sparse-native-state.cjs');
const Cap=require('./finite-parent-capacity.cjs');
const {P,B}=Initial,started=Date.now(),limits=Initial.limits;
Object.assign(limits,{ms:20000,width:50000,downTransientWidth:100000,events:200000,
  navigation:1800,steps:30,sourceWidth:22,rows:400,rowWidth:80,routeSteps:160,plan:80,nodes:160,index:32});
Object.assign(P.limits,limits);Object.assign(P.E.limits,limits,{restore:limits.navigation});
const key=JSON.stringify,copy=x=>JSON.parse(key(x));
const native=require('./load-tbm.cjs').loadTBM();
const stats={checks:0,pairs:0,ports:0,sourceSteps:0,budgets:0,maxBudget:0,calls:0,
  allocations:0,ordinaryRowSteps:0,deletedRowSteps:0,keptSmallerBanks:0,
  strictSubcovariances:0,topDowns:0,maxWidth:0,maxNodes:0,mainUnits:0,mainLimits:0,mainDeletes:0};
function tick() {
  P.tick();assert(Date.now()-started<limits.ms,'native row-bank time guard');
  assert(process.memoryUsage().rss<650*2**20,'native row-bank RSS guard');
  assert(stats.pairs<5000000&&stats.ports<5000000,'row-bank pair/port guard');
}
function fs(expr,n) {tick();native.context.expr=expr;native.context.n=n;return copy(native.run('B.TBM.FS(expr,n)',1000));}
const cmp=(a,b)=>Math.sign(B.compare(a,b)),eq=(a,b)=>cmp(a,b)===0;
const prefix=(a,b)=>a.length<=b.length&&eq(a,b.slice(0,a.length));
function rowGraph(a) {
  assert(a.length<=limits.rowWidth,'row width guard');
  for(const c of a)assert(c.length<=limits.rows&&c.every(e=>B.is_one(e[1])),'ordinary bounded-row BMS only');
  return Array.from(B.parents(a,a.map(B.column_verticals)),c=>Array.from(c,e=>e[0]+1));
}
const ends=source=>Array.from(source,col=>Array.from(B.column_verticals(col),v=>copy(v.flat())));
const all=s=>s.levels.flatMap(l=>Array.from(l.dict.values()));
const grade=(s,a,level=s.levels.length-1)=>!a.length?7:
  (assert(s.levels[level].dict.has(key(a)),'registered level '+level+' endpoint '+B.display(a)),
  s.levels[level].dict.get(key(a)).points.at(-1)+1);
const lowerGrade=(s,level,a)=>!a.length?0:level===0?a.length:grade(s,a,level-1);
function capProfile(word) {
  assert(word.length<=limits.rowWidth);
  const V=word.map(B.column_verticals),P=B.parents(word,V),cuts=new Map([[key([]),[]]]);
  for(let j=0;j<word.length;j++){
    assert.equal(P[j].length,word[j].length);
    for(const v of V[j])cuts.set(key(v),v);
  }
  const positions=[...cuts.values()].sort(B.vertical_compare);
  const result=word.map(()=>word.map(()=>[]));
  for(let j=0;j<word.length;j++){
    let previous=null;
    for(let k=0;k+1<positions.length;k++){
      tick();const pos=positions[k],end=copy(positions[k+1].flat()),anc=new Set();
      let q=j;
      for(let n=0;n<word.length;n++){
        const z=B.index_after(V[q],pos);
        if(z>=word[q].length)break;
        const p=P[q][z][0];assert(p>=0&&p<q);
        anc.add(p);result[p][j]=end;q=p;
      }
      if(previous)for(const p of anc)assert(previous.has(p),'native nested ancestor forests');
      previous=anc;
    }
  }
  return result;
}
function makeBank(s,level,word,points){
  return {id:s.nextId++,level,word:copy(word),points,
    ...(level===0?{graph:rowGraph(word)}:{profile:capProfile(word)})};
}
function bankNeeds(s,v){
  if(v.kind==='ceiling')return null;
  const C=v.level===0?Cap.capacities(v.graph):null;
  return v.points.map((_,i)=>v.points.map((_,j)=>i<j
    ?3+(C?Cap.at(C,i+1,j+1):lowerGrade(s,v.level,v.profile[i][j])):0));
}
const movePacket=(p,f)=>Object.fromEntries(Object.entries(p).map(([k,v])=>[k,f(v)]));
function restore(s,v=s.active) {s.active=v;s.archive=v.points.at(-1);P.E.restore(s,s.archive);}
function transport(s,cut,delta,pivot=null) {
  const move=p=>p>=cut?p+delta:p,f=q=>q>cut?q+delta:q;
  const before=all(s).map(v=>({v,q:grade(s,v.word,v.level),points:v.points.slice()}));
  s.a=move(s.a);s.K=f(s.K);s.codes=[7,s.K];
  s.packets=s.packets.map(p=>movePacket(p,move));s.slots=s.slots.map(move);
  for(const {v,q,points} of before) {
    const keep=pivot&&v.level===pivot.level&&cmp(v.word,pivot.word)<0;
    v.points=keep?points:points.map(move);
    const after=grade(s,v.word,v.level);assert(after<=f(q),'main grade subcovariance');
    if(after<f(q))stats.strictSubcovariances++;
    if(keep)stats.keptSmallerBanks++;
    if(v.kind==='ceiling'&&!keep&&v.high>cut)v.high+=delta;
  }
}
function check(s,label='state') {
  tick();stats.checks++;
  const N=s.g.length,q=Sparse.capacities(s.g),C=(p,j)=>Sparse.at(q,p,j),banks=all(s);
  stats.maxWidth=Math.max(stats.maxWidth,N);stats.maxNodes=Math.max(stats.maxNodes,banks.length);
  assert(N<=limits.width&&banks.length<=limits.nodes,'recursive row-bank state guard');
  if(!s.source.length)return;
  assert.equal(s.K,s.root.points.at(-1)+1);assert.equal(s.a,s.K);
  assert.equal(s.g[s.a-1].length,2);assert.equal(s.g[s.a-1][0],s.g[s.a-1][1]);
  let previousTop=null;
  for(const layer of s.levels){
    if(!layer.root)continue;
    const list=[...layer.dict.values()].sort((a,b)=>cmp(a.word,b.word));
    for(let i=1;i<list.length;i++)assert(list[i-1].points.at(-1)+2<=list[i].points.at(-1),'within-layer archive order');
    for(const v of list){
      if(previousTop)assert(previousTop.points.at(-1)+4<=v.points[0],'whole layer separation');
      if(v.kind==='ceiling'){
        const [r,u,w,e]=v.points;assert(v.high>r&&v.high<=u);
        assert(v.background>=3&&v.background<=s.seedAudit.background,'fixed initial background bound');
        assert(C(r,u)>=v.background&&C(r,w)>=v.background&&C(r,e)>=v.background);
        assert(C(u,w)>=v.high&&C(u,e)>=3&&C(w,e)>=3,'recursive ceiling template');
        for(const z of list)if(z!==v)assert(z.points.at(-1)+2<=r,'all finite banks before their own ceiling');
      }else assert.equal(v.points.length,v.word.length);
      const need=bankNeeds(s,v);
      for(let j=0;j<v.points.length;j++){
        const p=v.points[j];assert(p>=s.seedAudit.r&&p<s.a&&(!j||v.points[j-1]<p));
        assert(C(p,s.a)>=2,label+': private bank port');stats.ports++;
        if(need)for(let i=0;i<j;i++){
          assert(C(v.points[i],p)>=need[i][j],label+': level '+v.level+' complete bank cover '+v.id+' '+i+','+j+' actual '+C(v.points[i],p)+' need '+need[i][j]);stats.pairs++;
        }
      }
    }
    previousTop=layer.root;
  }
  assert.equal(s.packets.length,s.source.length);assert.equal(s.packets[0].point,s.a+1);
  const packetNodes=new Set(s.packets.flatMap(p=>Object.values(p)));
  for(let i=0;i<s.packets.length;i++) {
    const p=s.packets[i],last=i===s.packets.length-1;
    assert(p.g1===p.point+1&&p.g2===p.point+2&&p.g3===p.point+3);
    if(i)assert(s.packets[i-1].g3<p.point);
    Sparse.full(s.g,p.g1-1,p.point,s.K,'first main guard');
    if(!last||s.phase==='cold')Sparse.full(s.g,p.g2-1,p.g1,s.K,'second main guard');
    if(!last)Sparse.full(s.g,p.g3-1,p.g2,s.K,'nonlast work guard');
    assert(s.g[p.point-1].length<=s.K);
    if(s.g[p.point-1].length===s.K)assert(packetNodes.has(s.g[p.point-1][s.K-1]));
    assert(C(s.a,p.point)>=2,'main point private port');
  }
  if(s.phase==='cold')assert.equal(s.slots.length,0);
  const first=s.packets.at(-1).g1;
  for(let i=0;i<s.slots.length;i++) {
    const z=s.slots[i];assert(z-1>first&&z<N&&(!i||s.slots[i-1]+2<=z));
    for(const t of [z-1,z]) {
      assert(C(s.a,t)>=2&&C(first,t)>=1,'coupon main/private ports');
      for(const v of banks) {assert(C(v.points.at(-1),t)>=2,'coupon all archive ports');stats.ports++;}
    }
  }
  const E=ends(s.source),V=s.source.map(B.column_verticals),parents=B.parents(s.source,V);
  const pairs=[];
  for(let j=0;j<E.length;j++)for(let k=0;k<E[j].length;k++)pairs.push({a:E[j][k],v:V[j][k]});
  for(const a of pairs)for(const b of pairs)assert.equal(cmp(a.a,b.a),Math.sign(B.vertical_compare(a.v,b.v)),'flattened endpoint order');
  for(let j=0;j<E.length;j++)for(let k=0;k<E[j].length;k++) {
    const p=parents[j][k][0];assert(p>=0&&p<j);
    assert(C(s.packets[p].point,s.packets[j].point)>=grade(s,E[j][k]),label+': source main parent');
  }
  assert.equal(s.archive,s.active.points.at(-1));
  assert.deepEqual(s.g.at(-1).slice(1),s.g[s.archive-1].slice(1),'active archive inherited tail');
  assert(C(s.a,N)===1&&C(first,N)>=1,'work separation and main reload port');
  const bank=s.active.points.slice();bank[bank.length-1]=N;
  if(s.active.kind==='ceiling'){
    const [r,u,v]=bank;
    assert(C(r,N)>=s.active.background&&C(u,N)>=3&&C(v,N)>=3,'active recursive template tail');
  }else{
    const need=bankNeeds(s,s.active);
    for(let j=1;j<bank.length;j++)for(let i=0;i<j;i++){
      assert(C(bank[i],bank[j])>=need[i][j],'active recursive full bank cover');stats.pairs++;
    }
  }
}
function initialize(columns=2,levelCount=2) {
  assert(Number.isInteger(levelCount)&&levelCount>=1&&levelCount<=5);
  limits.rows=400;
  const seedColumns=columns+(levelCount>1?1:0);
  const s=require('./native-row-bank-seed.cjs').makeSeed(P,Initial.M,Sparse,limits,seedColumns,Math.max(3,levelCount-1),tick);
  const r=s.seedAudit.r,level=levelCount-1;
  s.nextId=1;s.mode='recursive';s.levels=Array.from({length:levelCount},(_,l)=>({level:l,dict:new Map(),root:null}));
  s.rowRoot=copy(B.infinity_FS(level+2));s.J=[[],[[1,copy(s.rowRoot)],[1,B.ONE()]]];
  s.source=fs(s.J,seedColumns-1);
  s.root={id:0,level,kind:'ceiling',word:s.rowRoot,points:[r,r+4,r+5,r+6],high:r+3,background:r-1};
  s.levels[level].root=s.root;s.levels[level].dict.set(key(s.rowRoot),s.root);
  s.active=s.root;s.archive=r+6;s.K=r+7;s.slots=[];s.phase='cold';s.path=[];s.trace=[];
  check(s,'pre-simulation seed');
  if(levelCount>1){
    prepareBudget(s,levelCount-1);
    for(let l=level-1;l>=0;l--)cloneInitialLayer(s,s.levels[l+1].root,l);
    assert.equal(s.slots.length,0);
    // These are paid TARGET initialization steps. The actual source
    // simulation begins only after the spare last packet has been removed.
    s.packets.pop();P.trim(s,s.packets.at(-1).g3);
    s.source=fs(s.J,columns-1);s.phase='cold';restore(s,s.root);
  }
  s.initializationTrace=s.trace.slice();s.trace=[];
  check(s,'recursive simulation initial state');return s;
}
function cloneInitialLayer(s,parent,level){
  assert(!s.levels[level].root&&parent.level===level+1&&parent.background>=4);
  activate(s,parent);
  const [r,u,v]=parent.points,H=parent.high,bg=parent.background,N=s.g.length,D=N-r,t=s.a+2;
  assert(N-1+3*D<=limits.width,'initial recursive clone width guard');
  P.prepare(s,r,bg);s.fs(3);transport(s,r,2*D);
  const root={id:s.nextId++,level,kind:'ceiling',word:copy(B.infinity_FS(level+2)),points:[r,u,v,N],high:H,background:bg-1};
  s.levels[level].root=root;s.levels[level].dict.set(key(root.word),root);
  P.trim(s,t+3*D);restore(s,root);
  stats.initialClones=(stats.initialClones??0)+1;s.trace.push({kind:'initial-layer',level,background:bg-1,width:s.g.length});
  check(s,'paid initial lower layer clone');return root;
}
function prepareBudget(s,count) {
  check(s,'before coupon preparation');assert(s.phase==='cold'&&count>=1&&count<=limits.plan);
  const z=s.packets.at(-1).g2,K=s.K;P.trim(s,z);
  for(let i=0;i<limits.navigation;i++) {
    s.truncate(K);const c=s.g.at(-1).at(-1);
    if(s.g[c-1].length<K)break;
    s.down();stats.topDowns++;assert(i+1<limits.navigation);
  }
  s.truncate(K);const c=s.g.at(-1).at(-1),D=z-c;
  assert(s.packets.some(p=>p.point===c)&&D>=2);
  assert(z-1+(count+1)*D<=limits.width,'coupon width guard');s.fs(count+1);
  s.slots=Array.from({length:count},(_,i)=>z+(i+1)*D);s.phase='budget';restore(s);
  stats.budgets++;stats.maxBudget=Math.max(stats.maxBudget,count);
  s.trace.push({kind:'budget',count,width:s.g.length});check(s,'after coupon preparation');
}
function activate(s,v) {
  check(s,'before bank call');assert(s.phase==='budget'&&s.slots.length);
  const z=s.slots.pop(),e=v.points.at(-1);P.trim(s,z);P.prepare(s,e,2);
  const D=z-e;assert(z-1+D<=limits.width,'bank call width guard');s.fs(1);transport(s,e,D);
  restore(s,v);stats.calls++;check(s,'after bank call');
}
function allocateStep(s,parent,n,expected=null){
  assert(parent.kind!=='ceiling');
  const level=parent.level,next=fs(parent.word,n),dict=s.levels[level].dict;
  assert(next.length&&cmp(next,parent.word)<0);
  if(expected)assert(eq(next,expected));
  assert(!dict.has(key(next)));
  for(const v of dict.values())assert(!(cmp(next,v.word)<0&&cmp(v.word,parent.word)<0),'nearest upper within same level');
  if(level>0)for(const a of ends(next).flat())lowerGrade(s,level,a);
  const word=copy(parent.word),oldPoints=parent.points.slice();
  const V=word.map(B.column_verticals),parents=B.parents(word,V),col=word.at(-1);
  activate(s,parent);
  const points=parent.points.slice(),N=s.g.length,t=s.a+2;
  let cut,row,blocks,childPoints,kind;
  if(!col.length||B.is_one(col.at(-1)[1])&&!n){
    cut=points.at(-2);row=3;blocks=2;childPoints=points.slice(0,-2).concat(N);
    kind='delete';stats.deletedRowSteps++;
  }else if(!B.is_one(col.at(-1)[1])){
    const a=ends(next).at(-1).at(-1),c=parents.at(-1).at(-1)[0];
    cut=points[c];row=3+lowerGrade(s,level,a)+1;blocks=2;
    childPoints=points.slice(0,-1).concat(N);kind='limit';
    stats.recursiveRowLimits=(stats.recursiveRowLimits??0)+1;
  }else{
    const c=parents.at(-1).at(-1)[0],E=ends(word).at(-1),beta=E.at(-2)??[];
    cut=points[c];row=3+lowerGrade(s,level,beta)+1;blocks=n+1;
    const D=N-cut;childPoints=points.slice(0,-1);
    for(let j=1;j<=n;j++)for(const p of points.slice(c,-1))childPoints.push(p+j*D);
    kind='unit';stats.ordinaryRowSteps++;
  }
  const D=N-cut;assert(childPoints.at(-1)>=N&&D>=2);
  assert(N-1+(blocks+1)*D<=limits.width,'recursive row allocation width guard');
  P.prepare(s,cut,row);s.fs(blocks+1);transport(s,cut,blocks*D,{level,word});
  const node=makeBank(s,level,next,childPoints);dict.set(key(next),node);
  P.trim(s,t+(blocks+1)*D);restore(s,node);stats.allocations++;
  s.trace.push({kind:'row-'+kind,level,parent:parent.id,node:node.id,n,row,cut,blocks,label:B.display(next),parentBefore:oldPoints,width:s.g.length});
  check(s,'recursive source row child');return node;
}
function allocateCeiling(s,level,n,expected=null){
  const layer=s.levels[level],word=fs(layer.root.word,n);
  if(expected)assert(eq(word,expected));
  assert(word.length===2&&word[0].length===0);
  const E=ends(word).at(-1),alpha=E.at(-1);
  for(const a of E)lowerGrade(s,level,a);
  for(const v of layer.dict.values())if(v!==layer.root)assert(cmp(v.word,word)<0);
  activate(s,layer.root);
  const [r,u,v]=layer.root.points,H=layer.root.high,bg=layer.root.background,N=s.g.length,D=N-r,t=s.a+2;
  const needed=3+lowerGrade(s,level,alpha),m=Math.max(0,Math.ceil((needed-H)/D)),blocks=m+1;
  if(level>0)assert.equal(m,0,'lower whole layer already lies before higher internal demand');
  assert(N-1+(blocks+1)*D<=limits.width,'recursive ceiling allocation width guard');
  const points=[u+m*D,v+m*D];
  P.prepare(s,r,bg);s.fs(blocks+1);transport(s,r,blocks*D);
  const node=makeBank(s,level,word,points);layer.dict.set(key(word),node);
  P.trim(s,t+(blocks+1)*D);restore(s,node);stats.allocations++;
  stats.ceilingAllocations=(stats.ceilingAllocations??0)+1;
  s.trace.push({kind:'ceiling',level,node:node.id,n,needed,childCopy:m,background:bg,width:s.g.length});
  check(s,'recursive layer ceiling allocation');return node;
}
function route(upper,target) {
  let current=copy(upper);const result=[];
  assert(cmp(current,target)>=0);
  for(let k=0;k<limits.routeSteps&&!eq(current,target);k++) {
    tick();let chosen=null;
    for(let n=0;n<=Math.min(limits.index,2+key(target).length);n++) {
      const child=fs(current,n);assert(cmp(child,current)<0);
      if(cmp(child,target)>=0) {chosen={n,child};break;}
      // Recursive children are not literal prefixes. No such early-stop inference.
    }
    assert(chosen,'target not located in this row descent cone');
    current=chosen.child;result.push({n:chosen.n,word:current});
    assert(result.length<=limits.plan,'row route plan guard');
  }
  assert(eq(current,target),'row route length guard');return result;
}
function plan(s,targets,level=s.levels.length-1){
  const words=s.levels.map(layer=>[...layer.dict.values()].map(v=>v.word)),ops=[];
  function ensure(level,targets){
    assert(level>=0);
    for(const target of targets.slice().sort((a,b)=>-cmp(a,b))){
      if(!target.length||words[level].some(a=>eq(a,target)))continue;
      let upper=words[level].filter(a=>cmp(a,target)>0).sort(cmp)[0];assert(upper,'recursive upper endpoint exists');
      if(eq(upper,s.levels[level].root.word)){
        let chosen=null;
        for(let n=0;n<=limits.index;n++){
          const word=fs(upper,n);
          if(cmp(word,target)>=0&&words[level].every(a=>eq(a,upper)||cmp(a,word)<0)){chosen={n,word};break;}
        }
        assert(chosen,'recursive finite ceiling index guard or non-cofinal target');
        if(level>0)ensure(level-1,ends(chosen.word).flat());
        words[level].push(chosen.word);ops.push({kind:'ceiling',level,...chosen});upper=chosen.word;
        if(eq(upper,target))continue;
      }
      let previous=upper;
      for(const op of route(upper,target)){
        assert(!words[level].some(a=>eq(a,op.word)));
        if(level>0)ensure(level-1,ends(op.word).flat());
        words[level].push(op.word);ops.push({level,parent:previous,n:op.n,word:op.word});previous=op.word;
        assert(ops.length<=limits.plan,'whole recursive plan guard');
      }
    }
  }
  ensure(level,targets);return ops;
}
function register(s,targets,level=s.levels.length-1){
  const ops=plan(s,targets,level);if(!ops.length)return;
  prepareBudget(s,ops.length);
  for(const op of ops){
    if(op.kind==='ceiling')allocateCeiling(s,op.level,op.n,op.word);
    else allocateStep(s,s.levels[op.level].dict.get(key(op.parent)),op.n,op.word);
  }
  assert.equal(s.slots.length,0);return ops;
}
function regenerateLimit(s,a,parent) {
  const last=s.packets.at(-1),cut=s.packets[parent].point;
  P.trim(s,last.point);P.prepare(s,cut,grade(s,a)+1);assert(last.point-cut>=4);
  s.fs(1);P.trim(s,last.g3);s.phase='cold';s.slots=[];restore(s);
}
function step(s,n) {
  assert(Number.isInteger(n)&&n>=0&&n<=limits.index);check(s,'before source step');
  assert(s.source.length&&s.phase==='cold');assert(s.path.length<limits.steps);
  const old=s.source,col=old.at(-1),next=fs(old,n);assert(next.length<=limits.sourceWidth);
  const kind=!col.length?'delete':B.is_one(col.at(-1)[1])?'unit':'limit';
  if(kind==='delete'||kind==='unit'&&!n) {
    if(next.length){P.trim(s,s.packets.at(-2).g3);s.packets.pop();restore(s);}
    else {s.fs(0);s.packets=[];}stats.mainDeletes++;
  } else {
    const x=old.length-1,E=ends(old),parents=B.parents(old,old.map(B.column_verticals));
    const parent=parents[x].at(-1)[0],alpha=E[x].at(-1);
    if(kind==='limit') {
      const En=ends(next),a=En[x].at(-1);assert(cmp(a,alpha)<0,'actual flattened endpoint strictly decreases');
      register(s,En[x]);for(const t of En[x])grade(s,t);assert(grade(s,a)<grade(s,alpha));
      const Pn=B.parents(next,next.map(B.column_verticals));
      for(const p of Pn[x].slice(col.length-1))assert.equal(p[0],parent);
      regenerateLimit(s,a,parent);stats.mainLimits++;
    } else {
      const beta=E[x].at(-2)??[],row=grade(s,beta)+1;assert(row<=grade(s,alpha));
      const known=new Set(E.flat().map(key));for(const t of ends(next).flat())assert(known.has(key(t)));
      P.prepare(s,s.packets.at(-1).g1,1,true);
      Sparse.full(s.g,s.g.length-1,s.packets.at(-1).point,s.K,'main reload');
      const packets=s.packets.map(p=>({...p})),cut=packets[parent].point;
      P.prepare(s,cut,row);const N=s.g.length,D=N-cut;
      assert(N-1+n*D<=limits.width,'main width guard');s.fs(n);
      s.packets=packets.slice(0,-1);
      for(let b=1;b<=n;b++)for(const p of packets.slice(parent,-1))s.packets.push(movePacket(p,j=>j+b*D));
      P.trim(s,s.packets.at(-1).g3);restore(s);stats.mainUnits++;
    }
  }
  s.source=next;s.path.push(n);stats.sourceSteps++;check(s,'after source step');return !!next.length;
}
function report(s) {
  const seed={...s.seedAudit};delete seed.commonSeed;delete seed.graph;
  return {path:s.path,source:B.display(s.source),width:s.g.length,phase:s.phase,slots:s.slots,
    rowRoot:B.display(s.rowRoot),mode:s.mode,seedAudit:seed,initializationTrace:s.initializationTrace,banks:all(s).map(v=>({id:v.id,level:v.level,kind:v.kind,background:v.background,label:B.display(v.word),points:v.points})),
    trace:s.trace,stats,sparseStats:s.sparseStats,limits,elapsedMs:Date.now()-started,rssMiB:process.memoryUsage().rss/2**20};
}
module.exports={initialize,step,register,plan,route,prepareBudget,allocateStep,allocateCeiling,activate,check,
  report,limits,stats,ends,grade,all,fs,B,P,Sparse,rowGraph,cmp,eq,key,cloneInitialLayer,lowerGrade,capProfile};
if(require.main===module) {
  let s,error=null;
  try {s=initialize(Number(process.argv[3]??2),Number(process.argv[4]??2));
    for(const n of (process.argv[2]??'0,0,0,0').split(',').filter(Boolean).map(Number))if(!step(s,n))break;
  }catch(e){error={message:e.message,stack:e.stack};process.exitCode=1;}
  console.log(JSON.stringify({status:error?'failed or guarded':'bounded CONDITIONAL recursive row-bank path passed',error,...(s?report(s):{stats,limits})},null,2));
}


