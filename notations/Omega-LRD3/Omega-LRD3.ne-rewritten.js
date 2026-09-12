/* Ω-LRD3 v0.1: self-indexed LRD, one-column prefix-nested top.
   Local packet {0,K[0]}; block b packet {0,K[0],...,K[b]}.
   Standalone NER file: no imports, network, or cross-task persistent caches.
   The well-ordering argument still depends on the unaudited LRD proof draft. */
(function(){
'use strict';
const TOP='Limit of Ω-LRD3';
const CAP={width:4096,depth:128,index:4096n,work:20000000,groups:1000000,
  graphs:100000,text:16000000,textWork:128000000,ms:1000};
const COUNT_CAP={work:300000000,nodes:800000,columnCells:2000000,traceCells:1000000,
  traceStates:100000,activeCells:1000000,keyChars:32000000,comparisons:100000};
let active=null;
function budget(maxWork=CAP.work){
  if(!active){
    const task={start:Date.now(),work:0,groups:0,textWork:0,graphs:new Map(),ids:new Map(),nextId:0,
      cache:new Map(),parsed:new Map(),inputChars:0};
    active=task;const clear=()=>{if(active===task)active=null;};
    if(typeof queueMicrotask==='function')queueMicrotask(clear);else Promise.resolve().then(clear);
  }
  const task=active,b={task,work:0,cache:task.cache};
  b.tick=()=>{task.work++;if(++b.work>maxWork||task.work>COUNT_CAP.work||
    (task.work%128===0&&Date.now()-task.start>CAP.ms))
      throw Error('Ω-LRD3：约 1 秒计算预算或工作量超限，未返回截断结果。');};
  b.id=g=>{let id=task.ids.get(g.key);if(id===undefined){
    if(task.nextId>=CAP.graphs)throw Error('Ω-LRD3：图标识缓存超限');id=task.nextId++;task.ids.set(g.key,id);}return id;};
  return b;
}
function guard(f){try{return f();}catch(e){if(e instanceof RangeError)
  throw Error('Ω-LRD3：递归或整数规模超限，未返回截断结果。');throw e;}}
function nat(x){if(typeof x==='number'&&!Number.isSafeInteger(x))throw Error('需要安全整数或 BigInt');
  if(!['number','bigint'].includes(typeof x))throw Error('指标须为非负整数');
  const n=BigInt(x);if(n<0n)throw Error('负指标');return n;}
const icmp=(a,b)=>a<b?-1:a>b?1:0;
function cmp(a,c,b){b.tick();if(a===c||a.key===c.key)return 0;
  for(let j=0;j<Math.min(a.cols.length,c.cols.length);j++){
    const x=a.cols[j],y=c.cols[j];for(let i=0;i<Math.min(x.length,y.length);i++){
      const d=icmp(x[i].p,y[i].p)||cmp(x[i].k,y[i].k,b)||icmp(x[i].q,y[i].q);if(d)return d;
    }const d=icmp(x.length,y.length);if(d)return d;
  }return icmp(a.cols.length,c.cols.length);
}
function make(cols,b){
  b.tick();if(cols.length>CAP.width)throw Error('Ω-LRD3：列数超限');let depth=0;
  const result=cols.map((col,j)=>{
    const m=new Map();for(const e of col){b.tick();
      if(!Number.isSafeInteger(e.p)||!Number.isSafeInteger(e.q)||e.q<0||e.q>e.p||e.p>=j)
        throw Error('必须满足 0≤根≤父列<子列');
      depth=Math.max(depth,e.k.depth+1);if(depth>CAP.depth)throw Error('Ω-LRD3：嵌套深度超限');
      const id=e.p+':'+b.id(e.k),old=m.get(id);if(!old||old.q<e.q)m.set(id,e);
    }
    b.task.groups+=m.size;if(b.task.groups>CAP.groups)throw Error('Ω-LRD3：关系组预算超限');
    return [...m.values()].sort((a,c)=>-(icmp(a.p,c.p)||cmp(a.k,c.k,b)||icmp(a.q,c.q)));
  });
  let estimated=result.length?2*result.length:1;
  for(const col of result){estimated+=Math.max(0,col.length-1);for(const e of col){
    b.tick();estimated+=(e.k.finite?String(e.k.cols.length).length:e.k.key.length+2)+String(e.p).length+String(e.q).length+4;
    if(estimated>CAP.text||b.task.textWork+estimated>CAP.textWork)throw Error('Ω-LRD3：完整表达式文本预算超限');
  }}
  const key=result.length?result.map(col=>'['+col.map(e=>'('+rowText(e.k)+','+e.p+','+e.q+')').join(',')+']').join(''):'∅';
  b.task.textWork+=key.length;if(key.length>CAP.text||b.task.textWork>CAP.textWork)throw Error('Ω-LRD3：完整表达式文本超限');
  const saved=b.task.graphs.get(key);if(saved)return saved;
  if(b.task.graphs.size>=CAP.graphs)throw Error('Ω-LRD3：图缓存超限');
  const out=Object.freeze({cols:Object.freeze(result.map(col=>Object.freeze(col.map(e=>Object.freeze({...e}))))),
    key,finite:result.every(c=>!c.length),depth});b.task.graphs.set(key,out);return out;
}
function integer(n,b){if(n>BigInt(CAP.width))throw Error('Ω-LRD3：有限行号的列数超限');
  return make(Array.from({length:Number(n)},()=>[]),b);}
const rowText=g=>g.finite?String(g.cols.length):'{'+g.key+'}';
function control(g,b){let best=null;for(const e of g.cols.at(-1)||[]){b.tick();
  if(!best||(cmp(e.k,best.k,b)||icmp(e.q,best.q)||icmp(e.p,best.p))>0)best=e;
}return best;}
function seed(d,b){const n=nat(d);if(n>BigInt(Math.min(CAP.width,CAP.depth+1)))throw Error('Ω-LRD3：起始式层数超限');
  let g=integer(0n,b);for(let i=0;i<Number(n);i++){
    const m=g.cols.length;
    // A_0=0, A_1=1; thereafter append ONE edge column, with no spacer.
    // Its row is the previous finite expression. A_(n+1)[0]=A_n.
    g=make(m?[...g.cols,[{k:g,p:m-1,q:m-1}]]:[[]],b);
  }return g;}
function packet(k,v,b){
  if(k.finite)return [];
  const zero=integer(0n,b),found=new Map([[zero.key,zero]]);
  for(let t=0;t<=v;t++){b.tick();const lower=step(k,BigInt(t),b);
    if(cmp(lower,k,b)>=0)throw Error('Ω-LRD3：行标下降检查失败');found.set(lower.key,lower);}
  return [...found.values()];
}
function step(g,index,b){
  b.tick();const n=nat(index);if(n>CAP.index)throw Error('Ω-LRD3：展开指标超限');
  const memoKey=b.id(g)+'@'+n,saved=b.cache.get(memoKey);if(saved)return saved;
  const m=g.cols.length,e=control(g,b);
  if(!m)return g;
  if(!n||!e)return make(g.cols.slice(0,-1),b);
  const x=m-1,c=e.p,L=x-c,N=Number(n),size=x+N*L;
  if(size>CAP.width)throw Error('Ω-LRD3：展开后列数超限');
  const cols=Array.from({length:size},()=>[]);
  for(let v=0;v<=N;v++){
    const f=i=>i<c?i:i+v*L;
    for(let j=0;j<x;j++)for(const a of g.cols[j]){b.tick();cols[f(j)].push({k:a.k,p:f(a.p),q:f(a.q)});}
    if(v===N)break;
    for(const a of g.cols[x]){b.tick();const d=cmp(a.k,e.k,b);
      const q=d<0?f(a.q):d===0?Math.min(f(a.q),f(e.q)-1):-1;
      if(q>=0)cols[x+v*L].push({k:a.k,p:f(a.p),q});
    }
    for(const k of packet(e.k,v,b)){b.tick();cols[x+v*L].push({k,p:f(c),q:f(c)});}
  }
  const out=make(cols,b);if(cmp(out,g,b)>=0)throw Error('Ω-LRD3：一步下降检查失败');
  if(b.cache.size<1024)b.cache.set(memoKey,out);return out;
}
function parse(raw,b){
  if(typeof raw!=='string'||raw.length>CAP.text)throw Error('Ω-LRD3：输入长度超限或类型错误');
  b.tick();const saved=b.task.parsed.get(raw);if(saved)return saved;
  const s=raw.replace(/\s/g,'');let i=0;
  const take=x=>{b.tick();if(s[i++]!==x)throw Error('格式错误：期待 '+x);};
  function num(){const start=i;let n=0n;while(i<s.length&&/\d/.test(s[i])){
    b.tick();n=n*10n+BigInt(s[i++]);if(n>CAP.index)throw Error('Ω-LRD3：输入整数超限');
  }if(start===i)throw Error('期待自然数');return n;}
  function expr(d){
    b.tick();if(d>CAP.depth)throw Error('Ω-LRD3：嵌套深度超限');let g;
    if(s[i]==='∅'){i++;g=integer(0n,b);}
    else if(/\d/.test(s[i]??''))g=integer(num(),b);
    else if(s[i]==='A'||s[i]==='T'){i++;g=seed(num(),b);}
    else if(s.slice(i,i+5)==='Limit'){
      if(d)throw Error('Ω-LRD3：外顶端不能用作行标；请写有限的 A_n');
      i+=5;take('[');const n=num();take(']');g=seed(n,b);
    }else{
      const cols=[];
      while(s[i]==='['&&!/\d/.test(s[i+1]??'')){
        if(cols.length>=CAP.width)throw Error('Ω-LRD3：列数超限');take('[');const col=[];
        if(s[i]!==']')for(;;){
          b.tick();take('(');let k;
          if(s[i]==='{'){take('{');k=expr(d+1);take('}');}else k=integer(num(),b);
          take(',');const p=num();take(',');const q=num();take(')');
          if(p>=BigInt(cols.length)||q>p)throw Error('必须满足 0≤根≤父列<子列');
          col.push({k,p:Number(p),q:Number(q)});if(col.length>CAP.groups)throw Error('Ω-LRD3：关系数量超限');
          if(s[i]!==',')break;take(',');
        }take(']');cols.push(col);
      }
      if(!cols.length)throw Error('请输入列列表、自然数或 A3[2][1]');g=make(cols,b);
    }
    let steps=0;while(s[i]==='['&&/\d/.test(s[i+1]??'')){
      if(++steps>4096)throw Error('Ω-LRD3：构造记录超限');take('[');const n=num();take(']');g=step(g,n,b);
    }return g;
  }
  const out=expr(0);if(i!==s.length)throw Error('表达式后有未识别的内容');
  if(b.task.parsed.size<64&&b.task.inputChars+raw.length<=32000000){b.task.parsed.set(raw,out);b.task.inputChars+=raw.length;}
  return out;
}
const isTop=raw=>typeof raw==='string'&&['Limit',TOP].includes(raw.trim());
const plain=raw=>guard(()=>isTop(raw)?TOP:parse(raw,budget()).key);
const esc=s=>s.replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;');
const tex=s=>s==='∅'?'\\varnothing':s===TOP?'\\text{Limit of }\\Omega\\text{-LRD3}':'\\text{'+s.replace(/[{}]/g,'\\$&')+'}';
const list={name:'列表',plain,html:raw=>'<span style="font-family:inherit;white-space:nowrap">'+esc(plain(raw))+'</span>',
  latex:raw=>tex(plain(raw)),from_display:plain};
const fs=(raw,n)=>guard(()=>{const b=budget();return (isTop(raw)?seed(n,b):step(parse(raw,b),n,b)).key;});

// Exact local counts. The original recursive engine is kept only for audits.
function countsLegacy(g,b,options={}){
  let work=0,cells=0;const maxWork=Math.min(options.maxWork??30000000,30000000);
  const tick=()=>{b.tick();if(++work>maxWork)throw Error('Ω-LRD3：计数工作量超限');};
  const rowIds=new Map(),packets=new Map();let nextId=0;
  const rowId=k=>{let id=rowIds.get(k.key);if(id===undefined){if(nextId>=65536)throw Error('Ω-LRD3：计数行号缓存超限');id=nextId++;rowIds.set(k.key,id);}return id;};
  const pairId=e=>rowId(e.k)+','+e.q,priority=(a,c)=>cmp(a.k,c.k,b)||icmp(a.q,c.q);
  function put(map,e){tick();const id=pairId(e),old=map.get(id);if(!old||e.p>old.p)map.set(id,e);}
  const profiles=g.cols.map(col=>{const map=new Map();for(const e of col)for(let q=0;q<=e.q;q++)put(map,{k:e.k,p:e.p,q});return map;});
  const memo=new Map();
  function norm(c,cut,depth){
    tick();if(depth>512)throw Error('Ω-LRD3：计数递归栈超限');
    const id=c+':'+(cut?pairId(cut):'all'),saved=memo.get(id);if(saved)return saved;
    const active=new Map(profiles[c]);let steps=0n;
    for(;;){let top=null;for(const e of active.values()){tick();if(!top||priority(e,top)>0)top=e;}
      if(!top||(cut&&priority(top,cut)<0))break;
      active.delete(pairId(top));const sub=norm(top.p,top,depth+1);steps+=1n+sub.steps;
      for(const e of sub.rest.values())put(active,e);
      const rid=rowId(top.k);let pk=packets.get(rid);if(!pk){pk=packet(top.k,0,b);packets.set(rid,pk);}
      for(const k of pk)for(let q=0;q<=top.p;q++)put(active,{k,q,p:top.p});
    }
    cells+=active.size;if(cells>2000000||memo.size>=65536)throw Error('Ω-LRD3：计数缓存超限');
    const result={steps,rest:active};memo.set(id,result);return result;
  }
  return profiles.map((_,j)=>norm(j,null,0).steps+1n);
}

// All row graphs share exact prefix nodes. No positive-index row expansion is
// needed here: the local packet is exactly {zero, delete_last_column(K)}.
function countRows(root,b){
  const columns=[[]],columnIds=new Map([['',0]]),nodes=[{parent:0,col:0,len:0,finite:true,up:[]}];
  const nodeIds=new Map(),interned=new WeakMap(),comparisons=new Map();let cells=0,keyChars=0,maxWidth=0;
  function prefix(id,len){let d=nodes[id].len-len;for(let j=0;d;j++,d=Math.floor(d/2)){
    b.tick();if(d%2)id=nodes[id].up[j];}return id;}
  function compare(a,c){
    b.tick();if(a===c)return 0;const key=a+','+c,saved=comparisons.get(key);if(saved!==undefined)return saved;
    const la=nodes[a].len,lc=nodes[c].len,len=Math.min(la,lc);let x=prefix(a,len),y=prefix(c,len),out=icmp(la,lc);
    if(x!==y){
      for(let j=Math.max(nodes[x].up.length,nodes[y].up.length)-1;j>=0;j--){b.tick();
        const u=nodes[x].up[j]??0,v=nodes[y].up[j]??0;if(u!==v){x=u;y=v;}}
      const ca=columns[nodes[x].col],cc=columns[nodes[y].col];out=icmp(ca.length,cc.length);
      for(let j=0;j<Math.min(ca.length,cc.length);j++){
        b.tick();const d=icmp(ca[j][0],cc[j][0])||compare(ca[j][1],cc[j][1])||icmp(ca[j][2],cc[j][2]);
        if(d){out=d;break;}
      }
    }
    if(comparisons.size<COUNT_CAP.comparisons)comparisons.set(key,out);return out;
  }
  function column(es){
    const a=es.slice().sort((x,y)=>{b.tick();return -(icmp(x[0],y[0])||compare(x[1],y[1])||icmp(x[2],y[2]));});
    const key=a.map(e=>e.join(',')).join(';');let id=columnIds.get(key);
    if(id===undefined){cells+=a.length;keyChars+=key.length;
      if(cells>COUNT_CAP.columnCells||keyChars>COUNT_CAP.keyChars)throw Error('Ω-LRD3：共享行标关系列缓存超限');
      id=columns.length;columns.push(a);columnIds.set(key,id);}return id;
  }
  function append(parent,col){
    b.tick();const key=parent+','+col;let id=nodeIds.get(key);if(id!==undefined)return id;
    if(nodes.length>=COUNT_CAP.nodes)throw Error('Ω-LRD3：共享行标节点超限');
    const p=nodes[parent],up=[parent];for(let j=1;up[j-1];j++)up.push(nodes[up[j-1]].up[j-1]??0);
    id=nodes.length;nodes.push({parent,col,len:p.len+1,finite:p.finite&&!columns[col].length,up});
    nodeIds.set(key,id);maxWidth=Math.max(maxWidth,p.len+1);return id;
  }
  function intern(g){
    b.tick();const saved=interned.get(g);if(saved!==undefined)return saved;
    let id=0;for(const col of g.cols)id=append(id,column(col.map(e=>{b.tick();return [e.p,intern(e.k),e.q];})));
    interned.set(g,id);return id;
  }
  return {intern,compare,packet:id=>nodes[id].finite?[]:[...new Set([0,nodes[id].parent])],
    stats:()=>({mode:'persistent-all-row-prefixes',nodes:nodes.length,columns:columns.length,maxRowWidth:maxWidth,
      comparisons:comparisons.size})};
}
function counts(root,b,options={}){
  const workLimit=Math.min(options.maxWork??COUNT_CAP.work,COUNT_CAP.work);let work=0,iterations=0,traceCells=0,traceStates=0;
  const tick=()=>{b.tick();if(++work>workLimit)throw Error('Ω-LRD3：计数工作量超限');};
  const backend=countRows(root,b),traces=[],highest=[],unchanged=[];
  const pair=e=>e.k+','+e.q,priority=(a,c)=>backend.compare(a.k,c.k)||icmp(a.q,c.q);
  function push(heap,e){let i=heap.length;heap.push(e);while(i){tick();const p=(i-1)>>1;if(priority(heap[p],e)>=0)break;heap[i]=heap[p];i=p;}heap[i]=e;}
  function pop(heap){const first=heap[0],last=heap.pop();if(heap.length){let i=0;while(i*2+1<heap.length){tick();let c=i*2+1;
    if(c+1<heap.length&&priority(heap[c+1],heap[c])>0)c++;if(priority(last,heap[c])>=0)break;heap[i]=heap[c];i=c;}heap[i]=last;}return first;}
  function put(map,e){tick();const id=pair(e),old=map.get(id);if(!old||old.p<e.p){
    map.set(id,e);if(map.size>COUNT_CAP.activeCells)throw Error('Ω-LRD3：计数活动关系超限');if(map.heap)push(map.heap,e);
    if(map.heap?.length>2*COUNT_CAP.activeCells)throw Error('Ω-LRD3：计数优先队列超限');}}
  let profileCells=0;
  const profiles=root.cols.map(col=>{const m=new Map();for(const e of col){const k=backend.intern(e.k);
    for(let q=0;q<=e.q;q++)put(m,{k,q,p:e.p});}profileCells+=m.size;
    if(profileCells>COUNT_CAP.activeCells)throw Error('Ω-LRD3：计数输入关系超限');return m;});
  profiles.forEach((m,c)=>{highest[c]=[...m.values()].reduce((a,e)=>!a||priority(e,a)>0?e:a,null);unchanged[c]={steps:0n,rest:m};});
  const values=[];
  function query(c,cut){
    tick();if(!highest[c]||priority(highest[c],cut)<0)return unchanged[c];
    const t=traces[c];if(!t)throw Error('Ω-LRD3：缺少已完成源列的计数轨迹');
    let lo=0,hi=t.length-1;while(lo<hi){tick();const mid=(lo+hi)>>1;
      if(t[mid].top&&priority(t[mid].top,cut)>=0)lo=mid+1;else hi=mid;}return t[lo];
  }
  b.countStats=()=>({...backend.stats(),iterations,work,traceCells,traceStates});
  for(let c=0;c<profiles.length;c++){
    const active=new Map(profiles[c]);active.heap=[];for(const e of active.values())push(active.heap,e);
    const trace=c<profiles.length-1?[]:null;let steps=0n;
    b.countProgress={completed:values.map(String),column:c+1,lowerBound:'1'};
    for(;;){
      tick();while(active.heap.length&&active.get(pair(active.heap[0]))!==active.heap[0])pop(active.heap);
      const top=active.heap[0];
      if(trace){traceCells+=active.size;traceStates++;
        if(traceCells>COUNT_CAP.traceCells||traceStates>COUNT_CAP.traceStates)throw Error('Ω-LRD3：已完成列的计数轨迹缓存超限');
        if(trace.length&&top&&priority(trace.at(-1).top,top)<=0)throw Error('Ω-LRD3：计数轨迹优先级没有下降');
        trace.push({top,steps,rest:new Map(active)});
      }
      if(!top)break;pop(active.heap);active.delete(pair(top));
      const sub=query(top.p,top);steps+=1n+sub.steps;iterations++;
      for(const e of sub.rest.values())put(active,e);
      for(const k of backend.packet(top.k))for(let q=0;q<=top.p;q++)put(active,{k,q,p:top.p});
      b.countProgress.lowerBound=String(steps+1n);
    }
    values.push(steps+1n);if(trace)traces[c]=trace;
  }
  return values;
}
function numberPlain(raw){
  if(isTop(raw))return TOP;const b=budget(COUNT_CAP.work);
  try{const values=guard(()=>counts(parse(raw,b),b));return values.length?values.join(','):'0';}
  catch(e){if(!/超限|过长/.test(e.message))throw e;const p=b.countProgress;
    return p?'（计数超限：第 '+p.column+' 列已确认至少 '+p.lowerBound+'，尚未算完）':'（计数超限；请查看列表）';}
}
const numberView={name:'计数序列',plain:numberPlain,
  html:raw=>'<span style="font-family:inherit;white-space:nowrap">'+esc(numberPlain(raw))+'</span>',latex:raw=>tex(numberPlain(raw))};
register_notation({
  id:'omega-lrd3-single-column-v01',name:'Ω-LRD3',simple_name:'Ω-LRD3',
  description:[
    '自索引 LRD：行标也是有限 Ω-LRD3 表达式，不允许循环引用或以外顶端作行标。',
    '每列 [...]，关系为 (行标,父列,最大根)。自然数行标写数字，非有限行标用 {完整表达式}。',
    '非有限控制行 K 在第 b 块生成 {0,K[0],…,K[b]}；有限行不生成新层，保持 LRD 的指标约定。',
    '有限图 [0] 删末列；正指标展开只改变末列并向右追加，逐指标完整前缀递增。按列递归比较。',
    'A0=0，A1=[]；此后 A(n+1) 保留 An，只追加 [(An,n−1,n−1)]。不再添加间隔空列。',
    '顶端 Limit of Ω-LRD3 的 [n]=An，An 有 n 列，A(n+1)[0]=An。只有最左列为空；普通展开仍可产生正常的空列。',
    '输入 A3、A3[2][1]、Limit[3]、自然数或完整列表。T3 是 A3 的兼容别名，不能与旧记号同名输入的含义混淆。',
    '标准域只包括顶端及其展开后代；手工输入仅校验结构，不判定标准可达性。',
    '保留前缀衔接的良序与共尾性论证，依赖待独立审计的 LRD 通用 ZFC 证明稿；未证明与 Ω-LRD2 等强。',
    '默认一行列表，等价表示只有计数序列。字体继承页面。计数使用 BigInt，精确返回或明确报超限，不能反解输入。',
    '同一事件循环任务共享约 1 秒检查点预算；缓存和文本有上限，超限不返回截断图。不是浏览器硬实时或总内存保证。',
    '不画山脉图；自嵌套列表保持完整，不用省略号隐藏行标。'
  ],display:list,display_equiv:{'计数序列':numberView},FS:fs,FS_alter:fs,FS_short:fs,
  compare:(a,c)=>guard(()=>{const ta=isTop(a),tc=isTop(c),b=budget();
    if(ta||tc){if(!ta)parse(a,b);if(!tc)parse(c,b);return ta?(tc?0:1):-1;}return cmp(parse(a,b),parse(c,b),b);}),
  is_limit:raw=>guard(()=>{if(isTop(raw))return true;const b=budget();return !!control(parse(raw,b),b);}),
  init:()=>[TOP,'[]','∅'],
  debug:{limits:{...CAP,index:String(CAP.index)},parse:raw=>guard(()=>parse(raw,budget())),
    step:(g,n)=>guard(()=>step(g,n,budget())),seed:d=>guard(()=>seed(d,budget())),
    compare:(a,c)=>guard(()=>cmp(a,c,budget())),
    counts:(raw,options)=>guard(()=>isTop(raw)?null:counts(parse(raw,budget()),budget(COUNT_CAP.work),options)),
    counts_legacy:(raw,options)=>guard(()=>isTop(raw)?null:countsLegacy(parse(raw,budget()),budget(COUNT_CAP.work),options)),
    count_audit:(raw,options)=>{if(isTop(raw))return {status:'top'};const b=budget(COUNT_CAP.work);
      try{return {status:'exact',values:guard(()=>counts(parse(raw,b),b,options)).map(String),stats:b.countStats?.()};}
      catch(e){if(!/超限|过长/.test(e.message))throw e;return {status:'guard',reason:e.message,progress:b.countProgress,stats:b.countStats?.()};}}
  }
});
})();
