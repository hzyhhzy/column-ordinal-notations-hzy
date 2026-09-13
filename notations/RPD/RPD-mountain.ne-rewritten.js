// Standalone RPD adjacency-view trial; published mathematical core is embedded unchanged.
(function (register) {
'use strict';
let definition;
(function (register_notation) {
// RPD mountain view v1.2.2; four explicit menu choices, compact roots, native NER diagram.
// Parent-first column comparison; no KB path semantics. No imports or network.
// Proof status: step descent proved; global standard well-order conditional on
// the graph-termination lemma; >=Y / equality with old path RPD not established.
(function(){
"use strict";
if(typeof register_notation!=="function")throw Error("请在 ne-rewritten 自定义记号中导入。");
'use strict';
// Root-reflection Path Diagrams (RPD), 2026-09-12.
// Independent finite rules; no Y evaluator is used by this module.
// All mathematical integers use BigInt. Resource guards throw, never truncate.
const DEFAULT = {maxWidth: 128n, maxAtoms: 40000, maxCopies: 32n,
  maxSeed: 32n, maxPath: 1000, maxOps: 5000000, ms: 5000};
function budget(options={}) {
  const b={...DEFAULT,...options,ops:0,start:Date.now()};
  b.tick=()=>{if(++b.ops>b.maxOps || Date.now()-b.start>b.ms) throw Error('resource budget');};
  return b;
}
function nat(n) {
  if(typeof n==='number' && !Number.isSafeInteger(n)) throw Error('unsafe integer');
  if(typeof n!=='number' && typeof n!=='bigint') throw Error('integer required');
  const v=BigInt(n); if(v<0n) throw Error('negative integer'); return v;
}
function cmp(a,b) {
  for(let i=0;i<Math.min(a.length,b.length);i++) if(a[i]!==b[i]) return a[i]<b[i]?-1:1;
  return Math.sign(a.length-b.length);
}
function close(g,b=budget()) {
  const size=nat(g.size); if(size>b.maxWidth) throw Error('width guard');
  const atoms=new Map();
  for(const raw of g.atoms) {
    if(raw.length!==4) throw Error('four fields required');
    const [k,r,p,c]=raw.map(nat);
    if(!(r<=p && p<c && c<size)) throw Error('invalid edge');
    for(let q=0n;q<=r;q++) {
      b.tick(); const e=[k,q,p,c]; atoms.set(e.join(','),e);
      if(atoms.size>b.maxAtoms) throw Error('atom guard');
    }
  }
  return {size,atoms:[...atoms.values()].sort(cmp)};
}
function seed(k,b=budget()) {
  k=nat(k); if(k>b.maxSeed) throw Error('seed guard');
  const atoms=[]; for(let j=0n;j<=k;j++) atoms.push([j,0n,0n,1n]);
  return {size:2n,atoms};
}
function end(g) {return g.atoms.filter(e=>e[3]===g.size-1n);}
function drop(g) {
  if(g.size===0n) throw Error('terminal diagram has no moves');
  return {size:g.size-1n,atoms:g.atoms.filter(e=>e[3]<g.size-1n)};
}
// Finite-iteration implementation of the displayed closed-form rule.
function copy(g,controller,n,b=budget()) {
  n=nat(n); if(n===0n) return drop(g);
  if(n>b.maxCopies) throw Error('copy guard');
  const e=controller.map(nat), last=g.size-1n;
  if(e[3]!==last || !g.atoms.some(a=>cmp(a,e)===0)) throw Error('controller absent');
  const [K,r,c]=e;
  if(last+n*(last-c)>b.maxWidth) throw Error('width guard');
  let out=drop(g),cut=c,root=r,facts=out.atoms,templates=end(g).map(a=>a.slice(0,3));
  for(let j=0n;j<n;j++) {
    b.tick(); const len=out.size,move=i=>i<cut?i:len+i-cut;
    const moved=facts.map(([k,q,p,v])=>[k,move(q),move(p),move(v)]),needs=[];
    for(const [k,q,p] of templates) for(let h=0n;h<=q;h++) {
      b.tick(); if(k<K || k===K && h<root) needs.push([k,h,p,len]);
    }
    out=close({size:len+(len-cut),atoms:[...out.atoms,...moved,...needs]},b);
    facts=moved; templates=templates.map(([k,q,p])=>[k,move(q),move(p)]);
    root=move(root); cut=len;
  }
  return out;
}
// Independent implementation directly from the mathematical formula.
function copyFormula(g,controller,n,b=budget()) {
  n=nat(n); if(n===0n) return drop(g);
  if(n>b.maxCopies) throw Error('copy guard');
  const e=controller.map(nat),x=g.size-1n,[K,r,c]=e,L=x-c;
  if(e[3]!==x || !g.atoms.some(a=>cmp(a,e)===0)) throw Error('controller absent');
  if(x+n*L>b.maxWidth) throw Error('width guard');
  const base=drop(g).atoms,top=end(g),atoms=[];
  for(let j=0n;j<=n;j++) {
    const f=i=>i<c?i:i+j*L;
    for(const [k,q,p,v] of base) {b.tick();atoms.push([k,f(q),f(p),f(v)]);}
    if(j===n) continue;
    for(const [k,q,p] of top) for(let h=0n;h<=f(q);h++) {
      b.tick();if(k<K || k===K && h<f(r)) atoms.push([k,h,f(p),x+j*L]);
    }
  }
  return close({size:x+n*L,atoms},b);
}

// The public expression is the COLUMN LIST itself, never an operation path.
const NE_LIMITS=Object.freeze({maxWidth:256n,maxAtoms:12000,maxCopies:128n,
  maxSeed:256n,maxPath:512,maxOps:500000,ms:400});
const NE_TEXT_LIMIT=400000,NE_CACHE_ENTRIES=64,NE_CACHE_ATOMS=48000;
const neCache=new Map(),neTraces=new Map();
let neCachedAtoms=0;
function neGuard(action){
  try{return action();}
  catch(error){
    if(/guard|resource budget/.test(String(error.message)))
      throw Error("RPD：达到计算保护上限；未返回截断或近似结果。("+error.message+")");
    throw error;
  }
}
// Display triples are (layer k, parent p, root q). Comparison priority is p,k,q.
function edgeCompare(a,b){return cmp([a[1],a[0],a[2]],[b[1],b[0],b[2]]);}
function graphColumns(g){
  if(g===null)return null;
  const result=Array.from({length:Number(g.size)},()=>[]);
  for(const [k,q,p,j] of g.atoms)result[Number(j)].push([k,p,q]);
  for(const column of result)column.sort((a,b)=>-edgeCompare(a,b));
  return result;
}
function columnCompare(a,b){
  for(let i=0;i<Math.min(a.length,b.length);i++){
    const c=edgeCompare(a[i],b[i]);if(c)return c;
  }
  return Math.sign(a.length-b.length);
}
function columnsCompare(a,b){
  if(a===null)return b===null?0:1;
  if(b===null)return -1;
  for(let j=0;j<Math.min(a.length,b.length);j++){
    const c=columnCompare(a[j],b[j]);if(c)return c;
  }
  return Math.sign(a.length-b.length);
}
function columnsText(columns){
  if(columns===null)return "Limit";
  if(!columns.length)return "∅";
  return columns.map(c=>"["+c.map(e=>"("+e.join(",")+")").join(",")+"]").join("");
}
function neRemember(g,trace){
  const columns=graphColumns(g),key=columnsText(columns);
  if(trace&&trace.length<=8192){
    const old=neTraces.get(key);
    if(!old||trace.length<old.length)neTraces.set(key,trace);
    while(neTraces.size>128)neTraces.delete(neTraces.keys().next().value);
  }
  const old=neCache.get(key);
  if(old){neCache.delete(key);neCache.set(key,old);return old;}
  const atoms=g===null?0:g.atoms.length;
  while(neCache.size>=NE_CACHE_ENTRIES||neCachedAtoms+atoms>NE_CACHE_ATOMS){
    const first=neCache.keys().next().value;if(first===undefined)break;
    const item=neCache.get(first);neCachedAtoms-=item.graph===null?0:item.graph.atoms.length;
    neCache.delete(first);
  }
  const kind=g===null?"limit":g.size===0n?"zero":end(g).length?"limit":"successor";
  const result={graph:g,columns,key,kind};
  neCache.set(key,result);neCachedAtoms+=atoms;return result;
}
function graphStep(g,n,b){
  n=nat(n);b.tick();
  if(g===null)return seed(n,b);
  if(g.size===0n)return g;
  const controls=end(g);
  if(n===0n||!controls.length)return drop(g);
  return copy(g,controls[controls.length-1],n,b);
}
function neInspect(raw){
  if(typeof raw!=="string")throw TypeError("请输入列列表文本。");
  if(raw.length>NE_TEXT_LIMIT)throw Error("列列表超过输入保护上限。");
  const input=raw.trim(),cached=neCache.get(input);
  if(cached){neCache.delete(input);neCache.set(input,cached);return cached;}
  if(/^(Limit|Omega|Ω)$/i.test(input))return neRemember(null,"Ω");
  if(input==="∅"||input==="0")return neRemember({size:0n,atoms:[]});
  if(input==="1")return neRemember({size:1n,atoms:[]});
  const trace=input.match(/^(?:Ω|Limit|Omega)((?:\s*\[\s*\d+\s*\])+)\s*$/i);
  if(trace){
    const indices=[...trace[1].matchAll(/\d+/g)].map(m=>BigInt(m[0]));
    if(indices.length>NE_LIMITS.maxPath)throw Error("操作记录超过长度保护上限。");
    const b=budget(NE_LIMITS);let g=null;
    for(const n of indices)g=graphStep(g,n,b);
    return neRemember(g,"Ω"+indices.map(n=>"["+n+"]").join(""));
  }
  // Only structural validity is checked here, not standard reachability from Ω.
  const tokens=input.match(/\d+|[\[\](),]/g)||[];
  if(!tokens.length||tokens.join("")!==input.replace(/\s/g,""))
    throw TypeError("格式应为 [列0关系][列1关系]…；关系写 (k,p,q)，空图写 ∅。");
  let i=0,j=0;const atoms=[];
  const take=s=>{if(tokens[i++]!==s)throw TypeError("列列表格式错误：期待 "+s+"。");};
  const integer=()=>{const t=tokens[i++];if(!t||!/^\d+$/.test(t))throw TypeError("关系字段必须是自然数。");return BigInt(t);};
  while(i<tokens.length){
    if(BigInt(j)>=NE_LIMITS.maxWidth)throw Error("width guard");
    take("[");
    if(tokens[i]!=="]"){
      for(;;){
        take("(");const k=integer();take(",");const p=integer();take(",");const q=integer();take(")");
        atoms.push([k,q,p,BigInt(j)]);
        if(atoms.length>NE_LIMITS.maxAtoms)throw Error("atom guard");
        if(tokens[i]!==",")break;take(",");
      }
    }
    take("]");j++;
  }
  return neRemember(close({size:BigInt(j),atoms},budget(NE_LIMITS)));
}
function neCompare(a,b){return neGuard(()=>columnsCompare(neInspect(a).columns,neInspect(b).columns));}
function neFS(raw,index){
  return neGuard(()=>{
    const n=nat(index),before=neInspect(raw),g=graphStep(before.graph,n,budget(NE_LIMITS));
    const trace=neTraces.get(before.key);
    const after=neRemember(g,trace?trace+"["+n+"]":undefined);
    if(before.kind!=="zero"&&columnsCompare(after.columns,before.columns)>=0)
      throw Error("内部一致性检查失败：候选展开没有在列字典序下严格下降。");
    return after.key;
  });
}
function viewEscape(s){return String(s).replace(/&/g,"&amp;").replace(/</g,"&lt;").replace(/>/g,"&gt;").replace(/"/g,"&quot;");}
function viewPlain(raw){return neGuard(()=>neInspect(raw).key);}
function viewParse(raw){return viewPlain(raw);}
function viewListHTML(raw){
  const state=neInspect(raw);
  if(state.columns===null)return "Ω";
  return '<span style="white-space:nowrap">'+viewEscape(state.key)+'</span>';
}
function viewLatex(raw){
  const c=neInspect(raw).columns;if(c===null)return "\\Omega";if(!c.length)return "\\varnothing";
  return c.map(col=>"\\left["+col.map(e=>"("+e.join(",")+")").join(",")+"\\right]").join("");
}
const VIEW_MAX_EDGES=3000,VIEW_MAX_SVG_CHARS=2000000;

function viewSVG(raw) {
  return neGuard(()=>{
    const state=neInspect(raw),g=state.graph;
    const textColor="currentColor",rootColor="var(--color-danger,currentColor)",
      guide="var(--color-border-light,currentColor)",background="var(--color-bg,transparent)";
    const svgStart=(w,h,description)=>'<svg xmlns="http://www.w3.org/2000/svg" role="img" aria-label="'+
      viewEscape(description)+'" width="'+w+'" height="'+h+'" viewBox="0 0 '+w+' '+h+
      '" style="display:block;max-width:none;font-family:monospace"><title>'+viewEscape('RPD 列图')+'</title>';
    const text=(x,y,s,size=12,anchor="start",color=textColor)=>
      '<text x="'+x+'" y="'+y+'" font-size="'+size+'" dominant-baseline="middle" text-anchor="'+anchor+
      '" fill="'+color+'">'+viewEscape(s)+'</text>';
    const line=(x1,y1,x2,y2,color=textColor,width=1,dash="")=>
      '<line x1="'+x1+'" y1="'+y1+'" x2="'+x2+'" y2="'+y2+'" stroke="'+color+
      '" stroke-width="'+width+'"'+(dash?' stroke-dasharray="'+dash+'"':"")+'/>';
    const circle=(x,y,r,color=textColor,fill=false)=>
      '<circle cx="'+x+'" cy="'+y+'" r="'+r+'" stroke="'+color+'" stroke-width="1.4" fill="'+
      (fill?color:background)+'"/>';
    if(g===null)return svgStart(300,60,"RPD 顶端")+
      text(10,18,"Ω · RPD 顶端",18)+text(10,44,"展开后进入有限种子图。")+"</svg>";
    const m=Number(g.size);
    if(g.atoms.length>VIEW_MAX_EDGES)throw Error("全图有 "+g.atoms.length+
      " 条边，超过绘图保护上限 "+VIEW_MAX_EDGES+"；未绘制任何局部图。邻接列表仍然完整。");
    const edges=[...g.atoms].sort((a,b)=>cmp([a[0],a[3],a[2],a[1]],[b[0],b[3],b[2],b[1]]));
    const left=116,dx=46,rowHeight=34,y0=100;
    const width=Math.max(370,left+Math.max(1,m)*dx+18);
    const height=edges.length?y0+edges.length*rowHeight+40:132;
    const x=j=>left+Number(j)*dx;
    let out=svgStart(width,height,m+" 列、"+edges.length+" 条边的完整 RPD 图；实线 j→p，红色标记根 q。");
    out+=text(10,16,"完整图 · "+m+" 列 · "+edges.length+" 条边",14);
    out+=text(10,40,"实线 j→p；红圈/虚线标记根 q。k 为关系层。",12);
    if(!m)out+=text(12,81,"∅  空图",19)+text(12,110,
      "空列表为 0；没有历史回退。");
    for(let j=0;j<m;j++){
      out+='<g data-rpd-column="'+j+'">'+text(x(j),65,j,12,"middle")+circle(x(j),80,3,textColor,true);
      if(edges.length)out+=line(x(j),89,x(j),height-37,guide);
      out+='</g>';
    }
    if(m&&!edges.length)out+=text(10,110,"只有列节点，没有边。");
    edges.forEach(([k,q,p,j],i)=>{
      const y=y0+i*rowHeight,xp=x(p),xj=x(j),xq=x(q);
      out+='<g data-rpd-edge="'+i+'" data-relation="'+[k,q,p,j].join(',')+'">'+text(8,y,"k="+k+"  q="+q,12);
      out+=line(xp+5,y,xj-5,y,textColor,1.6)+
        line(xp+5,y,xp+12,y-4,textColor,1.6)+line(xp+5,y,xp+12,y+4,textColor,1.6);
      out+=circle(xp,y,3.5,textColor,true)+circle(xj,y,3.5);
      out+=line(xq,y+11,xp,y+11,rootColor,1,"3 3")+
        circle(xq,y+11,2.8,rootColor)+line(xp,y+7,xp,y+3,rootColor)+'</g>';
    });
    if(edges.length)out+=text(10,height-17,"全部 "+edges.length+" 条边均已绘制；小根边也逐条保留。");
    out+="</svg>";
    if(out.length>VIEW_MAX_SVG_CHARS)throw Error("完整 SVG 超过绘制大小保护上限；未返回局部图。");
    return out;
  });
}


function viewGraphHTML(raw){
  try{return viewSVG(raw);}
  catch(error){
    if(!/绘图保护|绘制大小保护/.test(String(error.message)))throw error;
    return '<span style="color:var(--color-danger,currentColor)">'+viewEscape(error.message)+'</span>';
  }
}
function tracePlain(raw){const state=neInspect(raw);return neTraces.get(state.key)||state.key;}
function traceHTML(raw){
  const state=neInspect(raw),trace=neTraces.get(state.key);
  return trace?viewEscape(trace):"（无操作记录；记号由列列表确定）";
}
// Inspect the first different column IN its shared left context.
// One local step = FS[1], then delete copied columns to the original width.
function trimGraph(g,m){return {size:m,atoms:g.atoms.filter(e=>e[3]<m)};}
function lowerLastColumn(g,b){
  const edges=end(g),e=edges[edges.length-1];if(!e)return null;
  const [K,r,c,x]=e;
  return close({size:g.size,atoms:[
    ...g.atoms.filter(f=>f[3]<x),
    ...g.atoms.filter(f=>f[3]===c).map(([k,q,p])=>[k,q,p,x]),
    ...edges.filter(([k,q])=>k<K||k===K&&q<r)
  ]},b);
}
function firstDifferenceCheck(rawA,rawB,maxSteps=256){
  if(!Number.isSafeInteger(maxSteps)||maxSteps<1||maxSteps>10000)
    throw Error("可达性核验步数必须为 1..10000。");
  return neGuard(()=>{
    const a=neInspect(rawA),b=neInspect(rawB),order=columnsCompare(a.columns,b.columns);
    if(!order)return {status:"equal",steps:0};
    if(a.graph===null||b.graph===null)return {status:"not-checked",reason:"顶端不做首差列核验"};
    let j=0;
    while(j<Math.min(a.columns.length,b.columns.length)&&!columnCompare(a.columns[j],b.columns[j]))j++;
    if(j===Math.min(a.columns.length,b.columns.length))
      return {status:"reachable",via:"delete suffix",steps:Math.abs(a.columns.length-b.columns.length),direction:order>0?"a-to-b":"b-to-a"};
    let current=trimGraph(order>0?a.graph:b.graph,BigInt(j+1));
    const target=trimGraph(order>0?b.graph:a.graph,BigInt(j+1)),targetColumns=graphColumns(target);
    const work=budget(NE_LIMITS);
    let steps=0;
    try{
      for(;steps<maxSteps;steps++){
        work.tick();
        const next=lowerLastColumn(current,work);
        if(next===null)return {status:"incomparable",column:j,steps,reason:"无可用的同宽下降步"};
        const c=columnsCompare(graphColumns(next),targetColumns);
        if(!c)return {status:"reachable",column:j,steps:steps+1,direction:order>0?"a-to-b":"b-to-a",
          scope:"共同前缀加首个不同列",via:"FS[1] then delete copied suffix"};
        if(c<0)return {status:"incomparable",column:j,steps:steps+1,
          reason:"所有下一项在首差列处都已小于目标；后续展开也严格下降",
          from:columnsText(graphColumns(current)),next:columnsText(graphColumns(next)),target:columnsText(targetColumns)};
        current=next;
      }
      return {status:"unknown",column:j,steps,reason:"达到迭代上限，不代表不可达"};
    }catch(error){
      if(/guard|resource budget/.test(String(error.message)))
        return {status:"unknown",column:j,steps,reason:"达到资源保护上限，不代表不可达"};
      throw error;
    }
  });
}

// Local-column height: 1 for an empty relation column; otherwise 1+h(T(C)).
// T is FS[1] restricted to the original width. Counts are BigInt throughout.
const NUMBER_LIMITS=Object.freeze({maxWork:8000000,maxMemo:8192,maxCells:250000,
  maxMs:400,maxText:100000,maxCacheEntries:32,maxCacheChars:600000});
const numberCache=new Map();
let numberCacheChars=0;
function numberLimit(reason){
  const error=Error("数字序列计算达到保护上限（"+reason+"）；请使用列表或图。未返回近似数字。");
  error.name="RPDNumberLimit";return error;
}
function calculateColumnNumbers(g,requested={}){
  const bounds={...NUMBER_LIMITS};
  for(const name of ["maxWork","maxMemo","maxCells","maxMs"]){
    if(requested[name]===undefined)continue;
    const value=requested[name];
    if(!Number.isSafeInteger(value)||value<1||value>bounds[name])throw Error("数字核验限额无效："+name);
    bounds[name]=value;
  }
  const start=Date.now();
  let work=0,cells=0,maxDepth=0;
  function tick(){
    if(++work>bounds.maxWork)throw numberLimit("操作次数");
    if((work&1023)===0&&Date.now()-start>bounds.maxMs)throw numberLimit("时间");
  }
  if(g===null)return {values:null,stats:{work:0,memoEntries:0,memoCells:0,pairs:0,maxDepth:0}};
  const labels=new Map();
  for(const [k,q]of g.atoms){tick();labels.set(k+","+q,[k,q]);}
  const pairs=[...labels.values()].sort((a,b)=>{tick();return cmp(a,b);});
  const ids=new Map(pairs.map((pair,i)=>[pair.join(","),i]));
  const rows=Array.from({length:Number(g.size)},()=>new Map());
  const highest=Array(rows.length).fill(-1);
  for(const [k,q,p,j]of g.atoms){
    tick();const c=Number(j),id=ids.get(k+","+q),parent=Number(p),row=rows[c];
    row.set(id,Math.max(row.get(id)??-1,parent));highest[c]=Math.max(highest[c],id);
  }
  // At a fixed (k,q), only its maximum parent can ever be selected; the entire
  // group is removed together. Thus this profile retains EXACT counting data.
  const memo=new Map();
  function normalise(c,cut,depth){
    tick();maxDepth=Math.max(maxDepth,depth);
    if(highest[c]<cut)return {steps:0n,rest:rows[c]};
    const key=c+":"+cut,saved=memo.get(key);if(saved)return saved;
    const active=new Map(rows[c]);let steps=0n;
    for(let i=highest[c];i>=cut;i--){
      tick();const parent=active.get(i);if(parent===undefined)continue;
      if(!(parent<c))throw Error("数字计数内部错误：父列没有向左严格减小。");
      active.delete(i);
      // Remaining active groups all have lower priority than i. Evaluate the
      // source column's >=i groups once, independently of that lower remainder.
      const sub=normalise(parent,i,depth+1);steps+=1n+sub.steps;
      for(const [id,p]of sub.rest){
        tick();if(id>=i)throw Error("数字计数内部错误：阈值化简未完成。");
        active.set(id,Math.max(active.get(id)??-1,p));
      }
    }
    if(memo.size>=bounds.maxMemo)throw numberLimit("子问题个数");
    cells+=active.size;if(cells>bounds.maxCells)throw numberLimit("缓存关系数");
    const result={steps,rest:active};memo.set(key,result);return result;
  }
  const values=rows.map((_,j)=>normalise(j,0,1).steps+1n);
  if(Date.now()-start>bounds.maxMs)throw numberLimit("时间");
  return {values,stats:{work,memoEntries:memo.size,memoCells:cells,
    pairs:pairs.length,maxDepth,elapsedMs:Date.now()-start}};
}
function numberInspect(raw){
  return neGuard(()=>{
    const state=neInspect(raw),saved=numberCache.get(state.key);
    if(saved){numberCache.delete(state.key);numberCache.set(state.key,saved);return saved;}
    const result=calculateColumnNumbers(state.graph);
    const text=result.values===null?"Limit":result.values.length?result.values.join(","):"0";
    if(text.length>NUMBER_LIMITS.maxText)throw numberLimit("完整数字文本长度");
    const chars=state.key.length+text.length;
    if(chars<=NUMBER_LIMITS.maxCacheChars){
      while(numberCache.size>=NUMBER_LIMITS.maxCacheEntries||numberCacheChars+chars>NUMBER_LIMITS.maxCacheChars){
        const first=numberCache.keys().next().value;if(first===undefined)break;
        numberCacheChars-=numberCache.get(first).chars;numberCache.delete(first);
      }
      const item={...result,text,chars};numberCache.set(state.key,item);numberCacheChars+=chars;return item;
    }
    return {...result,text,chars:0};
  });
}
function numberPlain(raw){
  try{return numberInspect(raw).text;}
  catch(error){if(error.name!=="RPDNumberLimit")throw error;return "（数字序列未计算：达到保护上限；请查看列表）";}
}
function numberHTML(raw){
  try{
    const result=numberInspect(raw),values=result.values;
    if(values===null)return "Ω";
    if(!values.length)return "0";
    return '<span style="white-space:nowrap">'+values.map((value,j)=>
      '<span data-rpd-number-column="'+j+'" title="列 '+j+'；包含最后一次删列">'+value+'</span>').join(",")+'</span>';
  }catch(error){
    if(error.name!=="RPDNumberLimit")throw error;
    return '<span style="color:var(--color-danger,currentColor)">'+viewEscape(error.message)+'</span>';
  }
}
function numberLatex(raw){
  try{const values=numberInspect(raw).values;return values===null?"\\Omega":values.length?"\\left("+values.join(",")+"\\right)":"0";}
  catch(error){if(error.name!=="RPDNumberLimit")throw error;return "\\text{Numeric view resource limit; use list view}";}
}

// RPD mountain presentation. No changes to graph identity, FS, or comparison.
// One node represents (k,p,j) with all roots 0..q_max; this is lossless because
// neInspect returns root-down-closed graphs. No parent/transitive edge is removed.
const MOUNTAIN_LIMITS=Object.freeze({maxGroups:2000,maxLayers:128,maxTracks:900,
  maxDimension:16000,maxPixels:12000000,maxLabel:160,maxWork:300000,
  maxMs:400,maxSvgChars:2500000});
function mountainLimit(reason){
  const error=Error("RPD 山脉图："+reason+"，达到完整绘图保护上限；未绘制局部图，请查看列表。");
  error.name="RPDMountainLimit";return error;
}
function mountainTextWidth(text,size){
  // Conservative estimate, with inherited font and no browser DOM dependency.
  let units=0;for(const char of String(text))units+=char.codePointAt(0)>255?1.12:.72;
  return Math.ceil(units*size);
}
function mountainModel(raw){
  const g=neInspect(raw).graph;
  if(g===null)return {kind:"top",columns:[],layers:[],groups:[],atomCount:0};
  const started=Date.now();let work=0;
  function tick(){
    if(++work>MOUNTAIN_LIMITS.maxWork||(work%512===0&&Date.now()-started>MOUNTAIN_LIMITS.maxMs))
      throw mountainLimit("布局计算量");
  }
  const groups=new Map();
  for(const [k,q,p,j]of g.atoms){
    tick();const key=[k,p,j].join(","),old=groups.get(key);
    if(old){if(q>old.q)old.q=q;}
    else{
      if(groups.size>=MOUNTAIN_LIMITS.maxGroups)throw mountainLimit("关系组个数");
      const layer=String(k);if(layer.length>MOUNTAIN_LIMITS.maxLabel)throw mountainLimit("层标记长度");
      groups.set(key,{k,q,p:Number(p),j:Number(j)});
    }
  }
  const ordered=[...groups.values()].sort((a,b)=>{
    tick();return cmp([a.k,BigInt(a.j),BigInt(a.p)],[b.k,BigInt(b.j),BigInt(b.p)]);
  });
  const width=Number(g.size),layers=[];let band,trackCount=0;
  ordered.forEach((group,id)=>{
    tick();
    if(!band||band.k!==String(group.k)){
      if(layers.length>=MOUNTAIN_LIMITS.maxLayers)throw mountainLimit("层数");
      band={k:String(group.k),top:Array(width).fill(0),nodes:[],used:new Set(),tracks:0};layers.push(band);
    }
    const targetTrack=band.top[group.p],track=Math.max(band.top[group.j]+1,targetTrack+1);
    trackCount+=Math.max(0,track-band.tracks);
    if(trackCount>MOUNTAIN_LIMITS.maxTracks)throw mountainLimit("纵向排版轨道数");
    band.tracks=Math.max(band.tracks,track);band.top[group.j]=track;
    band.used.add(group.p);band.used.add(group.j);
    // Track numbers position the drawing only; they are NOT new RPD layers.
    band.nodes.push({id,k:String(group.k),q:String(group.q),p:group.p,j:group.j,track,targetTrack});
  });
  let numberValues,numberWarning;
  try{numberValues=numberInspect(raw).values.map(String);}
  catch(error){
    if(error.name!=="RPDNumberLimit")throw error;
    numberValues=null;numberWarning="数字计数超限：底部改标列号；全部关系仍完整。";
  }
  if(numberValues?.some(value=>value.length>MOUNTAIN_LIMITS.maxLabel)){
    numberValues=null;numberWarning="数字文本过长：底部改标列号；全部关系仍完整。";
  }
  if(Date.now()-started>MOUNTAIN_LIMITS.maxMs+NUMBER_LIMITS.maxMs)throw mountainLimit("布局时间");
  const columns=Array.from({length:width},(_,j)=>({j,number:numberValues?.[j]??null}));
  const cleanLayers=layers.map(layer=>({...layer,used:[...layer.used].sort((a,b)=>a-b)}));
  return {kind:width?"finite":"zero",columns,layers:cleanLayers,
    groups:cleanLayers.flatMap(layer=>layer.nodes),atomCount:g.atoms.length,numberWarning};
}
function mountainMessage(lines,isWarning=false){
  const width=Math.max(260,...lines.map(text=>mountainTextWidth(text,13)+32));
  return {width,height:24+lines.length*25,elements:[],extra_text:lines.map((text,i)=>({
    text,x:16,y:18+i*25,size:13,align:"left",color:{type:isWarning?"red":"text"}
  })),_rpd:{complete:!isWarning,warning:isWarning}};
}
function mountainDiagram(raw,data={}){
  const model=mountainModel(raw),invert=!!data.invert_vertical,fullRoots=!!data.full_root_labels;
  if(model.kind==="top")return mountainMessage(["Ω · RPD 顶端","展开后显示有限种子的山脉图。"]);
  if(model.kind==="zero")return mountainMessage(["0 · 空图（没有列，也没有关系）"]);
  const black={type:"text"},gray={type:"gray"},red={type:"red"};
  const colGap=Number.isFinite(data.column_gap)?Math.max(32,Math.min(160,data.column_gap)):48;
  const rowGap=36,padding=24;
  const labelWidth=Math.max(30,...model.layers.map(layer=>mountainTextWidth("k="+layer.k,12)));
  const left=labelWidth+32,xs=[],columnWidths=[],rootWidths=Array(model.columns.length).fill(0);let cursor=left;
  const rootLabel=node=>fullRoots?"q="+node.q:node.q==="0"?"":node.q;
  for(const node of model.groups){
    const label=rootLabel(node);
    if(label)rootWidths[node.j]=Math.max(rootWidths[node.j],mountainTextWidth(label,12));
  }
  for(const col of model.columns){
    const cell=Math.max(colGap,mountainTextWidth(col.number??"j="+col.j,16)+20,
      mountainTextWidth("j="+col.j,10)+12,rootWidths[col.j]?rootWidths[col.j]*2+18:0);
    columnWidths.push(cell);xs.push(cursor+cell/2);cursor+=cell;
  }
  let offset=64;
  for(const layer of model.layers){layer.offset=offset;offset+=rowGap*layer.tracks+44;}
  const extent=model.layers.length?offset-24:72;
  const footer=[fullRoots?"q=t：包含根 0…t。":"红字 t：根 0…t；未标：根 0。",
    "斜线→父列；灰线／层内高度仅排版。"];
  if(model.numberWarning)footer.push(model.numberWarning);
  const width=Math.ceil(Math.max(cursor+padding,...footer.map(text=>mountainTextWidth(text,12)+32)));
  const plotHeight=extent+2*padding,height=Math.ceil(plotHeight+footer.length*22+18);
  if(width>MOUNTAIN_LIMITS.maxDimension||height>MOUNTAIN_LIMITS.maxDimension||width*height>MOUNTAIN_LIMITS.maxPixels)
    throw mountainLimit("画布尺寸／像素数");
  const y=d=>invert?padding+d:padding+extent-d;
  const elements=[],extra_text=[];
  const line=(x1,y1,x2,y2,color=black,weight=1,meta)=>elements.push({type:"line",x1,y1,x2,y2,
    stroke:true,stroke_color:color,width:weight,...(meta?{_rpd:meta}:{})});
  const dot=(x,y,color=black,r=2.7,meta)=>elements.push({type:"circle",x,y,r,stroke:false,
    fill:true,fill_color:color,...(meta?{_rpd:meta}:{})});
  const text=(label,x,y,size=12,color=black,align="left",meta)=>extra_text.push({
    text:String(label),x,y,size,color,align,...(meta?{_rpd:meta}:{})});
  // Light spines are alignment guides, not additional directed graph edges.
  for(const col of model.columns){
    line(xs[col.j],y(30),xs[col.j],y(extent),gray,.65,{kind:"column-guide",j:col.j});
    text(col.number??"j="+col.j,xs[col.j],y(22),16,black,"center",{kind:"column",j:col.j});
    if(col.number!==null)text("j="+col.j,xs[col.j],y(0),10,gray,"center");
  }
  for(const layer of model.layers){
    const base=layer.offset;
    line(left-8,y(base),width-padding,y(base),gray,.65,{kind:"layer-guide",k:layer.k});
    text("k="+layer.k,left-16,y(base+layer.tracks*rowGap/2),12,black,"right",{kind:"layer",k:layer.k});
    for(const j of layer.used)if(layer.top[j]===0)
      dot(xs[j],y(base),gray,2,{kind:"anchor",j,k:layer.k});
    for(const node of layer.nodes){
      const xj=xs[node.j],xp=xs[node.p],yj=y(base+node.track*rowGap),yp=y(base+node.targetTrack*rowGap);
      const dx=xp-xj,dy=yp-yj,length=Math.hypot(dx,dy),ux=dx/length,uy=dy/length;
      line(xj+ux*4,yj+uy*4,xp-ux*4,yp-uy*4,black,1.2,{kind:"relation",...node});
    }
  }
  // Place all node labels after all lines, using host extra_text (inherited font).
  for(const layer of model.layers)for(const node of layer.nodes){
    const cx=xs[node.j],cy=y(layer.offset+node.track*rowGap);
    dot(cx,cy,black,2.7,{kind:"node",...node});
    // Left/up is away from both the left/down parent leg and right/up children.
    const label=rootLabel(node);
    if(label)text(label,cx-7,cy+(invert?10:-10),12,red,"right",{kind:"root",...node});
  }
  footer.forEach((label,i)=>text(label,16,plotHeight+10+i*22,12,
    model.numberWarning&&i===footer.length-1?red:gray));
  return {width,height,elements,extra_text,_rpd:{complete:true,kind:model.kind,
    columns:model.columns.length,groups:model.groups.length,atoms:model.atomCount,
    invert_vertical:invert,full_root_labels:fullRoots,plotHeight,extent,padding,columnWidths,numberWarning:model.numberWarning??null}};
}
function mountainSafeDiagram(raw,data={}){
  try{return mountainDiagram(raw,data);}
  catch(error){
    if(error.name!=="RPDMountainLimit")throw error;
    return mountainMessage(["完整山脉图超过保护上限。",error.message],true);
  }
}
function mountainColor(color){
  if(color?.type==="gray")return "var(--color-text-muted,#85858c)";
  if(color?.type==="red")return "var(--color-danger,#b84a40)";
  return "currentColor";
}
function mountainSvg(raw,data={}){
  const diagram=mountainDiagram(raw,data),{width,height}=diagram;
  let out='<svg xmlns="http://www.w3.org/2000/svg" role="img" width="'+width+'" height="'+height+
    '" viewBox="0 0 '+width+' '+height+'" style="display:block;max-width:none;font-family:inherit" aria-label="RPD 完整山脉图">'+
    '<title>RPD 完整山脉图</title><desc>横向按列，纵向按层 k；红字 t 或 q=t 表示根 0 到 t 全部保留，未标根值的黑点表示根 0。灰线仅为对齐辅助线。</desc>';
  function metadata(meta){
    if(!meta)return "";
    if(meta.kind==="column")return ' data-rpd-column="'+meta.j+'"';
    if(meta.kind==="relation")return ' data-rpd-group="'+meta.id+'" data-relation="'+
      [meta.k,meta.q,meta.p,meta.j].join(',')+'"';
    return ' data-rpd-kind="'+meta.kind+'"';
  }
  for(const el of diagram.elements){
    const meta=metadata(el._rpd);
    if(el.type==="line")out+='<line x1="'+el.x1+'" y1="'+el.y1+'" x2="'+el.x2+'" y2="'+el.y2+
      '" stroke="'+mountainColor(el.stroke_color)+'" stroke-width="'+el.width+'"'+meta+'/>';
    else if(el.type==="circle")out+='<circle cx="'+el.x+'" cy="'+el.y+'" r="'+el.r+'" fill="'+
      mountainColor(el.fill_color)+'"'+meta+'/>';
  }
  for(const t of diagram.extra_text)out+='<text x="'+t.x+'" y="'+t.y+'" font-size="'+t.size+
    '" dominant-baseline="middle" text-anchor="'+({left:"start",center:"middle",right:"end"}[t.align])+
    '" fill="'+mountainColor(t.color)+'"'+metadata(t._rpd)+'>'+viewEscape(t.text)+'</text>';
  out+='</svg>';
  if(out.length>MOUNTAIN_LIMITS.maxSvgChars)throw mountainLimit("完整 SVG 文本长度");
  return out;
}
function mountainHTML(raw){
  try{return mountainSvg(raw);}
  catch(error){
    if(error.name!=="RPDMountainLimit")throw error;
    return '<span style="color:var(--color-danger,currentColor)">'+viewEscape(error.message)+'</span>';
  }
}
const mountainControl={
  default_data:{invert_vertical:false,column_gap:48,full_root_labels:false},
  settings:[
    {type:"boolean",name:"上下翻转",field_name:"invert_vertical"},
    {type:"number",name:"最小列间距",min:32,max:160,field_name:"column_gap"},
    {type:"boolean",name:"完整根标记（含 q=0）",field_name:"full_root_labels"},
    {type:"info",name:"简写：红字 t 含根 0…t，无红字即根 0。所有父列关系均保留。"}
  ],
  draw_diagram:mountainSafeDiagram,
  handle_action:(data,action)=>action.type==="scroll"&&["up","down"].includes(action.direction)?
    {...data,invert_vertical:action.direction==="down"}:null
};

register_notation({
  id:"rpd-column-mountain-v1",
  name:"RPD（山脉图·四视图）",simple_name:"RPD·山脉",
  description:[
    "记号本身是列列表；同图相等，空列表 ∅ 为 0，不再按历史路径赋值或回退。",
    "每个方括号是一列；三元组 (k,p,q) 表示层、父列、根列。所有列从 0 编号。",
    "比较：列内按父列 p→层 k→根 q 降序排列，再从左到右逐列、逐项按数值比较；真前缀较小。",
    "非空极限项 [0] 删末列；[n] 固定按 (k,q,p) 最大的控制边新增 n 份副本，源块保留。顶端 Ω[n] 仍为种子 S_n。",
    "非空无控制边时各指标都删末列；空图各指标仍为空图。非顶端基本列保持逐列前缀递增。",
    "输入可用列列表，或构造记录 Ω[种子][指标]…。纯列表自动去重并补全小根关系。",
    "标准式仅指从顶端经这些展开可达的图；手工输入只校验有限图条件，不判定标准可达性。",
    "操作序列是辅助记录，不参与比较；相同图的不同历史合并。记录只缓存在当前会话，刷新或缓存淘汰后可能不显示。",
    "在等价表示菜单中直接选择：列表、数字序列、操作序列、画图；(None) 也显示默认列表。显示模式的纯文本／HTML／LaTeX 是另一组选项。画图视图需 HTML，亦可使用原生显示图表。超限拒绝，不返回局部图。",
    "山脉图横向按列，纵向按真实层 k 分区；区内错层只是排版。斜线指向父列，灰线仅对齐；红字 t 含根 0…t，不标即根 0。不删除任何父列捷径，图表设置可恢复完整 q= 标记。",
    "数字表示每列局部清空的次数，包含最后一次删列；空关系列为 1。末列数字大于 1 时，正指标展开使旧末列位置的数字恰好减 1，然后追加新列。指标 0 或末列数字为 1 时直接删末列。",
    "数字用 BigInt 精确递归计数，不逐次执行可能极长的下降链。数列仅作显示；独立输入仍用列表或 Ω[...] 构造记录。",
    "父列优先的一步下降可直接证明。标准式良序性依赖原图终止引理的条件性证明；与 Y 或旧路径系统等强尚未证明。"
  ],
  display:{name:"列表",plain:viewPlain,html:viewListHTML,latex:viewLatex,from_display:viewParse},
  display_equiv:{
    "列表":{name:"列表",plain:viewPlain,html:viewListHTML,latex:viewLatex,from_display:viewParse},
    "数字序列":{name:"数字序列",plain:numberPlain,html:numberHTML,latex:numberLatex},
    "操作序列":{name:"操作序列",plain:tracePlain,html:traceHTML,from_display:viewParse},
    "画图":{name:"画图",plain:viewPlain,html:mountainHTML,latex:viewLatex,from_display:viewParse}
  },
  draw_diagram:mountainControl,
  compare:neCompare,is_limit:raw=>neGuard(()=>neInspect(raw).kind==="limit"),
  FS:neFS,FS_alter:neFS,FS_short:neFS,
  init:()=>["Limit",neRemember({size:1n,atoms:[]},"Ω[0][0]").key,
    neRemember({size:0n,atoms:[]},"Ω[0][0][0]").key],
  debug:{
    version:"1.2.2-four-explicit-menu-choices",
    column_numbers:raw=>{const values=numberInspect(raw).values;return values===null?null:values.map(String);},
    number_audit:(raw,limits)=>{const result=calculateColumnNumbers(neInspect(raw).graph,limits);return {values:result.values===null?null:result.values.map(String),stats:result.stats};},
    number_cache_stats:()=>({entries:numberCache.size,chars:numberCacheChars,maxEntries:NUMBER_LIMITS.maxCacheEntries,maxChars:NUMBER_LIMITS.maxCacheChars}),
    graph:raw=>neGuard(()=>{const g=neInspect(raw).graph;return g===null?null:{size:String(g.size),atoms:g.atoms.map(e=>e.map(String))};}),
    type:raw=>neGuard(()=>neInspect(raw).kind),
    adjacency:raw=>neGuard(()=>{const c=neInspect(raw).columns;return c===null?null:c.map(col=>col.map(e=>e.map(String)));}),
    full_svg:mountainSvg,raw_relation_svg:viewSVG,
    mountain_model:mountainModel,mountain_diagram:mountainDiagram,mountain_limits:{...MOUNTAIN_LIMITS},
    first_difference_reachability:firstDifferenceCheck,
    first_column_step:raw=>neGuard(()=>{const g=neInspect(raw).graph;if(g===null||!end(g).length)return null;
      return neRemember(lowerLastColumn(g,budget(NE_LIMITS))).key;}),
    cache_stats:()=>({entries:neCache.size,atoms:neCachedAtoms,traces:neTraces.size,
      maxEntries:NE_CACHE_ENTRIES,maxAtoms:NE_CACHE_ATOMS,maxTraces:128})
  }
});
})();
})(value => { if (definition) throw Error('Duplicate notation registration'); definition = value; });

// Shared presentation-only source. The two delivered scripts inline this file.
// It never changes an expression, expansion rule, comparison, or existing view.
function addAdjacencyDisplays(notation, config) {
  'use strict';
  const TEXT = '邻接表（文字）', TABLE = '邻接表（图）';
  const limits = Object.freeze({ ms: config.ms, work: 1000000,
    text: 1000000, slots: 500000, layers: 256, cells: 250000,
    dimension: 32768, pixels: 30000000, svg: 2500000, label: 160 });
  const escape = value => String(value).replace(/&/g, '&amp;').replace(/</g, '&lt;')
    .replace(/>/g, '&gt;').replace(/"/g, '&quot;');
  function fail(reason) {
    const error = Error(config.label + ' 邻接表：' + reason + '超限；未返回截断结果，请查看原列表。');
    error.name = 'AdjacencyViewLimit'; throw error;
  }
  function budget() {
    const started = Date.now(); let work = 0;
    return () => {
      if (++work > limits.work || ((work & 255) === 0 && Date.now() - started > limits.ms))
        fail('计算预算');
    };
  }
  function inspect(raw, tick) {
    const input = config.read(raw);
    if (input === null) return null;
    const columns = [], layers = new Map(); let groups = 0;
    for (let j = 0; j < input.length; j++) {
      tick(); const column = new Map(); columns.push(column);
      for (const [rawK, rawP, rawQ] of input[j]) {
        tick(); const k = BigInt(rawK).toString(), p = Number(rawP), q = BigInt(rawQ);
        if (k.length > limits.label) fail('层标文字');
        if (!column.has(k)) column.set(k, new Map());
        const row = column.get(k), old = row.get(p);
        if (old === undefined) groups++;
        if (old === undefined || q > old) row.set(p, q);
      }
      for (const [k, parents] of column) {
        tick(); if (!layers.has(k)) layers.set(k, { k, entries: [] });
        for (const [p, q] of parents) layers.get(k).entries.push({ k, p, q: String(q), j });
      }
    }
    return { columns, layers: [...layers.values()].sort((a, b) =>
      BigInt(a.k) < BigInt(b.k) ? -1 : BigInt(a.k) > BigInt(b.k) ? 1 : 0), groups };
  }
  function plain(raw) {
    const tick = budget(), graph = inspect(raw, tick);
    if (graph === null) return config.top;
    if (!graph.columns.length) return '∅';
    const output = []; let slots = 0, chars = 0;
    for (const column of graph.columns) {
      tick(); let highest = -1n;
      for (const k of column.keys()) if (BigInt(k) > highest) highest = BigInt(k);
      if (highest >= BigInt(limits.slots)) fail('文字空层数');
      slots += Number(highest + 1n); if (slots > limits.slots) fail('文字格位数');
      const rows = Array(Number(highest + 1n)).fill('');
      for (const [k, parents] of column) {
        tick(); let end = -1;
        for (const p of parents.keys()) end = Math.max(end, p);
        slots += end + 1; if (slots > limits.slots) fail('文字格位数');
        const cells = Array(end + 1).fill('');
        for (const [p, q] of parents) { tick(); cells[p] = String(q); }
        rows[Number(k)] = cells.join(',');
      }
      const text = '[' + rows.join(';') + ']'; chars += text.length;
      if (chars > limits.text) fail('文字长度');
      output.push(text);
    }
    return output.join('');
  }
  function fromDisplay(raw) {
    if (typeof raw !== 'string') throw TypeError('请输入邻接表文字。');
    if (raw.length > limits.text) fail('输入文字');
    const tick = budget(), text = raw.replace(/\s/g, '');
    if (!text || text === '0' || text === '∅') return notation.display.plain('∅');
    if (text === config.top.replace(/\s/g, '')) return notation.display.plain(config.top);
    let cursor = 0, j = 0, slots = 0; const columns = [];
    for (const match of text.matchAll(/\[([^\[\]]*)\]/g)) {
      tick();
      if (match.index !== cursor) throw TypeError('邻接表应为连续的 [列][列]。');
      if (j >= config.width) fail('输入列数');
      cursor += match[0].length;
      if (!/^[\d,;]*$/.test(match[1])) throw TypeError('邻接表内只允许自然数、逗号和分号。');
      const rows = match[1].split(';'), triples = [];
      slots += rows.length;
      for (let k = 0; k < rows.length; k++) {
        tick(); if (!rows[k]) continue;
        const cells = rows[k].split(','); slots += cells.length;
        if (slots > limits.slots) fail('输入格位数');
        if (cells.length > j) throw TypeError('第 ' + j + ' 列只能引用此前的父列。');
        for (let p = 0; p < cells.length; p++) {
          tick(); if (cells[p] === '') continue;
          if (cells[p].length > limits.label) fail('根数值文字');
          const q = BigInt(cells[p]);
          if (q > BigInt(p)) throw TypeError('最大根不能超过父列。');
          if (config.anchored && k >= j) throw TypeError('ARD 行锚必须在子列之前。');
          triples.push('(' + k + ',' + p + ',' + q + ')');
        }
      }
      if (slots > limits.slots) fail('输入空层数');
      columns.push('[' + triples.join(',') + ']'); j++;
    }
    if (!j || cursor !== text.length) throw TypeError('邻接表应为连续的 [列][列]。');
    return notation.display.plain(columns.join(''));
  }
  function textHTML(raw) {
    return '<span style="font-family:inherit;white-space:nowrap">' + escape(plain(raw)) + '</span>';
  }
  function latex(raw) {
    const text = plain(raw);
    return text === '∅' ? '\\varnothing' : '\\text{' + text + '}';
  }
  function message(text, warning = false) {
    return { width: Math.max(160, Array.from(text).length * 14 + 24), height: 48,
      elements: [], extra_text: [{ text, x: 12, y: 24, size: 13, align: 'left',
        color: { type: warning ? 'red' : 'text' } }],
      _adjacency: { complete: !warning, warning, layers: [], entries: [] } };
  }
  function diagram(raw, data = {}) {
    const tick = budget(), graph = inspect(raw, tick);
    if (graph === null) return message(config.top);
    const size = graph.columns.length;
    const layers = data.invert_vertical ? graph.layers.slice().reverse() : graph.layers;
    if (layers.length > limits.layers || layers.length * size * (size + 1) / 2 > limits.cells)
      fail('完整三角表格数');
    let digits = String(Math.max(0, size - 1)).length;
    for (const layer of layers) for (const entry of layer.entries) {
      tick(); digits = Math.max(digits, entry.q.length);
    }
    // Uniform compact cells align all layers, including diagonal index cells.
    // Counts are a separate line, not column headings or coordinate labels.
    const cell = Math.ceil(digits * 7.4 + 3), rowHeight = 14, padding = 4, gap = 8;
    const layerWidth = Math.max(8, ...layers.map(layer => layer.k.length * 7.4));
    const left = padding + layerWidth + 6, firstTableY = 28;
    const tableWidth = size * cell, tableHeight = size * rowHeight;
    const columnWidths = Array(size).fill(cell);
    const columnXs = Array.from({ length: size }, (_, j) => left + (j + 0.5) * cell);
    const minimumWidth = layers.length ? Math.ceil(left + tableWidth + padding) : 16;
    const height = layers.length ? firstTableY + layers.length * (tableHeight + gap) - gap + padding : 24;
    if (minimumWidth > limits.dimension || height > limits.dimension || minimumWidth * height > limits.pixels)
      fail('完整表格画布');
    const elements = [], extra_text = [], entries = [], tables = [];
    function line(x1, y1, x2, y2, kind, k, weight = 0.65) {
      tick(); elements.push({ type: 'line', x1, y1, x2, y2, stroke: true,
        stroke_color: { type: 'gray' }, width: weight, _adjacency: { kind, k } });
    }
    function label(text, x, y, kind, fields = {}, color = 'text', align = 'center') {
      tick(); extra_text.push({ text: String(text), x, y, size: 12, align,
        color: { type: color }, _adjacency: { kind, ...fields } });
    }
    for (let index = 0; index < layers.length; index++) {
      tick(); const layer = layers[index], y = firstTableY + index * (tableHeight + gap);
      label(layer.k, left - 6, y + tableHeight / 2, 'layer', { k: layer.k }, 'text', 'right');
      // Keep p<=j. The shaded p=j cells carry both coordinate labels; only
      // actual relations (p<j) contain q. NER supports lines but not rectangles,
      // so a butt-capped line one row thick fills each whole diagonal cell.
      for (let j = 0; j < size; j++) {
        tick(); const cy = y + (j + 0.5) * rowHeight;
        elements.push({ type: 'line', x1: left + j * cell, y1: cy,
          x2: left + (j + 1) * cell, y2: cy, stroke: true, width: rowHeight,
          stroke_color: { color: { r: 93, g: 155, b: 217, a: 0.24 } },
          _adjacency: { kind: 'diagonal-background', k: layer.k, j } });
        label(j, columnXs[j], cy, 'diagonal-index', { k: layer.k, j });
      }
      for (let p = 0; p <= size; p++) {
        line(left + Math.max(0, p - 1) * cell, y + p * rowHeight, left + tableWidth, y + p * rowHeight,
          'grid-horizontal', layer.k);
      }
      for (let j = 0; j <= size; j++) {
        line(left + j * cell, y, left + j * cell, y + Math.min(size, j + 1) * rowHeight,
          'grid-vertical', layer.k);
      }
      for (const entry of layer.entries) {
        const x = columnXs[entry.j], cy = y + (entry.p + 0.5) * rowHeight;
        label(entry.q, x, cy, 'cell', entry); entries.push({ ...entry, x, y: cy });
      }
      tables.push({ k: layer.k, x: left, y, width: tableWidth, height: tableHeight });
    }
    // Reuse the existing exact counter, including its existing error handling.
    // Do this after geometry so an exhausted counter does not suppress the graph.
    let countText = config.countText(raw), countComplete = /^\d+(?:,\d+)*$/.test(countText);
    const countWidth = text => Array.from(text).reduce((sum, ch) => sum +
      (ch.charCodeAt(0) > 127 ? 14 : 8.5), 2 * padding);
    const maximumCountWidth = Math.min(limits.dimension, Math.floor(limits.pixels / height));
    if (countWidth(countText) > maximumCountWidth) {
      countText = '计数序列文字过长；未截断显示'; countComplete = false;
    }
    const width = Math.ceil(Math.max(minimumWidth, countWidth(countText)));
    if (width > limits.dimension || width * height > limits.pixels) fail('完整表格画布');
    extra_text.unshift({ text: countText, x: padding, y: 11, size: 14, align: 'left',
      color: { type: countComplete ? 'text' : 'red' }, _adjacency: { kind: 'counts' } });
    return { width, height, elements, extra_text, _adjacency: { complete: true,
      columns: size, groups: graph.groups, layers: tables, entries, cell, columnWidths, columnXs, rowHeight,
      countText, countComplete, triangular: true } };
  }
  function safeDiagram(raw, data) {
    try { return diagram(raw, data); }
    catch (error) {
      if (error.name !== 'AdjacencyViewLimit') throw error;
      return message(error.message, true);
    }
  }
  const color = spec => spec.color ? 'rgba(' + [spec.color.r, spec.color.g, spec.color.b,
    spec.color.a ?? 1].join(',') + ')' : spec.type === 'gray' ? 'var(--color-text-muted,#999999)' :
    spec.type === 'red' ? 'var(--color-danger,#bb5147)' : 'currentColor';
  function svg(raw) {
    const value = safeDiagram(raw), tick = budget(), parts = [
      '<svg xmlns="http://www.w3.org/2000/svg" role="img" width="' + value.width +
      '" height="' + value.height + '" viewBox="0 0 ' + value.width + ' ' + value.height +
      '" style="display:block;max-width:none;font-family:inherit" aria-label="' + config.label + ' 分层邻接表">',
      '<title>' + config.label + ' 分层邻接表</title>',
      '<desc>最上方是计数序列，随后每层一张上三角邻接表；完整对角格用淡色背景填入列号，同时充当行列标。左侧裸数字为层号，其余格内数字为最大根 q。无外侧行列号。</desc>'
    ];
    for (const line of value.elements) {
      tick(); parts.push('<line x1="' + line.x1 + '" y1="' + line.y1 + '" x2="' + line.x2 +
        '" y2="' + line.y2 + '" stroke="' + color(line.stroke_color) + '" stroke-width="' + line.width +
        '" stroke-linecap="butt"/>');
    }
    for (const text of value.extra_text) {
      tick(); const meta = text._adjacency;
      const cell = meta?.kind === 'cell' ? ' data-adjacency="' + [meta.k, meta.p, meta.q, meta.j].join(',') + '"' : '';
      parts.push('<text x="' + text.x + '" y="' + text.y + '" font-size="' + text.size +
        '" dominant-baseline="middle" text-anchor="' + ({ left: 'start', center: 'middle', right: 'end' }[text.align]) +
        '" fill="' + color(text.color) + '"' + cell + '>' + escape(text.text) + '</text>');
    }
    parts.push('</svg>'); const result = parts.join('');
    if (result.length > limits.svg) fail('完整 SVG 文字');
    return result;
  }
  const oldControl = notation.draw_diagram;
  notation.id = config.id;
  notation.name = config.displayName || config.label + '（邻接表试用版）';
  if (config.displayName) notation.simple_name = config.displayName;
  notation.description = [...notation.description,
    '本试用版新增邻接表（文字）和邻接表（图），原有显示、展开及比较不变。',
    '文字：每列一对 []；分号从层 0 起分层，逗号从父列 0 起定位，格内填最大根 q。内部空位保留，尾部空位省略；0 不是空位。',
    '图：最上方是计数序列，其下每层一张上三角表；只裁去必空的下三角，不删任何关系。完整对角格用淡色背景填列号，同时标识该行和该列。层号在左侧，不加 k=，不画外侧行列号。',
    '两种新视图均可由纯文本导回列表。计数复用原精确算法；超限明确提示，不代填近似数字。表格完整显示全部关系。'
  ];
  notation.display_equiv = { ...notation.display_equiv,
    [TEXT]: { name: TEXT, plain, html: textHTML, latex, from_display: fromDisplay },
    [TABLE]: { name: TABLE, plain, html: svg, latex, from_display: fromDisplay }
  };
  notation.draw_diagram = { ...oldControl,
    default_data: { ...oldControl.default_data, current_equiv: undefined },
    draw_diagram: (raw, data = {}) => data.current_equiv === TABLE || data.current_equiv === TEXT ?
      safeDiagram(raw, data) : oldControl.draw_diagram(raw, data)
  };
  notation.debug = { ...notation.debug, adjacency_text: plain, adjacency_from_text: fromDisplay,
    adjacency_diagram: diagram, adjacency_svg: svg, adjacency_limits: limits };
}
addAdjacencyDisplays(definition, {label:'RPD',displayName:'RDP',top:'Limit',id:'rpd-column-adjacency-v1',width:256,ms:400,anchored:false,countText:raw=>definition.display_equiv['数字序列'].plain(raw),read:raw=>definition.debug.adjacency(raw)});
register(definition);
})(register_notation);
