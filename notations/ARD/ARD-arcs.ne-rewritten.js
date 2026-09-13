/* ARD arcs v0.1 — Anchored Row Diagrams (formerly Anchored-Rows).
   Standalone ne-rewritten custom notation; no imports, network or storage.
   Triples are (row anchor, parent, maximum root), all zero-based.
   Ordinary Lean well-ordering is proved; weak-theory derivability has a paper proof only.
   No strict strength comparison is claimed. See the documentation accompanying this release. */
(function () {
'use strict';
const TOP = 'Limit of ARD';
const CAP = Object.freeze({ms:1000, width:8192, groups:250000, records:1000000,
  work:10000000, text:8000000, cacheChars:16000000, cacheEntries:64,
  path:4096, digits:4096, countCells:500000, traceCells:500000,
  traceStates:100000, drawGroups:2000, drawRows:128, drawDimension:32768,
  drawPixels:30000000, drawElements:150000});
let active = null;
function limit(reason) {
  const e = Error('ARD：' + reason + '超限，未返回截断结果。');
  e.name = 'AnchoredRowsLimit'; throw e;
}
function budget() {
  if (!active) {
    const b = {start:Date.now(), work:0, records:0, chars:0, parsed:new Map(), counts:new Map()};
    b.tick = () => {
      if (++b.work > CAP.work || ((b.work & 127) === 0 && Date.now()-b.start > CAP.ms))
        limit('约 1 秒计算预算或工作量');
    };
    active = b;
    const clear = () => { if (active === b) active = null; };
    if (typeof queueMicrotask === 'function') queueMicrotask(clear);
    else Promise.resolve().then(clear);
  }
  active.tick(); return active;
}
function nat(n) {
  if (typeof n === 'number' && Number.isSafeInteger(n) && n >= 0) return BigInt(n);
  if (typeof n === 'bigint' && n >= 0n) return n;
  throw Error('指标必须是非负安全整数或 BigInt。');
}
const icmp = (a,b) => a < b ? -1 : a > b ? 1 : 0;
const edgeCmp = (a,b) => icmp(a.p,b.p) || icmp(a.k,b.k) || icmp(a.q,b.q);
function push(col,e,b) {
  b.tick(); if (++b.records > CAP.records) limit('关系构造预算'); col.push(e);
}
function make(columns,b) {
  b.tick(); if (columns.length > CAP.width) limit('列数');
  let groups = 0, textSize = 0;
  const cols = columns.map((col,j) => {
    b.tick(); const merged = new Map();
    for (const e of col) {
      b.tick();
      if (![e.k,e.p,e.q].every(Number.isSafeInteger) || e.k < 0 || e.k >= j ||
          e.q < 0 || e.q > e.p || e.p >= j)
        throw Error('第 '+j+' 列必须满足 0≤行锚<子列、0≤最大根≤父列<子列。');
      const id = e.k*CAP.width+e.p, old = merged.get(id);
      if (!old || old.q < e.q) merged.set(id,e);
    }
    groups += merged.size; if (groups > CAP.groups) limit('关系组数');
    return Object.freeze([...merged.values()].sort((a,c) => {b.tick(); return -edgeCmp(a,c);})
      .map(e => Object.freeze({k:e.k,p:e.p,q:e.q})));
  });
  const parts = cols.map(col => {
    b.tick(); const part = '['+col.map(e => '('+e.k+','+e.p+','+e.q+')').join(',')+']';
    textSize += part.length; if (textSize > CAP.text) limit('完整列表文本'); return part;
  });
  return Object.freeze({cols:Object.freeze(cols),key:parts.join('') || '∅',groups});
}
function compareGraphs(a,c,b) {
  b.tick(); if (a === c || a.key === c.key) return 0;
  for (let j=0;j<Math.min(a.cols.length,c.cols.length);j++) {
    b.tick(); const x=a.cols[j],y=c.cols[j];
    for (let i=0;i<Math.min(x.length,y.length);i++) { b.tick(); const d=edgeCmp(x[i],y[i]); if(d)return d; }
    const d=icmp(x.length,y.length); if(d)return d;
  }
  return icmp(a.cols.length,c.cols.length);
}
function control(col,b) {
  let best=null;
  for (const e of col) { b.tick();
    if (!best || (icmp(e.k,best.k)||icmp(e.q,best.q)||icmp(e.p,best.p))>0) best=e;
  }
  return best;
}
function finite(n,b) {
  if (n>BigInt(CAP.width)) limit('有限数的列数');
  return make(Array.from({length:Number(n)},()=>[]),b);
}
function seed(index,b) {
  const n=nat(index); if(n>BigInt(CAP.width))limit('种子列数');
  return make(Array.from({length:Number(n)},(_,j)=>j?[{k:j-1,p:j-1,q:j-1}]:[]),b);
}
function step(g,index,b) {
  const n=nat(index); b.tick();
  const x=g.cols.length-1;
  if(x<0)return g;
  if(n===0n || !g.cols[x].length)return make(g.cols.slice(0,x),b);
  const e=control(g.cols[x],b),c=e.p,L=x-c;
  const size=BigInt(x)+n*BigInt(L);
  if(size>BigInt(CAP.width))limit('展开后列数');
  const cols=Array.from({length:Number(size)},()=>[]),N=Number(n);
  // Frozen prefix need only be copied once. All its references are < c.
  for(let j=0;j<c;j++) for(const a of g.cols[j])push(cols[j],a,b);
  for(let v=0;v<=N;v++) {
    b.tick(); const phi=i=>i<c?i:i+v*L;
    for(let j=c;j<x;j++)for(const a of g.cols[j])
      push(cols[phi(j)],{k:phi(a.k),p:phi(a.p),q:phi(a.q)},b);
    if(v===N)break;
    const seam=cols[x+v*L];
    for(const a of g.cols[x]) {
      b.tick(); const q=a.k<e.k?phi(a.q):a.k===e.k?Math.min(phi(a.q),phi(e.q)-1):-1;
      if(q>=0)push(seam,{k:phi(a.k),p:phi(a.p),q},b);
    }
    for(let h=0;h<phi(e.k);h++)push(seam,{k:h,p:phi(c),q:phi(c)},b);
  }
  const result=make(cols,b);
  if(compareGraphs(result,g,b)>=0)throw Error('ARD：内部一步下降断言失败。');
  return result;
}
function parse(raw,b) {
  if(typeof raw!=='string')throw Error('请输入字符串表达式。');
  if(raw.length>CAP.text)limit('输入文本');
  b.tick(); const saved=b.parsed.get(raw); if(saved)return saved;
  const s=raw.replace(/\s/g,''),digit=c=>c!==undefined&&c>='0'&&c<='9'; let i=0,g;
  const take=c=>{b.tick();if(s[i++]!==c)throw Error('格式错误：期待 '+c);};
  function number() {
    const begin=i; while(digit(s[i])) {b.tick();i++;if(i-begin>CAP.digits)limit('整数文本');}
    if(i===begin)throw Error('格式错误：期待自然数。');return BigInt(s.slice(begin,i));
  }
  function coordinate() {const n=number();if(n>=BigInt(CAP.width))limit('坐标');return Number(n);}
  if(!s)g=finite(0n,b);
  else if(s[i]==='∅'){i++;g=finite(0n,b);}
  else if(s.startsWith('Limit')) {
    // Keep old saved expressions readable; emit only the current ARD name.
    const prefix=['LimitofAnchored-Rows','LimitofARD','Limit'].find(x=>s.startsWith(x));
    i=prefix.length;
    if(i===s.length)return null;take('[');g=seed(number(),b);take(']');
  }
  else if(s[i]==='A') {i++;g=seed(number(),b);}
  else if(digit(s[i]))g=finite(number(),b);
  else {
    const cols=[];
    while(s[i]==='['&&!digit(s[i+1])) {
      b.tick();if(cols.length>=CAP.width)limit('输入列数');take('[');const col=[];
      if(s[i]!==']')for(;;) {
        take('(');const k=coordinate();take(',');const p=coordinate();take(',');const q=coordinate();take(')');
        push(col,{k,p,q},b);if(s[i]!==',')break;take(',');
      }
      take(']');cols.push(col);
    }
    if(!cols.length)throw Error('请输入 A3、A3[2][1]、自然数或完整列列表。');g=make(cols,b);
  }
  let paths=0;
  while(s[i]==='['&&digit(s[i+1])) {
    if(++paths>CAP.path)limit('展开路径长度');take('[');const n=number();take(']');g=step(g,n,b);
  }
  if(i!==s.length)throw Error('表达式后有未识别的内容。');
  if(b.parsed.size<CAP.cacheEntries && b.chars+raw.length+g.key.length<=CAP.cacheChars) {
    b.parsed.set(raw,g);b.chars+=raw.length+g.key.length;
  }
  return g;
}
const plain=raw=>{const g=parse(raw,budget());return g===null?TOP:g.key;};
const esc=s=>String(s).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;');
const htmlText=s=>'<span style="font-family:inherit;white-space:nowrap">'+esc(s)+'</span>';
const latexText=s=>s==='∅'?'\\varnothing':'\\text{'+s.replace(/[{}\\]/g,c=>'\\'+c)+'}';
const fs=(raw,n)=>{n=nat(n);const b=budget(),g=parse(raw,b);return (g===null?seed(n,b):step(g,n,b)).key;};

// Exact local counts; no unfolding of copied blocks and no ordinal assumptions.
// For each (k,q) only the greatest parent can control. Earlier columns supply
// threshold traces. Each trace's greatest (k,q) strictly decreases.
function counts(g,b,options={}) {
  if(g===null)return null;
  if(options.maxWork===undefined && b.counts.has(g.key))return b.counts.get(g.key);
  const maxWork=options.maxWork===undefined?CAP.work:options.maxWork;
  if(!Number.isSafeInteger(maxWork)||maxWork<0)throw Error('计数工作量必须是非负安全整数。');
  let work=0,profileCells=0,traceCells=0,traceStates=0;
  const tick=()=>{b.tick();if(++work>maxWork)limit('计数工作量');};
  const W=Math.max(1,g.cols.length),pair=(k,q)=>k*W+q;
  const profiles=g.cols.map(col=> {
    const map=new Map();
    for(const e of col)for(let q=0;q<=e.q;q++) {
      tick();const id=pair(e.k,q);if(!map.has(id)||map.get(id)<e.p)map.set(id,e.p);
      if(map.size+profileCells>CAP.countCells)limit('计数输入关系');
    }
    profileCells+=map.size;return map;
  });
  const traces=[],values=[];
  function query(c,cut) {
    tick();const ts=traces[c];let lo=0,hi=ts.length-1;
    while(lo<hi){tick();const mid=(lo+hi)>>1;if(ts[mid].top>=cut)lo=mid+1;else hi=mid;}
    return ts[lo];
  }
  for(let c=0;c<profiles.length;c++) {
    tick();const map=new Map(profiles[c]),heap=[],trace=[];let steps=0n;
    function heapPush(id) {
      let i=heap.length;heap.push(id);
      while(i){tick();const p=(i-1)>>1;if(heap[p]>=id)break;heap[i]=heap[p];i=p;}heap[i]=id;
    }
    function heapPop() {
      const first=heap[0],last=heap.pop();if(heap.length){let i=0;
        while(i*2+1<heap.length){tick();let j=i*2+1;if(j+1<heap.length&&heap[j+1]>heap[j])j++;
          if(last>=heap[j])break;heap[i]=heap[j];i=j;}heap[i]=last;}
      return first;
    }
    function put(id,p) {
      tick();if(!map.has(id)){map.set(id,p);heapPush(id);}
      else if(map.get(id)<p)map.set(id,p);
      if(map.size>CAP.countCells)limit('计数活动关系');
    }
    for(const id of map.keys())heapPush(id);
    for(;;) {
      tick();const top=heap.length?heap[0]:-1;
      // The final column needs a value but no future source trace.
      if(c+1<profiles.length){traceCells+=map.size;
        if(traceCells>CAP.traceCells||++traceStates>CAP.traceStates)limit('计数轨迹缓存');
        if(trace.length&&trace[trace.length-1].top<=top)throw Error('计数轨迹下降断言失败。');
        trace.push({top,steps,rest:new Map(map)});
      }
      if(top<0)break;
      heapPop();const p=map.get(top);map.delete(top);
      const sub=query(p,top);steps+=1n+sub.steps;
      for(const [id,parent] of sub.rest)put(id,parent);
      const k=Math.floor(top/W);
      for(let h=0;h<k;h++)for(let q=0;q<=p;q++)put(pair(h,q),p);
    }
    traces[c]=trace;values.push(steps+1n);
  }
  const result=Object.freeze(values);
  if(options.maxWork===undefined&&b.counts.size<CAP.cacheEntries)b.counts.set(g.key,result);
  return result;
}
function countPlain(raw) {
  try {const b=budget(),g=parse(raw,b);if(g===null)return TOP;const ns=counts(g,b);return ns.length?ns.join(','):'0';}
  catch(e){if(e.name!=='AnchoredRowsLimit')throw e;return '（计数超限；未给出近似值，请查看列表）';}
}

// Row-anchored, fully routed arches. Lanes and fan-out ports are layout only.
// Each compressed group is one logical edge j -> p labelled q (all roots 0..q).
function messageDiagram(text,warning=false) {
  return {width:560,height:64,elements:[],extra_text:[{text,x:16,y:28,size:13,align:'left',
    color:{type:warning?'red':'text'}}],_anchored:{complete:!warning,warning,layout:'row-arcs',routes:[]}};
}
function diagram(raw,data={}) {
  const b=budget(),g=parse(raw,b);
  if(g===null)return messageDiagram(TOP+' · 展开后显示完整有限图');
  if(!g.cols.length)return messageDiagram('0 · 空图');
  if(g.groups>CAP.drawGroups)limit('完整弧线图关系数');
  const columnNumbers=counts(g,b).map(String),layers=new Map();
  let rootDigits=1;
  g.cols.forEach((col,j)=>{for(const e of col){
    b.tick();if(!layers.has(e.k))layers.set(e.k,{k:e.k,edges:[],lanes:[],ports:new Map()});
    const row=layers.get(e.k),edge={...e,j};row.edges.push(edge);
    rootDigits=Math.max(rootDigits,String(e.q).length);
    for(const [column,side] of [[e.p,'parent'],[j,'source']]){
      if(!row.ports.has(column))row.ports.set(column,[]);
      row.ports.get(column).push({edge,side});
    }
  }});
  if(layers.size>CAP.drawRows)limit('完整弧线图行数');
  const rows=[...layers.values()].sort((a,c)=>a.k-c.k),degrees=Array(g.cols.length).fill(0);
  // Short spans get low lanes; overlapping closed column intervals cannot share one.
  for(const row of rows){
    row.edges.sort((a,c)=>{b.tick();return (a.j-a.p)-(c.j-c.p)||a.p-c.p||a.j-c.j;});
    for(const edge of row.edges){
      let lane=0;
      for(;lane<row.lanes.length;lane++){
        let free=true;
        for(const other of row.lanes[lane]){
          b.tick();if(!(edge.j<other.p||other.j<edge.p)){free=false;break;}
        }
        if(free)break;
      }
      if(!row.lanes[lane])row.lanes.push([]);
      row.lanes[lane].push(edge);edge.lane=lane;
    }
    for(const [column,ports] of row.ports){
      degrees[column]=Math.max(degrees[column],ports.length);
      // Separate every vertical stem, even when several edges share a vertex.
      ports.sort((a,c)=>{b.tick();return a.edge.lane-c.edge.lane||
        a.edge.p-c.edge.p||a.edge.j-c.edge.j;});
      ports.forEach((port,i)=>{port.edge[port.side+'Offset']=(i-(ports.length-1)/2)*6;});
    }
  }
  const gap=Number.isFinite(data.column_gap)?Math.max(32,Math.min(100,data.column_gap)):40;
  const pitch=Number.isFinite(data.track_gap)?Math.max(24,Math.min(60,data.track_gap)):28;
  const left=48,xs=[],cells=[],innerGap=rootDigits*8+30;
  let cursor=left;
  for(let j=0;j<columnNumbers.length;j++){
    b.tick();
    const size=Math.max(gap,columnNumbers[j].length*9+18,
      Math.max(0,degrees[j]-1)*6+innerGap);
    cells.push({left:cursor,right:cursor+size});xs.push(cursor+size/2);cursor+=size;
  }
  const width=Math.max(120,cursor+16);let offset=54;
  for(const row of rows){row.base=offset+18+row.lanes.length*pitch;offset=row.base+30;}
  const plotEnd=Math.max(90,offset-16),height=plotEnd+12;
  if(width>CAP.drawDimension||height>CAP.drawDimension||width*height>CAP.drawPixels)
    limit('完整弧线图画布');
  const y=t=>data.invert_vertical?plotEnd-t:t;
  const elements=[],extra_text=[],routes=[];
  function element(e){
    b.tick();if(elements.length+extra_text.length>=CAP.drawElements)limit('完整弧线图线段数');
    elements.push(e);
  }
  const line=(x1,y1,x2,y2,color='text',weight=1.15,meta)=>element({type:'line',
    x1,y1:y(y1),x2,y2:y(y2),stroke:true,stroke_color:{type:color},width:weight,_anchored:meta});
  const dot=(x,yy,color='text',r=2.5,meta)=>element({type:'circle',x,y:y(yy),r,
    stroke:false,fill:true,fill_color:{type:color},_anchored:meta});
  function text(s,x,yy,size=12,color='text',align='center',meta){
    b.tick();extra_text.push({text:String(s),x,y:y(yy),size,color:{type:color},align,_anchored:meta});
  }
  // No mathematical small levels are implied by the lane heights.
  for(let j=0;j<g.cols.length;j++){
    line(xs[j],34,xs[j],plotEnd-2,'gray',.35);
    text(columnNumbers[j],xs[j],18,14,'text','center',{kind:'column',j,count:columnNumbers[j]});
  }
  for(const row of rows){
    line(left-8,row.base,width-12,row.base,'gray',.6);
    text(row.k,left-17,row.base,12,'text','right',{kind:'row-anchor',k:row.k});
    for(const edge of row.edges){
      edge.x1=xs[edge.p]+edge.parentOffset;edge.x2=xs[edge.j]+edge.sourceOffset;
      edge.y=row.base-18-(edge.lane+1)*pitch;
      const labelWidth=String(edge.q).length*8+10;
      edge.label={x:(edge.x1+edge.x2-labelWidth)/2,y:edge.y-9,width:labelWidth,height:18};
    }
    // A vertical stem gets an explicit gap at a horizontal crossing or a label.
    // Thus crossings cannot masquerade as shared vertices; only baseline dots join.
    function stem(x,from,to,edge,meta){
      const cuts=[];
      for(const other of row.edges){
        b.tick();if(other===edge)continue;
        if(x>other.x1+4&&x<other.x2-4&&other.y>from&&other.y<to)
          cuts.push([other.y-3,other.y+3]);
        const box=other.label;
        if(x>=box.x-3&&x<=box.x+box.width+3&&box.y<to&&box.y+box.height>from)
          cuts.push([box.y-3,box.y+box.height+3]);
      }
      cuts.sort((a,c)=>{b.tick();return a[0]-c[0];});
      let at=from;
      for(const [lo,hi] of cuts){
        b.tick();if(lo>at)line(x,at,x,Math.min(lo,to),'text',1.15,meta);
        at=Math.max(at,Math.min(hi,to));
      }
      if(at<to)line(x,at,x,to,'text',1.15,meta);
    }
    for(const edge of row.edges){
      b.tick();const {k,p,q,j,lane,x1,x2}=edge,yy=edge.y,base=row.base,r=4;
      const meta={kind:'arc-segment',k,p,q,j,lane},points=[{x:xs[p],y:base},
        {x:x1,y:base-10},{x:x1,y:yy+r}];
      const parentPort={x:xs[p],y:y(base)},sourcePort={x:xs[j],y:y(base)};
      line(xs[p],base,x1,base-10,'text',1.15,{...meta,kind:'relation'});
      line(xs[j],base,x2,base-10,'text',1.15,meta);
      stem(x1,yy+r,base-10,edge,meta);stem(x2,yy+r,base-10,edge,meta);
      let last={x:x1,y:yy+r};
      for(let i=1;i<=4;i++){
        const angle=i*Math.PI/8,next={x:x1+r-r*Math.cos(angle),y:yy+r-r*Math.sin(angle)};
        line(last.x,last.y,next.x,next.y,'text',1.15,meta);points.push(next);last=next;
      }
      // The edge meets the number's outline, rather than ending in empty space.
      line(x1+r,yy,edge.label.x,yy,'text',1.15,meta);
      line(edge.label.x+edge.label.width,yy,x2-r,yy,'text',1.15,meta);
      last={x:x2-r,y:yy};points.push(last);
      for(let i=1;i<=4;i++){
        const angle=i*Math.PI/8,next={x:x2-r+r*Math.sin(angle),y:yy+r-r*Math.cos(angle)};
        line(last.x,last.y,next.x,next.y,'text',1.15,meta);points.push(next);last=next;
      }
      points.push({x:x2,y:base-10},{x:xs[j],y:base});
      const label={...edge.label,y:data.invert_vertical?
        plotEnd-edge.label.y-edge.label.height:edge.label.y};
      // One digit fits a circle; longer values use a capsule of the same height.
      // Short line segments work identically in native NER canvas and inline SVG.
      const rim=[],radius=edge.label.height/2;
      for(const [cx,start] of [[edge.label.x+edge.label.width-radius,-Math.PI/2],
        [edge.label.x+radius,Math.PI/2]]){
        for(let i=0;i<=16;i++){
          const angle=start+i*Math.PI/16;
          rim.push({x:cx+radius*Math.cos(angle),y:yy+radius*Math.sin(angle)});
        }
      }
      for(let i=0;i<rim.length;i++){
        const a=rim[i],c=rim[(i+1)%rim.length];
        if(Math.hypot(c.x-a.x,c.y-a.y)>1e-6)
          line(a.x,a.y,c.x,c.y,'text',.85,{kind:'root-frame',k,p,q,j});
      }
      text(q,(x1+x2)/2,yy,12,'red','center',{kind:'root',k,p,q,j});
      routes.push({k,p,q,j,lane,x1,x2,y:y(yy),base:y(base),label,
        parentPort,sourcePort,points:points.map(pt=>({x:pt.x,y:y(pt.y)}))});
    }
    // Every endpoint is an actual column in this anchor row; no floating fake nodes.
    for(const column of row.ports.keys())
      dot(xs[column],row.base,'text',2.5,{kind:'vertex',k:row.k,j:column});
    dot(xs[row.k],row.base,'red',3.2,{kind:'anchor-target',k:row.k});
  }
  return {width,height,elements,extra_text,_anchored:{complete:true,layout:'row-arcs',
    columns:g.cols.length,groups:g.groups,rows:rows.length,counts:columnNumbers,
    columnXs:xs,columnCells:cells,routes}};
}
function safeDiagram(raw,data={}) {
  try{return diagram(raw,data);}catch(e){if(e.name!=='AnchoredRowsLimit')throw e;
    return messageDiagram('完整弧线图或计数超限，未绘制局部图；请查看列表。',true);}
}
const color=c=>c.type==='red'?'var(--color-danger,#bb5147)':c.type==='gray'?'var(--color-text-muted,#96969e)':'currentColor';
function svg(raw) {
  const d=safeDiagram(raw),out=['<svg xmlns="http://www.w3.org/2000/svg" role="img" width="'+d.width+'" height="'+d.height+
    '" viewBox="0 0 '+d.width+' '+d.height+'" style="display:block;max-width:none;font-family:inherit" aria-label="ARD 完整弧线图">',
    '<title>ARD 完整弧线图</title>'];
  for(const e of d.elements){const meta=e._anchored,attr=meta?.kind==='relation'?' data-relation="'+[meta.k,meta.p,meta.q,meta.j].join(',')+'"':'';
    if(e.type==='line')out.push('<line x1="'+e.x1+'" y1="'+e.y1+'" x2="'+e.x2+'" y2="'+e.y2+'" stroke="'+color(e.stroke_color)+'" stroke-width="'+e.width+'"'+attr+'/>');
    else out.push('<circle cx="'+e.x+'" cy="'+e.y+'" r="'+e.r+'" fill="'+color(e.fill_color)+'"/>');}
  for(const t of d.extra_text)out.push('<text x="'+t.x+'" y="'+t.y+'" font-size="'+t.size+'" dominant-baseline="middle" text-anchor="'+
    ({left:'start',center:'middle',right:'end'}[t.align])+'" fill="'+color(t.color)+'">'+esc(t.text)+'</text>');
  out.push('</svg>');return out.join('');
}
const list={name:'列表',plain,html:raw=>htmlText(plain(raw)),latex:raw=>latexText(plain(raw)),from_display:plain};
register_notation({
  id:'ard-arcs-v01',name:'ARD（弧线图）',simple_name:'ARD',
  description:[
    'ARD（Anchored Row Diagrams，行锚图）：行锚随列一起移动。普通 Lean 良序证明已完成；弱体系内推导仅有纸面证明；未证明强于 RPD 或 Ω-LRD3。',
    '每列 [...]；(k,p,q) 是行锚、父列、最大根。列号从 0 开始，k<子列且 0≤q≤p<子列。k 是列引用，不是固定层号。',
    '控制按 (k,q,p) 最大；切点为控制父列。复制同时搬移行锚、父、根、子；第 b 块生成所有 h<φ_b(k) 的低行锚。',
    '有限式 [0] 删末列；A[n] 是 A[n+1] 的完整列前缀。先找最早不同列，再按 (p,k,q) 递减列列表比较。',
    'A0=0，A1=[]，A(n+1) 在 An 后追加 [(n−1,n−1,n−1)]；Limit of ARD 的 [n]=An。旧顶端名称仍可输入。',
    '输入 A3、A3[2][1]、Limit[3]、自然数或完整列表。自然数表示相应数量的空列。手写输入只检查结构，不保证标准可达。',
    '列表为默认显示，等价表示提供计数序列和完整弧线图；图上方为每列精确计数，无图下注释。字体继承页面。计数不参与比较。',
    '计数使用 BigInt，有限局部化简可证明终止；正指标展开在原末列位置的计数减 1。超限不显示近似值。',
    '同一事件任务共享约 1 秒检查点预算。列数、关系数、文本、计数轨迹和画布另有限制；超限不是数学不终止的证据。',
    '三个 FS 选项采用同一规则，不加指标偏移。无需其他记号文件，不访问网络、不保存持久缓存。'
  ],
  display:list,
  display_equiv:{
    '计数序列':{name:'计数序列',plain:countPlain,html:raw=>htmlText(countPlain(raw)),latex:raw=>latexText(countPlain(raw))},
    '弧线图':{name:'弧线图',plain,html:svg,latex:raw=>latexText(plain(raw)),from_display:plain}
  },
  FS:fs,FS_alter:fs,FS_short:fs,
  compare:(a,c)=>{const b=budget(),x=parse(a,b),y=parse(c,b);return x===null?(y===null?0:1):y===null?-1:compareGraphs(x,y,b);},
  is_limit:raw=>{const g=parse(raw,budget());return g===null||!!g.cols[g.cols.length-1]?.length;},
  init:()=>[TOP,'[]','∅'],
  draw_diagram:{default_data:{column_gap:40,track_gap:28,invert_vertical:false},settings:[
    {type:'number',name:'列间距',field_name:'column_gap',min:32,max:100},
    {type:'number',name:'轨道间距',field_name:'track_gap',min:24,max:60},
    {type:'boolean',name:'上下翻转',field_name:'invert_vertical'},
    {type:'info',name:'所有关系完整显示；弧线连接子列与父列，红数是最大根。轨道只排版，断口表示交叉而非相连。'}
  ],draw_diagram:safeDiagram},
  debug:{limits:CAP,parse:raw=>parse(raw,budget()),seed:n=>seed(n,budget()),
    step:(g,n)=>step(g,n,budget()),compare:(a,c)=>compareGraphs(a,c,budget()),
    counts:(raw,options)=>{const b=budget();return counts(parse(raw,b),b,options);},
    diagram,svg}
});
})();
