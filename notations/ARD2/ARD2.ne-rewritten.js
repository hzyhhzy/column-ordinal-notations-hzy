// ARD2 (skyline full-context anchored row diagrams), standalone notation.
// Renderer adapted from ARD; the ARD2 rule and local counter are independent.
(function (register) {
'use strict';
let definition;
(function (register_notation) {
/* ARD2 v0.2 — exact skyline edition; ARD2-legacy preserves the old rule.
   Standalone custom notation; no imports, network or persistent storage.
   At child j: 0 <= row, maximum root <= j and 0 <= parent < j.
   Ordinary Lean: ../../lean/ARD2/src/ARD2SkylineFinal.lean; paper proof:
   ../../proofs/paper/ard2-well-ordering.md. No internal KP proof-system encoding
   and no order-type comparison or optimal axiom bound is claimed. */
(function () {
'use strict';
const TOP = 'Limit of ARD2';
const CAP = Object.freeze({ms:1000, width:8192, groups:250000, records:1000000,
  work:10000000, text:8000000, cacheChars:16000000, cacheEntries:64,
  path:4096, digits:4096, countCells:500000,
  drawGroups:2000, drawRows:128, drawDimension:32768,
  drawPixels:30000000, drawElements:150000});
function limit(reason) {
  const e = Error('ARD2：' + reason + '超限，未返回截断结果。');
  e.name = 'ARD2Limit'; throw e;
}
function budget() {
  // Each public operation is isolated: a count timeout cannot poison FS or drawing.
  const b = {start:Date.now(), work:0, records:0, chars:0, parsed:new Map()};
  b.tick = () => {
    if (++b.work > CAP.work || ((b.work & 127) === 0 && Date.now()-b.start > CAP.ms))
      limit('约 1 秒计算预算或工作量');
  };
  b.tick(); return b;
}
function nat(n) {
  if (typeof n === 'number' && Number.isSafeInteger(n) && n >= 0) return BigInt(n);
  if (typeof n === 'bigint' && n >= 0n) return n;
  throw Error('指标必须是非负安全整数或 BigInt。');
}
const icmp = (a,b) => a < b ? -1 : a > b ? 1 : 0;
const edgeCmp = (a,b) => icmp(a.p,b.p) || icmp(a.k,b.k) || icmp(a.q,b.q);
const pairCmp = (a,b) => icmp(a.k,b.k) || icmp(a.q,b.q);
function push(col,e,b) {
  b.tick(); if (++b.records > CAP.records) limit('关系构造预算'); col.push(e);
}
function skyline(col,b) {
  const best=new Map();
  for(const e of col) {b.tick();const old=best.get(e.p);if(!old||pairCmp(e,old)>0)best.set(e.p,e);}
  const result=[];let high=null;
  for(const e of [...best.values()].sort((a,c)=>{b.tick();return c.p-a.p;})) {
    b.tick();if(!high||pairCmp(e,high)>0){result.push(e);high=e;}
  }
  return result;
}
function predecessor(e,child) {
  return e.q>0?[{k:e.k,p:e.p,q:e.q-1}]:e.k>0?[{k:e.k-1,p:e.p,q:child}]:[];
}
function make(columns,b) {
  b.tick(); if (columns.length > CAP.width) limit('列数');
  let groups = 0, textSize = 0;
  const cols = columns.map((col,j) => {
    b.tick();
    for (const e of col) {
      b.tick();
      if (![e.k,e.p,e.q].every(Number.isSafeInteger) || e.k < 0 || e.k > j ||
          e.q < 0 || e.q > j || e.p < 0 || e.p >= j)
        throw Error('第 '+j+' 列必须满足 0≤行锚,最大根≤子列、0≤父列<子列。');
    }
    const reduced=skyline(col,b);
    groups += reduced.length; if (groups > CAP.groups) limit('关系组数');
    return Object.freeze(reduced
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
  b.tick();return col.length?col[col.length-1]:null;
}
function finite(n,b) {
  if (n>BigInt(CAP.width)) limit('有限数的列数');
  return make(Array.from({length:Number(n)},()=>[]),b);
}
function seed(index,b) {
  const n=nat(index); if(n>BigInt(CAP.width))limit('种子列数');
  return make(Array.from({length:Number(n)},(_,j)=>j?[{k:j,p:j-1,q:j}]:[]),b);
}
function step(g,index,b) {
  const n=nat(index); b.tick();
  const x=g.cols.length-1;
  if(x<0)return g;
  if(n===0n || !g.cols[x].length)return make(g.cols.slice(0,x),b);
  const e=control(g.cols[x],b),c=e.p,L=x-c;
  const size=BigInt(x)+n*BigInt(L);
  if(size>BigInt(CAP.width))limit('展开后列数');
  const cols=g.cols.slice(0,x),N=Number(n);
  const moved=(a,v)=>{b.tick();const phi=i=>i<c?i:i+v*L;return {k:phi(a.k),p:phi(a.p),q:phi(a.q)};};
  for(let v=0;v<N;v++) {
    b.tick();const seam=[];
    for(const a of g.cols[x].slice(0,-1))push(seam,moved(a,v),b);
    for(const a of predecessor(moved(e,v),x+v*L))push(seam,a,b);
    // Both SELF coordinates of C_c move to this seam via the next block.
    for(const a of g.cols[c])push(seam,moved(a,v+1),b);
    cols.push(skyline(seam,b));
    for(let j=c+1;j<x;j++)cols.push(g.cols[j].map(a=>moved(a,v+1)));
  }
  const result=make(cols,b);
  if(compareGraphs(result,g,b)>=0)throw Error('ARD2：内部一步下降断言失败。');
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
    const prefix=['LimitofARD2','Limit'].find(x=>s.startsWith(x));
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

// Exact frozen-prefix local counter. It deliberately does NOT use ARD's
// threshold-trace optimization, which assumes root <= parent and excludes SELF.
// A local column has finitely many canonical states and strictly decreases;
// the resource guard limits computation, not its mathematical value.
function localColumn(prefix,col,j,b) {
  const e=control(col,b),seam=col.slice(0,-1);
  seam.push(...predecessor(e,j));
  for(const a of prefix[e.p]) {
    push(seam,{k:a.k===e.p?j:a.k,p:a.p,q:a.q===e.p?j:a.q},b);
  }
  if(seam.length>CAP.countCells)limit('计数活动关系');
  return skyline(seam,b);
}
function counts(g,unused,options={}) {
  if(g===null)return null;
  const b=budget(),maxWork=options.maxWork===undefined?CAP.work:options.maxWork;
  if(!Number.isSafeInteger(maxWork)||maxWork<0)throw Error('计数工作量必须是非负安全整数。');
  const ordinaryTick=b.tick;
  b.tick=()=>{ordinaryTick();if(b.work>maxWork)limit('计数工作量');};
  const values=[];
  for(let j=0;j<g.cols.length;j++) {
    b.tick();let col=g.cols[j],value=1n; // Includes deletion of the final empty column.
    while(col.length) {
      b.tick();col=localColumn(g.cols,col,j,b);value+=1n;
    }
    values.push(value);
  }
  return Object.freeze(values);
}
function countPlain(raw) {
  try {const b=budget(),g=parse(raw,b);if(g===null)return TOP;const ns=counts(g,b);return ns.length?ns.join(','):'0';}
  catch(e){if(e.name!=='ARD2Limit')throw e;return '（计数超限；未给出近似值，请查看列表）';}
}

// Row-anchored, fully routed arches. Lanes and fan-out ports are layout only.
// Each compressed group is one logical edge j -> p labelled q (all roots 0..q).
function messageDiagram(text,warning=false) {
  return {width:560,height:64,elements:[],extra_text:[{text,x:16,y:28,size:13,align:'left',
    color:{type:warning?'red':'text'}}],_anchored:{complete:!warning,warning,layout:'row-arcs',routes:[]}};
}
function diagram(raw,data={}) {
  const g=parse(raw,budget());
  if(g===null)return messageDiagram(TOP+' · 展开后显示完整有限图');
  if(!g.cols.length)return messageDiagram('0 · 空图');
  if(g.groups>CAP.drawGroups)limit('完整弧线图关系数');
  let columnNumbers,countComplete=true;
  try {columnNumbers=counts(g,null,{maxWork:data.count_max_work}).map(String);}
  catch(error) {
    if(error.name!=='ARD2Limit')throw error;
    countComplete=false;columnNumbers=Array(g.cols.length).fill('');
  }
  const b=budget(),layers=new Map();
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
  const width=Math.max(countComplete?120:560,cursor+16);let offset=54;
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
  if(!countComplete)text('计数超限；未给出近似值。下方关系仍完整显示。',16,18,13,'red','left',{kind:'count-warning'});
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
    columns:g.cols.length,groups:g.groups,rows:rows.length,counts:columnNumbers,countComplete,
    columnXs:xs,columnCells:cells,routes}};
}
function safeDiagram(raw,data={}) {
  try{return diagram(raw,data);}catch(e){if(e.name!=='ARD2Limit')throw e;
    return messageDiagram('完整弧线图超限，未绘制局部图；请查看列表。',true);}
}
const color=c=>c.type==='red'?'var(--color-danger,#bb5147)':c.type==='gray'?'var(--color-text-muted,#96969e)':'currentColor';
function svg(raw) {
  const d=safeDiagram(raw),out=['<svg xmlns="http://www.w3.org/2000/svg" role="img" width="'+d.width+'" height="'+d.height+
    '" viewBox="0 0 '+d.width+' '+d.height+'" style="display:block;max-width:none;font-family:inherit" aria-label="ARD2 完整弧线图">',
    '<title>ARD2 完整弧线图</title>'];
  for(const e of d.elements){const meta=e._anchored,attr=meta?.kind==='relation'?' data-relation="'+[meta.k,meta.p,meta.q,meta.j].join(',')+'"':'';
    if(e.type==='line')out.push('<line x1="'+e.x1+'" y1="'+e.y1+'" x2="'+e.x2+'" y2="'+e.y2+'" stroke="'+color(e.stroke_color)+'" stroke-width="'+e.width+'"'+attr+'/>');
    else out.push('<circle cx="'+e.x+'" cy="'+e.y+'" r="'+e.r+'" fill="'+color(e.fill_color)+'"/>');}
  for(const t of d.extra_text)out.push('<text x="'+t.x+'" y="'+t.y+'" font-size="'+t.size+'" dominant-baseline="middle" text-anchor="'+
    ({left:'start',center:'middle',right:'end'}[t.align])+'" fill="'+color(t.color)+'">'+esc(t.text)+'</text>');
  out.push('</svg>');return out.join('');
}
const list={name:'列表',plain,html:raw=>htmlText(plain(raw)),latex:raw=>latexText(plain(raw)),from_display:plain};
register_notation({
  id:'ard2-skyline-v02',name:'ARD2',simple_name:'ARD2',
  description:[
    'ARD2：全上下文行锚图的简化轮廓版。每个父只留最大 (k,q)，父递减而 (k,q) 严格递增；标准序型、基本列指标和计数与 ARD2-legacy 相同（纸面证明）。',
    '仓库证明：lean/ARD2/src/ARD2SkylineFinal.lean；proofs/paper/ard2-well-ordering.zh-CN.md。弱体系上界为 KP_omega＋存在不可数序数的纸面证明；Lean 证明新版良序，不含弱体系内部编码或新旧同构。',
    '每列 [...]；(k,p,q) 为行锚、父列、最大根，根 0…q 全包含。第 j 列要求 0≤k,q≤j、0≤p<j；行与根都允许 SELF。',
    '末记录是控制；搬运后根减一，根零时换为 (k−1,p,N_b)，行根皆零则删去。N_b 是接缝自身，不是父列。合入下一份切点列，两个 SELF 都重绑，再取轮廓。',
    '有限非零式 [0] 删末列；G[n] 是 G[n+1] 的完整列前缀。按最早不同列及递减 (p,k,q) 组列表比较。',
    'A0=0，A1=[]；第 j>0 列为 [(j,j−1,j)]。Limit of ARD2 的 [n]=An。',
    '输入 A3、A3[2][1]、Limit[3]、自然数或完整列表。自然数表示空列数量；手写输入只检查合法性，不保证标准可达。',
    '默认列表，另有计数序列、完整弧线图及两种邻接表。字体继承页面；计数不参与比较，不提供有歧义的计数反向解析。',
    '计数为固定前缀下精确的局部删空次数，含最后的空列删除；使用 BigInt，允许约 1 秒。超限不代表不终止，也不填近似数。',
    '计数超限不阻止完整几何绘制；若图本身超限，明确提示且绝不只画局部。列数、关系数、文本和画布另有限制。',
    '三个 FS 选项采用同一规则，无指标偏移。独立文件，无网络或持久缓存。'
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
})(value => { if (definition) throw Error('Duplicate notation registration'); definition = value; });

// Presentation-only adjacency views, adapted for both SELF coordinates.
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
          if (q > BigInt(j)) throw TypeError('最大根不能超过子列。');
          if (k > j) throw TypeError('ARD2 行锚不能超过子列。');
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
    '邻接表（文字）和邻接表（图）只改变呈现，不改变展开或比较。',
    '文字：每列一对 []；分号从层 0 起分层，逗号从父列 0 起定位，格内填最大根 q。内部空位保留，尾部空位省略；0 不是空位。',
    '图：最上方是计数序列，其下每层一张上三角表；只裁去必空的下三角，不删任何关系。完整对角格用淡色背景填列号，同时标识该行和该列。层号在左侧，不加 k=，不画外侧行列号。',
    '两种新视图均可由纯文本导回列表。计数使用当前精确局部算法；超限明确提示，不代填近似数字。表格完整显示全部关系。'
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
addAdjacencyDisplays(definition, {label:'ARD2',displayName:'ARD2',top:'Limit of ARD2',id:'ard2-skyline-v02',width:8192,ms:1000,anchored:true,countText:raw=>definition.display_equiv['计数序列'].plain(raw),read:raw=>{const g=definition.debug.parse(raw);return g===null?null:g.cols.map(col=>col.map(e=>[e.k,e.p,e.q]));}});
register(definition);
})(register_notation);
