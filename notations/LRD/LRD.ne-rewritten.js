(function(){
'use strict';
// LRD candidate v0.1: Layer-generating Root Diagrams. NOT a proved well-order.
// Row null is W=omega^omega; finite arrays [a0,...,ad] mean sum omega^i*ai.
// All graph/count integers are BigInt. Runtime guards are not mathematical rules.
const LIMITS=Object.freeze({maxWidth:4096n,maxAtoms:500000,maxIndex:4096n,maxDegree:4097,
  maxOps:20000000,maxMs:1000});
function budget(options={}){
  const b={...LIMITS,...options,ops:0,start:Date.now()};
  b.tick=()=>{if(++b.ops>b.maxOps||(b.ops%256===0&&Date.now()-b.start>b.maxMs))throw Error('LRD resource guard');};
  return b;
}
function nat(x){
  if(typeof x!=='bigint'&&(typeof x!=='number'||!Number.isSafeInteger(x)))throw TypeError('safe integer or BigInt required');
  x=BigInt(x);if(x<0n)throw Error('negative integer');return x;
}
const icmp=(a,b)=>a<b?-1:a>b?1:0;
function row(raw,b=budget()){
  if(raw===null)return null;
  if(!Array.isArray(raw)||!raw.length||raw.length>b.maxDegree+1)throw Error('LRD row shape guard');
  const out=raw.map(x=>{b.tick();return nat(x);});
  while(out.length>1&&out.at(-1)===0n)out.pop();return out;
}
function rowCmp(a,b){
  if(a===null)return b===null?0:1;if(b===null)return -1;
  if(a.length!==b.length)return icmp(a.length,b.length);
  for(let i=a.length-1;i>=0;i--){const c=icmp(a[i],b[i]);if(c)return c;}return 0;
}
const finiteRow=a=>a!==null&&a.length===1;
const rowKey=a=>a===null?'W':a.join(',');
function rowText(a){
  if(a===null)return 'w^w';const out=[];
  for(let d=a.length-1;d>=0;d--){
    if(a[d]===0n)continue;
    out.push(d===0?String(a[d]):(d===1?'w':'w^'+d)+(a[d]===1n?'':'*'+a[d]));
  }return out.join('+')||'0';
}
function rowFS(a,t,b=budget()){
  t=nat(t);if(t>b.maxIndex)throw Error('LRD row index guard');
  if(a===null){
    const d=Number(t)+1;if(d>b.maxDegree)throw Error('LRD row degree guard');
    const result=Array(d+1).fill(0n);result[d]=1n;return result;
  }
  if(a.length===1&&a[0]===0n)return [0n];
  const result=[...a],d=result.findIndex(x=>x!==0n);result[d]--;
  if(d>0)result[d-1]=t+1n;
  return row(result,b);
}
function packet(a,bIndex,b=budget()){
  // Finite rows retain the ENTIRE old RPD rule exactly, including nonstandard graphs.
  if(finiteRow(a))return [];
  bIndex=nat(bIndex);if(bIndex>b.maxIndex)throw Error('LRD packet index guard');
  const found=new Map([['0',[0n]]]);
  for(let t=0n;t<=bIndex;t++){
    b.tick();const lower=rowFS(a,t,b);
    if(rowCmp(lower,a)>=0)throw Error('LRD packet did not lower row');
    found.set(rowKey(lower),lower);
  }
  return [...found.values()].sort(rowCmp);
}
function atomCmp(a,b){
  const k=rowCmp(a[0],b[0]);if(k)return k;
  for(let i=1;i<4;i++){const c=icmp(a[i],b[i]);if(c)return c;}return 0;
}
const atomKey=e=>rowKey(e[0])+'|'+e.slice(1).join(',');
function close(g,b=budget()){
  const size=nat(g.size);if(size>b.maxWidth)throw Error('LRD width guard');
  const atoms=new Map(),groups=new Map();let keyChars=0,groupChars=0;
  for(const e of g.atoms){
    if(e.length!==4)throw Error('four fields required');
    const k=row(e[0],b),q=nat(e[1]),p=nat(e[2]),j=nat(e[3]);
    if(!(q<=p&&p<j&&j<size))throw Error('invalid relation');
    const groupId=rowKey(k)+'|'+p+','+j,previous=groups.get(groupId);
    if(!previous){groupChars+=groupId.length;if(groupChars>32000000)throw Error('LRD key memory guard');}
    if(!previous||q>previous[1])groups.set(groupId,[k,q,p,j]);
  }
  // Merge root ranges before expanding: avoid quadratic re-closing of closed input.
  for(const [k,q,p,j] of groups.values()){
    for(let u=0n;u<=q;u++){
      b.tick();const a=[k,u,p,j],id=atomKey(a);
      if(!atoms.has(id)){keyChars+=id.length;if(keyChars>32000000)throw Error('LRD key memory guard');}
      atoms.set(id,a);
      if(atoms.size>b.maxAtoms)throw Error('LRD atom guard');
    }
  }
  return {size,atoms:[...atoms.values()].sort((a,c)=>{b.tick();return atomCmp(a,c);})};
}
const seed=()=>({size:2n,atoms:[[null,0n,0n,1n]]});
function drop(g){return g.size===0n?g:{size:g.size-1n,atoms:g.atoms.filter(e=>e[3]<g.size-1n)};}
const end=g=>g.atoms.filter(e=>e[3]===g.size-1n);
function controller(g){const es=end(g);return es.length?es.reduce((a,b)=>atomCmp(a,b)<0?b:a):null;}
function parameters(g,n,b){
  n=nat(n);if(n>b.maxIndex)throw Error('LRD index guard');
  const e=controller(g);if(n===0n||!e)return null;
  const [K,r,c]=e,x=g.size-1n,L=x-c;
  if(x+n*L>b.maxWidth)throw Error('LRD width guard');
  return {e,K,r,c,x,L,n,base:drop(g).atoms,templates:end(g)};
}
function step(g,n,b=budget()){
  const p=parameters(g,n,b);if(!p)return drop(g);
  const {K,r,c,x,L,base,templates}=p,atoms=[];
  const emit=a=>{if(atoms.length>=1000000)throw Error('LRD temporary relation guard');atoms.push(a);};
  for(let v=0n;v<=p.n;v++){
    const f=i=>i<c?i:i+v*L;
    for(const [k,q,parent,j]of base){b.tick();emit([k,f(q),f(parent),f(j)]);}
    if(v===p.n)break;
    // Ordinary RPD seams, obtained from OLD endpoint templates.
    for(const [k,q,parent]of templates)for(let u=0n;u<=f(q);u++){
      b.tick();const d=rowCmp(k,K);
      if(d<0||d===0&&u<f(r))emit([k,u,f(parent),x+v*L]);
    }
    // New demands: lower rows at the transported control parent, all valid roots.
    // Their intended semantic source is generalized R.lower_block, not templates.
    for(const delta of packet(K,v,b))for(let u=0n;u<=f(c);u++){
      b.tick();emit([delta,u,f(c),x+v*L]);
    }
  }
  const out=close({size:x+p.n*L,atoms},b);
  if(compare(out,g)>=0)throw Error('LRD one-step descent assertion');
  return out;
}
// Independent append construction for checking the closed formula and prefix law.
function appendStep(g,n,b=budget()){
  const p=parameters(g,n,b);if(!p)return drop(g);
  const {K,r,c,x,L,base,templates}=p;let out=drop(g);
  for(let v=0n;v<p.n;v++){
    const f=i=>i<c?i:i+v*L,move=i=>i<c?i:i+(v+1n)*L;
    const additions=base.map(([k,q,parent,j])=>{b.tick();return [k,move(q),move(parent),move(j)];});
    for(const [k,q,parent]of templates){
      const allowed=rowCmp(k,K)<0?f(q):rowCmp(k,K)===0?(f(q)<f(r)-1n?f(q):f(r)-1n):-1n;
      for(let u=0n;u<=allowed;u++){b.tick();additions.push([k,u,f(parent),x+v*L]);}
    }
    for(const delta of packet(K,v,b))for(let u=0n;u<=f(c);u++){
      b.tick();additions.push([delta,u,f(c),x+v*L]);
    }
    out=close({size:x+(v+1n)*L,atoms:[...out.atoms,...additions]},b);
  }
  return out;
}
function colCmp(a,b){
  let c=icmp(a[1],b[1]);if(c)return c;c=rowCmp(a[0],b[0]);return c||icmp(a[2],b[2]);
}
function columns(g){
  const result=Array.from({length:Number(g.size)},()=>[]);
  for(const [k,q,p,j]of g.atoms)result[Number(j)].push([k,p,q]);
  for(const col of result)col.sort((a,b)=>-colCmp(a,b));return result;
}
function compare(g,h){
  const a=columns(g),b=columns(h);
  for(let j=0;j<Math.min(a.length,b.length);j++){
    for(let i=0;i<Math.min(a[j].length,b[j].length);i++){const c=colCmp(a[j][i],b[j][i]);if(c)return c;}
    const c=icmp(a[j].length,b[j].length);if(c)return c;
  }return icmp(a.length,b.length);
}
function fullText(g){return g.size===0n?'∅':columns(g).map(c=>'['+c.map(([k,p,q])=>'('+[rowText(k),p,q].join(',')+')').join(',')+']').join('');}
function text(g){
  if(g.size===0n)return '∅';
  return columns(g).map(col=>{
    const seen=new Set(),groups=[];
    for(const [k,p,q]of col){
      const id=p+'|'+rowKey(k);if(seen.has(id))continue;seen.add(id);
      groups.push('('+[rowText(k),p,q].join(',')+')');
    }return '['+groups.join(',')+']';
  }).join('');
}
function key(g){return g.size+'|'+g.atoms.map(atomKey).join(';');}
function prefix(g,h){return g.size<=h.size&&key(g)===key({size:g.size,atoms:h.atoms.filter(e=>e[3]<g.size)});}
function evaluate(indices,b=budget()){
  if(!Array.isArray(indices)||indices.length>4096)throw Error('LRD trace length guard');
  let g=seed();for(const n of indices){b.tick();g=step(g,n,b);}return g;
}

// Appended inside the standalone bundle, after the unchanged LRD core.
const esc=s=>String(s).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;');
function parseRow(s,b){
  if(s==='w^w')return null;
  const a=[0n];
  for(const term of s.split('+')){
    const m=term.match(/^w(?:\^(\d+))?(?:\*(\d+))?$/);
    if(m){const d=m[1]===undefined?1:Number(m[1]);if(!Number.isSafeInteger(d)||d<1||d>b.maxDegree)throw Error('LRD row degree guard');
      while(a.length<=d)a.push(0n);a[d]+=BigInt(m[2]??1);
    }else if(/^\d+$/.test(term))a[0]+=BigInt(term);
    else throw Error('行号格式：0、w、w^2*3+w+1 或 w^w');
  }return row(a,b);
}
function parse(raw,b=budget()){
  if(typeof raw!=='string'||raw.length>8000000)throw Error('LRD input guard');
  const s=raw.replace(/\s/g,'').replace(/ω/g,'w');
  if(s==='0'||s==='∅')return {size:0n,atoms:[]};
  if(s==='1')return {size:1n,atoms:[]};
  if(/^T(?:\[\d+\])*$/.test(s)){
    const indices=[...s.matchAll(/\[(\d+)\]/g)].map(m=>BigInt(m[1]));return evaluate(indices,b);
  }
  let pos=0,j=0n;const atoms=[];
  while(pos<s.length){
    b.tick();if(j>=b.maxWidth)throw Error('LRD width guard');
    if(s[pos++]!=='[')throw Error('每列用方括号；关系为 (行号,父列,最大根)。');
    if(s[pos]!==']')for(;;){
      const m=s.slice(pos).match(/^\(([^,()\[\]]+),(\d+),(\d+)\)/);
      if(!m)throw Error('关系格式错误；应为 (行号,父列,最大根)。');
      atoms.push([parseRow(m[1],b),BigInt(m[3]),BigInt(m[2]),j]);pos+=m[0].length;
      if(atoms.length>b.maxAtoms)throw Error('LRD atom guard');
      if(s[pos]!==',')break;pos++;
    }
    if(s[pos++]!==']')throw Error('缺少列结束符 ]');j++;
  }
  if(!j)throw Error('空图请输入 ∅');return close({size:j,atoms},b);
}
const plain=raw=>text(parse(raw));
const listHTML=raw=>'<span style="white-space:nowrap;font-family:inherit">'+esc(plain(raw))+'</span>';
const latex=raw=>plain(raw)==='∅'?'\\varnothing':'\\text{'+plain(raw).replace(/\^/g,'\\^{}')+'}';
const fs=(raw,n)=>{const b=budget();return text(step(parse(raw,b),n,b));};

// Count threshold-normalisations, not a full fundamental-sequence descent.
// A profile stores max parent at each (row,root); that group is removed together.
function countColumns(g,options={}){
  const maxWork=Math.min(options.maxWork??30000000,30000000),start=Date.now();
  let work=0,cells=0;
  const fail=()=>{throw Error('LRD count guard: 计数达到保护上限；请查看列表，未返回近似数字。');};
  const tick=()=>{if(++work>maxWork||((work&255)===0&&Date.now()-start>1000))fail();};
  const pairCmp=(a,b)=>rowCmp(a.k,b.k)||icmp(a.q,b.q);
  const rows=Array.from({length:Number(g.size)},()=>new Map());
  function put(map,k,q,p){tick();const id=rowKey(k)+'|'+q,old=map.get(id);if(!old||old.p<p)map.set(id,{k,q,p});}
  for(const [k,q,p,j] of g.atoms)put(rows[Number(j)],k,q,p);
  const memo=new Map();
  function normalise(c,cut){
    tick();const id=c+':'+(cut?rowKey(cut.k)+'|'+cut.q:'all'),saved=memo.get(id);if(saved)return saved;
    const active=new Map(rows[c]);let steps=0n;
    for(;;){
      let top=null;
      for(const item of active.values()){tick();if(!top||pairCmp(item,top)>0)top=item;}
      if(!top||(cut&&pairCmp(top,cut)<0))break;
      active.delete(rowKey(top.k)+'|'+top.q);
      if(top.p>=BigInt(c))throw Error('计数父列必须严格向左');
      const sub=normalise(Number(top.p),top);steps+=1n+sub.steps;
      for(const item of sub.rest.values())put(active,item.k,item.q,item.p);
      // Exactly V_0: fresh lower rows, all roots up to the selected parent.
      for(const k of packet(top.k,0n))for(let q=0n;q<=top.p;q++)put(active,k,q,top.p);
    }
    cells+=active.size;if(memo.size>=65536||cells>2000000)fail();
    const result={steps,rest:active};memo.set(id,result);return result;
  }
  const values=rows.map((_,j)=>normalise(j,null).steps+1n);
  return {values,work,memo: memo.size};
}
function numberPlain(raw){
  try{const values=countColumns(parse(raw)).values;return values.length?values.join(','):'0';}
  catch(e){if(!String(e.message).includes('count guard'))throw e;return '（计数超限；请查看列表）';}
}
function groups(g){
  const map=new Map();for(const [k,q,p,j]of g.atoms){const id=rowKey(k)+'|'+p+'|'+j;
    const old=map.get(id);if(!old||q>old.q)map.set(id,{k,q,p,j,id});}
  return [...map.values()];
}
// All actual rows and all parent edges are drawn. No omitted/local graph.
function diagram(raw,data={}){
  const g=parse(raw),nodes=groups(g),layers=[...new Map(nodes.map(n=>[rowKey(n.k),n.k])).values()].sort(rowCmp);
  if(nodes.length>15000||layers.length>2048)throw Error('LRD drawing guard: 完整图超限，不绘制局部图');
  const gap=Math.max(40,Math.min(160,Number(data.column_gap)||56));
  const left=Math.max(80,...layers.map(k=>rowText(k).length*8+24));
  let offset=65;const sections=[];
  for(const k of layers){
    const local=nodes.filter(n=>rowCmp(n.k,k)===0).sort((a,b)=>icmp(a.j,b.j)||icmp(a.p,b.p));
    const tops=Array(Number(g.size)).fill(0);
    for(const n of local){n.target=tops[Number(n.p)];n.track=Math.max(tops[Number(n.j)]+1,n.target+1);tops[Number(n.j)]=n.track;}
    const height=(Math.max(0,...tops)+1)*28;sections.push({k,local,offset,height});offset+=height+20;
  }
  const width=Math.max(440,left+Number(g.size)*gap+30),height=offset+60;
  if(width>32760||height>32760||width*height>100000000)throw Error('LRD drawing guard: 完整画布超限，不绘制局部图');
  const elements=[],extra_text=[],black={type:'black'},gray={type:'gray'},red={type:'red'};
  const x=j=>left+Number(j)*gap,y=z=>data.invert_vertical?z:height-45-z;
  const line=(x1,y1,x2,y2,color,meta)=>elements.push({type:'line',x1,y1,x2,y2,stroke:true,stroke_color:color,width:1,_lrd:meta});
  const dot=(xx,yy,color)=>elements.push({type:'circle',x:xx,y:yy,r:2.6,fill:true,fill_color:color,stroke:false});
  const label=(s,xx,yy,color=black,align='center',size=12)=>extra_text.push({text:String(s),x:xx,y:yy,color,align,size});
  for(let j=0n;j<g.size;j++){line(x(j),y(25),x(j),y(offset),gray);label(j,x(j),y(10));}
  for(const section of sections){
    const base=section.offset;label(rowText(section.k),left-15,y(base),black,'right');
    line(left-5,y(base),width-15,y(base),gray);
    const anchors=new Set();for(const n of section.local)if(!n.target)anchors.add(String(n.p));
    for(const p of anchors)dot(x(p),y(base),gray);
    for(const n of section.local){const yy=y(base+n.track*28),yp=y(base+n.target*28);
      line(x(n.j),yy,x(n.p),yp,black,{row:rowText(n.k),q:String(n.q),p:String(n.p),j:String(n.j)});
      dot(x(n.j),yy,black);if(n.q>0n)label(n.q,x(n.j)-5,yy-9,red,'right');
    }
  }
  label('列号从 0 起；红字 t 表示根 0…t，无红字即根 0。',12,height-25,gray,'left');
  label('灰线只作对齐；层内高度仅为排版，所有父列关系均保留。',12,height-8,gray,'left');
  return {width,height,elements,extra_text,_lrd:{complete:true,groups:nodes.length,columns:Number(g.size)}};
}
const color=c=>c?.type==='gray'?'#888':c?.type==='red'?'#bd5149':'currentColor';
function svg(raw){
  const d=diagram(raw);let s='<svg xmlns="http://www.w3.org/2000/svg" width="'+d.width+'" height="'+d.height+'" viewBox="0 0 '+d.width+' '+d.height+'" style="font-family:inherit;max-width:none" role="img" aria-label="LRD 完整山脉图">';
  for(const e of d.elements)if(e.type==='line')s+='<line x1="'+e.x1+'" y1="'+e.y1+'" x2="'+e.x2+'" y2="'+e.y2+'" stroke="'+color(e.stroke_color)+'"/>';
    else s+='<circle cx="'+e.x+'" cy="'+e.y+'" r="'+e.r+'" fill="'+color(e.fill_color)+'"/>';
  for(const t of d.extra_text)s+='<text x="'+t.x+'" y="'+t.y+'" font-size="'+t.size+'" dominant-baseline="middle" text-anchor="'+({center:'middle',left:'start',right:'end'}[t.align])+'" fill="'+color(t.color)+'">'+esc(t.text)+'</text>';
  return s+'</svg>';
}
function graphHTML(raw){try{return svg(raw);}catch(e){if(!String(e.message).includes('drawing guard'))throw e;return esc(e.message);}}
const listView={name:'列表',plain,html:listHTML,latex,from_display:plain};
register_notation({
  id:'lrd-candidate-v01',name:'LRD（层生成反射图·候选）',simple_name:'LRD',
  description:[
    '候选记号：整体良序和显著强于 RPD 尚未证明。',
    '输入 T 或 T[2][1]；也可输入列列表。三元组 (行号,父列,最大根)，行号如 w^2+w+1、w^w。',
    '标准式仅指 T 的后代；手工列表只检查图结构，不判定标准可达性。',
    '[0] 删末列；[n] 是 [n+1] 的完整列前缀。直接按列比较；计数序列仅显示，不参与比较或输入。',
    '计数含最终删列，空关系列为 1；正指标展开在旧末列位置恰好减 1，随后可能追加列。',
    '等价表示提供列表、计数序列、山脉图。列表与数字继承网页字体；山脉图请用 HTML 或原生显示图表。',
    '图横向按列，纵向按实际出现的行号；层内错层仅为排版。红字 t 表示根 0…t，不标即根 0。',
    '所有运算设时间及规模保护；超限拒绝，不返回截断图或近似计数。'
  ],
  display:listView,
  display_equiv:{'计数序列':{name:'计数序列',plain:numberPlain,html:raw=>'<span style="white-space:nowrap;font-family:inherit">'+esc(numberPlain(raw))+'</span>',latex:raw=>'\\text{'+numberPlain(raw)+'}'},
    '山脉图':{name:'山脉图',plain,html:graphHTML,latex,from_display:plain}},
  draw_diagram:{default_data:{column_gap:56,invert_vertical:false},settings:[
    {type:'number',name:'列间距',field_name:'column_gap',min:40,max:160},
    {type:'boolean',name:'上下翻转',field_name:'invert_vertical'}],draw_diagram:diagram},
  compare:(a,b)=>compare(parse(a),parse(b)),is_limit:raw=>end(parse(raw)).length>0,
  FS:fs,FS_alter:fs,FS_short:fs,init:()=>[text(seed()),'[]','∅'],
  debug:{parse,countColumns,groups,diagram,svg,localStep:raw=>{const g=parse(raw),h=step(g,1n);return {size:g.size,atoms:h.atoms.filter(e=>e[3]<g.size)};}}
});
})();
