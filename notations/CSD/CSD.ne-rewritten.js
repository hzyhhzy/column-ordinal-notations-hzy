/* CSD — Contextual Stack Diagrams, standalone NER custom notation.
   Research candidate: full well-ordering and an ARD2 comparison are open.
   Mathematical source: csd.py and definition.zh-CN.md beside this file.
   No imports, network, storage, normalization, sorting, or dominance tests. */
(function () {
'use strict';
const TOP = 'Limit of CSD';
const CAP = Object.freeze({ms:1000, countMs:250, width:4096, cells:500000,
  word:32768, text:2000000, work:6000000, path:2048, digits:1024,
  cacheChars:8000000, cacheEntries:64, countBits:65536, countWork:2000000});
let active = null;
const cache = new Map(); let cacheChars = 0;
function limit(message) {
  const e = new Error('CSD：'+message+'超限；未返回截断或近似结果。');
  e.name = 'CSDLimit'; throw e;
}
function budget() {
  if (!active) {
    const b={start:Date.now(),work:0,cells:0,counts:new Map()};
    b.tick=()=>{if(++b.work>CAP.work || ((b.work&127)===0 && Date.now()-b.start>CAP.ms))
      limit('约 1 秒计算预算或工作量');};
    active=b;
    const clear=()=>{if(active===b)active=null;};
    if(typeof queueMicrotask==='function')queueMicrotask(clear);
    else Promise.resolve().then(clear);
  }
  active.tick(); return active;
}
function natural(n) {
  if(typeof n==='bigint' && n>=0n)return n;
  if(typeof n==='number' && Number.isSafeInteger(n) && n>=0)return BigInt(n);
  throw new Error('指标必须是非负安全整数或 BigInt。');
}
const cmp=(a,b)=>a<b?-1:a>b?1:0;
function wordCompare(a,b,ctx) {
  let d=cmp(a[0],b[0])||cmp(a.length,b.length); if(d)return d;
  for(let i=1;i<a.length;i++){ctx.tick();d=cmp(a[i],b[i]);if(d)return d;}
  return 0;
}
function make(cols,b) {
  if(cols.length>CAP.width)limit('列数');
  let cells=0,chars=0;const frozen=[],parts=[];
  for(let j=0;j<cols.length;j++) {
    b.tick();let previous=j;const col=[],text=[];
    for(const e of cols[j]) {
      b.tick();
      if(!Number.isSafeInteger(e.p)||e.p<0||e.p>=previous)
        throw new Error('第 '+j+' 列的父地址必须严格递减且小于列号；不自动排序或去重。');
      previous=e.p;
      if(!Array.isArray(e.w)||e.w.length<2)throw new Error('每个词必须有头地址和非空尾部。');
      if(e.w.length>CAP.word)limit('完整词长');
      cells+=1+e.w.length;if(cells>CAP.cells)limit('地址单元数');
      for(const a of e.w){b.tick();if(!Number.isSafeInteger(a)||a<0||a>j)
        throw new Error('第 '+j+' 列的词地址必须在 0…'+j+' 内。');}
      col.push(Object.freeze({p:e.p,w:Object.freeze(e.w.slice())}));
      text.push(e.p+':('+e.w[0]+';'+e.w.slice(1).join(',')+')');
    }
    const part='['+text.join(';')+']';chars+=part.length;if(chars>CAP.text)limit('完整列表文字');
    parts.push(part);frozen.push(Object.freeze(col));
  }
  return Object.freeze({cols:Object.freeze(frozen),key:parts.join('')||'∅',cells});
}
function compareGraphs(a,b,ctx) {
  if(a.key===b.key)return 0;
  for(let j=0;j<Math.min(a.cols.length,b.cols.length);j++) {
    const x=a.cols[j],y=b.cols[j];
    for(let i=0;i<Math.min(x.length,y.length);i++){
      ctx.tick();const d=cmp(x[i].p,y[i].p)||wordCompare(x[i].w,y[i].w,ctx);if(d)return d;
    }
    const d=cmp(x.length,y.length);if(d)return d;
  }
  return cmp(a.cols.length,b.cols.length);
}
function lowerWord(word,prefix,b) {
  const N=prefix.length,head=word[0];
  for(let i=word.length-1;i>=1;i--) {
    b.tick();if(word[i])return word.slice(0,i).concat(word[i]-1,Array(word.length-i-1).fill(N));
  }
  if(word.length>2)return [head,...Array(word.length-2).fill(N)];
  if(!head)return null;
  const out=[head-1,N];
  for(const e of prefix[head-1]) {
    b.tick();if(out.length+1+e.w.length>CAP.word)limit('再生后的完整词长');
    out.push(e.p);for(const a of e.w){b.tick();out.push(a);}
  }
  return out;
}
function finite(n,b) {
  if(n>BigInt(CAP.width))limit('有限数列数');
  return make(Array.from({length:Number(n)},()=>[]),b);
}
function seed(n,b) {
  n=natural(n);if(n>BigInt(CAP.width))limit('种子列数');
  return make(Array.from({length:Number(n)},(_,j)=>j?[{p:j-1,w:[j,j]}]:[]),b);
}
function step(g,n,b) {
  n=natural(n);const source=g.cols,x=source.length-1;
  if(x<0)return g;
  if(!n||!source[x].length)return make(source.slice(0,x),b);
  const old=source[x],control=old[old.length-1],c=control.p,L=x-c;
  if(BigInt(x)+n*BigInt(L)>BigInt(CAP.width))limit('展开后列数');
  const out=source.slice(0,x);
  function moveCol(col,block) {
    const phi=a=>a<c?a:a+block*L;
    return col.map(e=>{
      b.tick();b.cells+=1+e.w.length;if(b.cells>CAP.cells*4)limit('地址构造预算');
      return {p:phi(e.p),w:e.w.map(a=>{b.tick();return phi(a);})};
    });
  }
  for(let block=0;block<Number(n);block++) {
    b.tick();const seam=moveCol(old.slice(0,-1),block);
    const moved=moveCol([control],block)[0],lower=lowerWord(moved.w,out,b);
    if(lower)seam.push({p:moved.p,w:lower});
    seam.push(...moveCol(source[c],block+1));out.push(seam);
    for(let j=c+1;j<x;j++)out.push(moveCol(source[j],block+1));
  }
  const result=make(out,b);
  if(compareGraphs(result,g,b)>=0)throw new Error('CSD 内部严格下降断言失败。');
  return result;
}
function remember(raw,g) {
  const size=raw.length+(g===null?0:g.key.length);
  if(size>CAP.cacheChars/4)return;
  while(cache.size>=CAP.cacheEntries||cacheChars+size>CAP.cacheChars){
    const key=cache.keys().next().value;cacheChars-=cache.get(key).size;cache.delete(key);
  }
  cache.set(raw,{g,size});cacheChars+=size;
}
function parse(raw,b) {
  if(typeof raw!=='string')throw new Error('请输入字符串表达式。');
  if(raw.length>CAP.text)limit('输入文本');
  b.tick();if(cache.has(raw))return cache.get(raw).g;
  const s=raw.replace(/\s/g,''),digit=c=>c!==undefined&&c>='0'&&c<='9';let i=0,g;
  const take=c=>{b.tick();if(s[i++]!==c)throw new Error('格式错误：期待 '+c);};
  function number(){const start=i;while(digit(s[i])){b.tick();i++;if(i-start>CAP.digits)limit('整数字符');}
    if(i===start)throw new Error('格式错误：期待非负整数。');return BigInt(s.slice(start,i));}
  function coordinate(){const n=number();if(n>=BigInt(CAP.width))limit('地址');return Number(n);}
  function columnStart(){
    if(s[i]!=='[')return false;if(s[i+1]===']')return true;
    let j=i+1;while(digit(s[j])){b.tick();j++;}return j>i+1&&s[j]===':';
  }
  if(!s){g=finite(0n,b);}
  else if(s[i]==='∅'){i++;g=finite(0n,b);}
  else if(s.startsWith('LimitofCSD')){i=10;g=null;}
  else if(s.startsWith('Limit')){i=5;g=null;}
  else if(s.startsWith('Top')){i=3;g=null;}
  else if(s[i]==='A'){i++;g=seed(number(),b);}
  else if(digit(s[i]))g=finite(number(),b);
  else {
    const cols=[];let cells=0;
    while(columnStart()){
      if(cols.length>=CAP.width)limit('输入列数');take('[');const col=[];
      if(s[i]!==']')for(;;){
        const p=coordinate();take(':');take('(');const w=[coordinate()];take(';');
        w.push(coordinate());while(s[i]===','){take(',');if(w.length>=CAP.word)limit('输入词长');w.push(coordinate());}
        take(')');cells+=1+w.length;if(cells>CAP.cells)limit('输入地址单元');
        col.push({p,w});if(s[i]!==';')break;take(';');
      }
      take(']');cols.push(col);
    }
    if(!cols.length)throw new Error('请输入 A3、Limit[3]、自然数或 [][0:(1;1)] 形式的列表。');
    g=make(cols,b);
  }
  let paths=0;
  while(s[i]==='['){if(++paths>CAP.path)limit('展开路径');take('[');const n=number();take(']');g=g===null?seed(n,b):step(g,n,b);}
  if(i!==s.length)throw new Error('表达式后有未识别的内容。');
  remember(raw,g);return g;
}

// Exact closed-form local counts. No repeated full FS or local trajectory.
function counts(g,b,options={}) {
  if(g===null)return null;
  const maxWork=options.maxWork===undefined?CAP.countWork:options.maxWork;
  if(!Number.isSafeInteger(maxWork)||maxWork<0)throw new Error('maxWork 必须是非负安全整数。');
  if(options.maxWork===undefined&&b.counts.has(g.key))return b.counts.get(g.key);
  let work=0;const start=Date.now(),bound=1n<<BigInt(CAP.countBits),values=[];
  const tick=()=>{b.tick();if(++work>maxWork||((work&127)===0&&Date.now()-start>CAP.countMs))limit('计数预算');};
  const checked=x=>{if(x>=bound)limit('计数位数保护（不是 2^63 限制）');return x;};
  for(let j=0;j<g.cols.length;j++) {
    tick();const base=BigInt(j+1),recharge=[0n],inherited=[];
    const append=(rank,digit)=>{tick();return checked(base*(rank+1n)+BigInt(digit));};
    function tailRank(w,source=-1){
      tick();let rank=BigInt(w[1]===source?j:w[1]);
      for(let a=2;a<w.length;a++)rank=append(rank,w[a]===source?j:w[a]);return rank;
    }
    for(let h=0;h<j;h++) {
      tick();let rank=BigInt(j);
      for(const e of g.cols[h]){rank=append(rank,e.p);for(const a of e.w)rank=append(rank,a);}
      recharge.push(checked(recharge[h]+rank+1n));
    }
    function cost(w,source=-1){
      tick();return checked(tailRank(w,source)+1n+recharge[w[0]===source?j:w[0]]);
    }
    for(let p=0;p<j;p++){
      tick();let total=0n;
      for(const e of g.cols[p]){tick();total=checked(total+checked(cost(e.w,p)*(1n+inherited[e.p])));}
      inherited.push(total);
    }
    let total=1n;
    for(const e of g.cols[j]){tick();total=checked(total+checked(cost(e.w)*(1n+inherited[e.p])));}
    values.push(total);
  }
  const result=Object.freeze(values);
  if(options.maxWork===undefined)b.counts.set(g.key,result);return result;
}
const escape=s=>String(s).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;');
const html=s=>'<span style="font-family:inherit;white-space:nowrap">'+escape(s)+'</span>';
const latex=s=>s==='∅'?'\\varnothing':'\\text{'+s.replace(/[{}\\]/g,c=>'\\'+c)+'}';
const plain=raw=>{const g=parse(raw,budget());return g===null?TOP:g.key;};
function countPlain(raw){
  try{
    const b=budget(),g=parse(raw,b);if(g===null)return TOP;
    const ns=counts(g,b),parts=[];let chars=0;
    for(const n of ns){b.tick();const text=n.toString();chars+=text.length+1;if(chars>CAP.text)limit('计数显示文本');parts.push(text);}
    return parts.join(',')||'0';
  }catch(e){if(e.name!=='CSDLimit')throw e;return '（计数超限；请查看列表，未给出近似值）';}
}
const fs=(raw,n)=>{n=natural(n);const b=budget(),g=parse(raw,b);return (g===null?seed(n,b):step(g,n,b)).key;};
register_notation({
  id:'csd-v01',name:'CSD',simple_name:'CSD',
  description:[
    'CSD：上下文栈图。研究候选；全局良序及与 ARD2、wY 的序型比较尚未证明。',
    '每列是一串父地址严格递减的任务 p:(头;地址尾部)，所有词地址不超过子列，允许 SELF。没有轮廓筛选、排序、去重或覆盖判断。',
    '降低头地址时，读取该地址前一列的完整栈，重建尾部。后面的复制块可能读取本次刚生成的前列。',
    '有限非零式 [0] 删末列；基本列项按完整列组成前缀链。比较只看最早不同列及其中记录，不计算计数。',
    '输入 A3、A3[2][1]、Limit[3]、自然数或 [][0:(1;1)][1:(2;2)]。自然数表示空列数量；手写输入只检查语法，不保证标准可达。',
    '默认列表；等价表示中另有计数序列，不重复添加列表按钮。计数由精确 BigInt 公式计算，不跑漫长的迭代轨道，也不作反向解析。',
    '约 1 秒共享计算预算，计数另限约 250 毫秒；输出、词长和整数位数另有限制。超限不代表数学不终止，绝不填近似数。',
    'FS、FS_alter、FS_short 使用完全相同的数学规则，无指标偏移。独立脚本，无网络或持久存储。'
  ],
  display:{name:'列表',plain,html:raw=>html(plain(raw)),latex:raw=>latex(plain(raw)),from_display:plain},
  display_equiv:{'计数序列':{name:'计数序列',plain:countPlain,html:raw=>html(countPlain(raw)),latex:raw=>latex(countPlain(raw))}},
  FS:fs,FS_alter:fs,FS_short:fs,
  compare:(a,c)=>{const b=budget(),x=parse(a,b),y=parse(c,b);return x===null?(y===null?0:1):y===null?-1:compareGraphs(x,y,b);},
  is_limit:raw=>{const g=parse(raw,budget());return g===null||!!g.cols[g.cols.length-1]?.length;},
  init:()=>[TOP,'[]','∅'],
  debug:{limits:CAP,parse:raw=>parse(raw,budget()),seed:n=>seed(n,budget()),
    counts:(raw,options)=>{const b=budget();return counts(parse(raw,b),b,options);},
    step:(g,n)=>step(g,n,budget()),lower_word:(w,prefix)=>lowerWord(w,prefix,budget())}
});
})();
