/* SRPD (formerly RPD0): zero-layer RPD in parent-list coordinates.
 * C_0=[] is an implicit root; visible columns start at 1.
 * Every column is nonincreasing, h-1 <= parent < child. INITIAL=[0].
 * The initial expression uses the SAME rule as every descendant.
 */
(() => {
  'use strict';
  const ROOT = Object.freeze([]), INITIAL = [[0]];
  const parentColumn = (graph,p)=>p?graph[p-1]:ROOT;
  const LIMITS = Object.freeze({ms:1000,work:2000000,cells:1000000,width:8192,text:2000000});
  function budget(options={}) {
    const cap={...LIMITS,...options},start=Date.now();let work=0;
    return ()=>{
      if(++work>cap.work || (work%256===0 && Date.now()-start>cap.ms)) {
        const error=Error('SRPD: calculation budget exceeded.');error.name='SRPDBudget';throw error;
      }
    };
  }
  function natural(n) {
    if(!Number.isSafeInteger(n)||n<0)throw Error('Expected a nonnegative safe integer');
  }
  function check(graph,tick=()=>{}) {
    if(!Array.isArray(graph)||graph.length>LIMITS.width)throw Error('Invalid/oversize graph');
    let cells=0;
    graph.forEach((column,j)=>{
      tick();if(!Array.isArray(column)||(cells+=column.length)>LIMITS.cells)throw Error('Too many list entries');
      for(let t=0;t<column.length;t++) {
        tick();const p=column[t];natural(p);
        if(!(column.length-1<=p&&p<j+1&&(!t||column[t-1]>=p)))
          throw Error('Require a nonincreasing column, with height-1 <= parent < child');
      }
    });return graph;
  }

  // One uniform finite expansion rule, including the initial term.
  function expand(graph,n,tick=()=>{}) {
    natural(n);
    if(!graph.length||!n||!graph.at(-1).length)return graph.slice(0,-1);
    const result=graph.slice(),span=graph.length-graph.at(-1).at(-1);
    if(n>(LIMITS.width-graph.length)/span)throw Error('Output width budget exceeded');
    let cells=graph.reduce((sum,c)=>sum+c.length,0);
    for(let b=0;b<n;b++) {
      tick();const column=result.at(-1),parent=column.at(-1);
      const move=source=>{
        tick();const size=source.length+(source.length>parent?span:0);
        if((cells+=size)>LIMITS.cells)throw Error('Output cell budget exceeded');
        const moved=source.map(p=>{tick();return p>=parent?p+span:p;});
        const inserted=moved.length>parent?Array(span).fill(moved[parent]):[];
        return moved.slice(0,parent).concat(inserted,moved.slice(parent));
      };
      const copies=result.slice(parent).map(move);
      const seam=column.slice(0,-1).concat(parentColumn(result,parent).slice(column.length-1));
      cells+=seam.length-column.length;
      if(cells>LIMITS.cells)throw Error('Output cell budget exceeded');
      result[result.length-1]=seam;
      for(const copy of copies)result.push(copy);
    }return result.slice(0,-1);
  }
  function countResult(graph,tick=()=>{}) {
    const tables=[[0n]],values=graph.map(c=>c.length?null:1n);
    try {
      for(let j=0;j<graph.length;j++) {
        tick();const column=graph[j],table=Array(column.length+1).fill(0n);
        for(let t=column.length-1;t>=0;t--) {
          tick();table[t]=table[t+1]+1n+(tables[column[t]][t]??0n);
        }
        tables.push(table);values[j]=table[0]+1n;
      }
    }catch(error){
      if(error.name!=='SRPDBudget')throw error;
      return {values,complete:values.every(v=>v!==null),reason:error.message};
    }return {values,complete:true};
  }
  function compare(a,b) {
    for(let i=0;i<Math.min(a.length,b.length);i++) {
      const c=Array.isArray(a[i])?compare(a[i],b[i]):Math.sign(a[i]-b[i]);if(c)return c;
    }return Math.sign(a.length-b.length);
  }
  function parse(raw,tick=budget()) {
    if(Array.isArray(raw))return check(raw,tick);
    if(typeof raw!=='string'||raw.length>LIMITS.text)throw Error('Invalid/oversize input');
    const text=raw.trim().replace(/\s+/g,''),route=/^(?:Limit(?:of(?:SRPD|RPD0))?|SRPD|RPD0|Top|Ω)((?:\[\d+\])*)$/i.exec(text);
    if(route){let g=INITIAL;for(const m of route[1].matchAll(/\[(\d+)\]/g))g=expand(g,Number(m[1]),tick);return g;}
    if(text==='∅'||text==='')return [];
    if(/^\d+$/.test(text)) {
      const n=Number(text);natural(n);if(n>LIMITS.width)throw Error('Too many columns');
      return Array.from({length:n},()=>[]);
    }
    if(!/^(?:\[(?:\d+(?:,\d+)*)?\])+$/.test(text))throw Error('Use [0], a parent list, or Limit[3][2]');
    return check(Array.from(text.matchAll(/\[([^\]]*)\]/g),m=>m[1]?m[1].split(',').map(Number):[]),tick);
  }
  const plainGraph=g=>g.map(c=>'['+c.join(',')+']').join('')||'0';
  const plain=raw=>plainGraph(parse(raw));
  const html=text=>'<span style="font-family:inherit">'+text+'</span>';

  // BMS-style node heights: same-row parent-chain depth, NOT an adjacency table.
  function heightGraph(graph,tick=()=>{}) {
    const heights=[ROOT];let cells=0;
    for(const column of graph) {
      tick();if((cells+=column.length)>LIMITS.cells)throw Error('Height display cell budget exceeded');
      heights.push(column.map((parent,row)=>{tick();return 1+(heights[parent][row]??0);}));
    }return heights.slice(1);
  }
  function parentsFromHeights(matrix,tick=()=>{}) {
    const full=[ROOT,...matrix],parents=[[]];
    for(let j=1;j<full.length;j++) {
      const column=[];parents.push(column);
      for(let row=0;row<full[j].length;row++) {
        let p=j;
        do {
          tick();p=row?parents[p]?.[row-1]:p-1;
          if(p===undefined||p<0)throw Error('No BMS-style parent for this height');
        }while((full[p][row]??0)>=full[j][row]);
        column.push(p);
      }
    }return parents.slice(1);
  }
  function fromHeightGraph(graph,tick=()=>{}) {
    if(!Array.isArray(graph)||graph.length>LIMITS.width)throw Error('Invalid/oversize height graph');
    let cells=0;
    const matrix=graph.map((heights,j)=>{
      tick();if(!Array.isArray(heights)||(cells+=heights.length)>LIMITS.cells)throw Error('Oversize height column');
      const column=heights.slice();
      for(const h of column){tick();natural(h);if(h>j+1)throw Error('Height exceeds possible parent-chain depth');}
      while(column.length&&column.at(-1)===0)column.pop();
      if(column.length>j+1||column.some(h=>h===0))throw Error('Only trailing zero heights may be omitted');
      return column;
    });
    const result=check(parentsFromHeights(matrix,tick),tick);
    if(compare(heightGraph(result,tick),matrix)!==0)throw Error('Heights do not equal the recovered parent-chain depths');
    return result;
  }
  function heightPlain(raw) {
    const tick=budget(),graph=parse(raw,tick),matrix=heightGraph(graph,tick);
    if(compare(parentsFromHeights(matrix,tick),graph)!==0)
      throw Error('此原始图不能用 BMS 式高度无损还原，请使用父列表；不能仅由语法合法性推出此视图适用。');
    return plainGraph(matrix);
  }
  function parseHeights(raw,tick=budget()) {
    if(Array.isArray(raw))return fromHeightGraph(raw,tick);
    if(typeof raw!=='string'||raw.length>LIMITS.text)throw Error('Invalid/oversize height input');
    const text=raw.trim().replace(/\s+/g,'');
    if(!text.startsWith('['))return parse(text,tick);
    if(!/^(?:\[(?:\d+(?:,\d+)*)?\])+$/.test(text))throw Error('Use BMS-style height lists such as [][1][2,1]');
    const graph=Array.from(text.matchAll(/\[([^\]]*)\]/g),m=>m[1]?m[1].split(',').map(Number):[]);
    return fromHeightGraph(graph,tick);
  }
  function counts(raw,options={}) {
    return countResult(parse(raw),budget(options)).values.map(v=>v===null?'?':String(v)).join(',')||'0';
  }
  function FS(raw,n){const tick=budget();return expand(parse(raw,tick),n,tick);}
  const api={ROOT,INITIAL,LIMITS,parentColumn,expand,countResult,check,compare,parse,plainGraph,counts,budget,
    heightGraph,parentsFromHeights,fromHeightGraph,heightPlain,parseHeights};
  if(typeof module!=='undefined'&&module.exports)module.exports=api;
  if(typeof register_notation==='function')register_notation({
    // Stored graph format changed: do not silently reinterpret old explicit-root states.
    id:'srpd-implicit-root-v02',name:'SRPD',simple_name:'SRPD',
    description:[
      '隐含根版：C₀=[] 不写出，可见列从 1 开始。长 h 的父列表非增，要求 h−1≤每个父<子列。',
      '初始式是 [0]，高度视图 [1]，计数 2；所有节点使用同一展开规则。没有可见列就是零。',
      '相比显式根版统一删去首空列，计数删首 1，有限底部重新编号；保留原 RPD(1,2) 的无限序型。普通 M13 后代计数直接对应，顶端指标差一。',
      '局部降低：删去末列最后一个数，再接父列从同一级开始的后缀；复制父值及对应行位置。',
      '层级列表是 BMS 式节点高度：每个格子的数是沿同层父链到无父节点的步数，缺格视作高度 0；不是按父列位置排列的邻接表。',
      '例如父项 [][1][2,2][3,3,3] 显示为高度 [][1][2,1][3,2,1]。换视图不改变内部图、展开、计数或比较。',
      '反向按 BMS 父项规则：最低层向左找，高层沿下一低层父链找第一个高度更低的节点；显示和解析都会检查无损往返。',
      '父列表按普通整数列表逐列字典序比较，其他视图使用同一内部比较。标准性要求从初始式可达；尚未一般证明高度视图覆盖所有标准式。',
      '旧显式根版的列表/高度字符串需删掉首个 []；新版注册 ID 已更新，避免把旧保存节点误当新格式。Limit[n] 路径可继续使用。',
      '计数为 BigInt；保留已知部分，超出预算的列显示 ?。三个 FS 接口都用默认规则。'
    ],
    display:{name:'列表',plain,html:raw=>html(plain(raw)),from_display:parse},
    display_equiv:{
      '计数序列':{name:'计数序列',plain:counts,html:raw=>html(counts(raw))},
      '层级列表':{name:'层级列表',plain:heightPlain,html:raw=>html(heightPlain(raw)),from_display:parseHeights}
    },
    FS,FS_alter:FS,FS_short:FS,compare:(a,b)=>compare(parse(a),parse(b)),
    is_limit:raw=>!!parse(raw).at(-1)?.length,init:()=>[INITIAL,[[]],[]],debug:api
  });
})();
