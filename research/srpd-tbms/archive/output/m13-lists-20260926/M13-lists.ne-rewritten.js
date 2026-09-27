/* M13-lists: exact parent-list presentation of ordinary e0MN below (1,3).
 * Each column is a nonincreasing integer list, not a list of edge pairs.
 * Independent implementation; original ordinary e0MN by test_alpha0.
 */
(() => {
  'use strict';
  const TOP = 'Limit';
  const LIMITS = Object.freeze({ms: 1000, work: 2000000, cells: 1000000, width: 8192, text: 2000000});
  function budget(options = {}) {
    const cap = {...LIMITS, ...options}, start = Date.now();
    let work = 0;
    return () => {
      if (++work > cap.work || (work % 256 === 0 && Date.now() - start > cap.ms)) {
        const error = Error('M13-lists: calculation budget exceeded.');
        error.name = 'M13Budget'; throw error;
      }
    };
  }
  function natural(n) {
    if (!Number.isSafeInteger(n) || n < 0) throw Error('Expected a nonnegative safe integer');
  }
  function check(graph, tick = () => {}) {
    if (graph === TOP) return graph;
    if (!Array.isArray(graph) || graph.length > LIMITS.width) throw Error('Invalid/oversize graph');
    let cells = 0;
    graph.forEach((column,j) => {
      tick();
      if (!Array.isArray(column) || (cells += column.length) > LIMITS.cells) throw Error('Too many list entries');
      for (let t=0;t<column.length;t++) {
        tick(); const p=column[t]; natural(p);
        if (!(column.length <= p && p < j+1 && (!t || column[t-1] >= p)))
          throw Error('Require a nonincreasing column, with height <= every parent < child');
      }
    });
    return graph;
  }

  // Complete expansion: shift one block, replace the last column by a splice,
  // append the block, and finally remove the temporary last control column.
  function expand(graph,n,tick=()=>{}) {
    natural(n);
    if (graph===TOP) {
      if (n>=LIMITS.width || n*(n+1)/2>LIMITS.cells) throw Error('Output budget exceeded');
      return [[],...Array.from({length:n},(_,i)=>Array(i+1).fill(i+1))];
    }
    if (!graph.length || !n || !graph.at(-1).length) return graph.slice(0,-1);
    const result=graph.slice(), span=graph.length-graph.at(-1).at(-1);
    if (n>(LIMITS.width-graph.length)/span) throw Error('Output budget exceeded');
    let cells=graph.reduce((a,c)=>a+c.length,0);
    for (let b=0;b<n;b++) {
      tick();
      const column=result.at(-1), parent=column.at(-1), height=column.length;
      const move=source=>{
        tick();
        const size=source.length+(source.length>parent?span:0);
        if ((cells+=size)>LIMITS.cells) throw Error('Output budget exceeded');
        const moved=source.map(p=>{tick();return p>=parent?p+span:p;});
        const inserted=moved.length>parent?Array(span).fill(moved[parent]):[];
        return moved.slice(0,parent).concat(inserted,moved.slice(parent));
      };
      const copies=result.slice(parent).map(move);
      const seam=column.slice(0,-1).concat(result[parent-1].slice(height-1));
      cells+=seam.length-column.length;
      if (cells>LIMITS.cells) throw Error('Output budget exceeded');
      result[result.length-1]=seam;
      for (const copy of copies) result.push(copy);
    }
    return result.slice(0,-1);
  }

  function countResult(graph,tick=()=>{}) {
    if (graph===TOP) return {values:null,complete:true};
    const tables=[],values=graph.map(c=>c.length?null:1n);
    try {
      for (let j=0;j<graph.length;j++) {
        tick(); const column=graph[j],table=Array(column.length+1).fill(0n);
        for (let t=column.length-1;t>=0;t--) {
          tick(); table[t]=table[t+1]+1n+(tables[column[t]-1][t]??0n);
        }
        tables.push(table);values[j]=table[0]+1n;
      }
    } catch(error) {
      if(error.name!=='M13Budget') throw error;
      return {values,complete:values.every(v=>v!==null),reason:error.message};
    }
    return {values,complete:true};
  }
  function lex(a,b) {
    for(let i=0;i<Math.min(a.length,b.length);i++) {
      const c=Array.isArray(a[i])?lex(a[i],b[i]):Math.sign(a[i]-b[i]);if(c)return c;
    }
    return Math.sign(a.length-b.length);
  }
  const compare=(a,b)=>a===TOP?(b===TOP?0:1):b===TOP?-1:lex(a,b);

  function parse(raw,tick=budget()) {
    if(Array.isArray(raw))return check(raw,tick);
    if(typeof raw!=='string'||raw.length>LIMITS.text)throw Error('Invalid/oversize input');
    const text=raw.trim().replace(/\s+/g,''),route=/^(?:Limit(?:ofM13-lists)?|M13|Top|Ω)((?:\[\d+\])*)$/i.exec(text);
    if(route){let g=TOP;for(const m of route[1].matchAll(/\[(\d+)\]/g))g=expand(g,Number(m[1]),tick);return g;}
    if(text==='∅'||text==='')return [];
    if(/^\d+$/.test(text)) {
      const n=Number(text);natural(n);if(n>LIMITS.width)throw Error('Too many columns');
      return Array.from({length:n},()=>[]);
    }
    if(!/^(?:\[(?:\d+(?:,\d+)*)?\])+$/.test(text))throw Error('Use [][1][2,2], a natural number, or Limit[2][1]');
    return check(Array.from(text.matchAll(/\[([^\]]*)\]/g),m=>m[1]?m[1].split(',').map(Number):[]),tick);
  }
  const plainGraph=g=>g===TOP?'Limit of M13-lists':g.map(c=>'['+c.join(',')+']').join('')||'0';
  const plain=raw=>plainGraph(parse(raw));
  const html=s=>'<span style="font-family:inherit">'+s+'</span>';
  function counts(raw,options={}) {
    const g=parse(raw);if(g===TOP)return 'Limit of M13-lists';
    return countResult(g,budget(options)).values.map(v=>v===null?'?':String(v)).join(',')||'0';
  }
  function FS(raw,n){const tick=budget();return expand(parse(raw,tick),n,tick);}
  const api={TOP,LIMITS,check,expand,countResult,compare,parse,plainGraph,counts,budget};
  if(typeof module!=='undefined'&&module.exports)module.exports=api;
  if(typeof register_notation==='function')register_notation({
    id:'m13-parent-lists-v01',name:'M13-lists',simple_name:'M13-lists',
    description:[
      'M13 的父列表版：每列只是一串非增的正整数，数字是各级父列号，不再存 (父,行) 对。',
      '列号从 1 开始。长度 h 的第 j 列，每项满足 h≤父<j。Limit[n]=[][1][2,2]...[n,...,n]。',
      '与 M13-core 及普通 e0MN(1,3) 的默认展开逐指标交换，计数不变。不导入其他展开器。',
      '列表、计数序列两种显示。计算预算不足时保留已算计数，其他列显示 ?。',
      '按普通整数列表逐列字典序比较；有限项 [0] 删末列，基本列保持前缀。',
      '解析只验结构，标准性要求从 Limit 可达。三个 FS 入口均采用默认规则，不模拟原 FS_short。'
    ],
    display:{name:'列表',plain,html:raw=>html(plain(raw)),from_display:parse},
    display_equiv:{'计数序列':{name:'计数序列',plain:counts,html:raw=>html(counts(raw))}},
    FS,FS_alter:FS,FS_short:FS,compare:(a,b)=>compare(parse(a),parse(b)),
    is_limit:raw=>{const g=parse(raw);return g===TOP||!!g.at(-1)?.length;},
    init:()=>[TOP,[[]],[]],debug:api
  });
})();
