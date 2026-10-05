/* TBMS <= SRPD: symmetric-tower edition; not an order embedding.
 * Scope: descendants of ordinary TBMS ()(1^()(1,1)), abbreviated ()(1^e0).
 * Standalone NER bundle. No imports, network, DOM, or Node required at runtime.
 * Native TBMS: https://smilelee-lyx.github.io/ne-rewritten/
 * SRPD: implicit-root edition, 2026-09-26. Source hashes are in debug.provenance.
 */
(function () {
  'use strict';
  const provenance = {
  "tbms": {
    "file": ".research-ne-rewritten/src/notations/BM-like/TBM.ts",
    "sha256": "ebc510ea3e2a032de6c793d25a84d3741e8b427b7f0d225b32fa49326b6be1bb"
  },
  "srpd": {
    "file": "output/m13-lists-20260926/SRPD.ne-rewritten.js",
    "sha256": "fdbd0d0788afe0cd6949cb280ffea4c85813bbd6d5e47d04e6a078e00bbee85a"
  },
  "cover": {
    "file": "output/tbms-e0mn-bridge-20260925/epsilon-row-cover.cjs",
    "sha256": "e5757a1bf40242d5dd70587b1785c90c843aeb8fe8fe6150ac50cb659910b500"
  },
  "symmetric": {
    "file": "output/tbms-e0mn-bridge-20260925/symmetric-tower-cover.cjs",
    "sha256": "75d273fdee0d4f9bb476d02354c577d90dc836042fdc68c163e4b2fc7025d8d3"
  }
};
  const LIMITS = Object.freeze({ms: 900, work: 12000000, width: 768,
    sourceWidth: 2048, cells: 160000, sourceCells: 80000, height: 24,
    route: 512, index: 2048, stateEntries: 24, stateChars: 3000000});
  let active = null;
  class BudgetStop extends Error {
    constructor(message) {super(message); this.name = 'BudgetStop';}
  }
  function budgetTick() {
    if (!active) return;
    if (++active.work > active.limit || (active.work % 128 === 0 && Date.now() > active.deadline))
      throw new BudgetStop('达到本次计算的时间／工作量上限');
  }
  function bounded(fn, options = {}) {
    const previous = active;
    active = {work: 0, limit: options.work ?? LIMITS.work,
      deadline: Date.now() + (options.ms ?? LIMITS.ms)};
    try {return fn();} finally {active = previous;}
  }
  function assert(value, message = 'simulation invariant failed') {
    if (!value) {const e = Error(message); e.name = 'SimulationInvariant'; throw e;}
  }
  assert.equal = (a, b, message) => assert(a === b, message ?? `${a} != ${b}`);
  const natural = n => assert(Number.isSafeInteger(n) && n >= 0, '需要非负安全整数');
  function clone(value, seen = new Map()) {
    budgetTick();
    if (value === null || typeof value !== 'object') return value;
    if (seen.has(value)) return seen.get(value);
    const out = value instanceof Map ? new Map() : Array.isArray(value) ? [] : {};
    seen.set(value, out);
    if (value instanceof Map) for (const [k, v] of value) out.set(k, clone(v, seen));
    else for (const k of Object.keys(value)) out[k] = clone(value[k], seen);
    return out;
  }
  const htmlEscape = text => String(text).replace(/[&<>"']/g,
    c => ({'&':'&amp;', '<':'&lt;', '>':'&gt;', '"':'&quot;', "'":'&#39;'}[c]));

  // The latest user-supplied SRPD is bundled without changing its rules.
  const S = (function () {
    const module = {exports: {}}, register_notation = undefined;
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

    return module.exports;
  })();

  // Only these three generic comparators are imported by native TBMS.
  const utils = {
    number_compare: (a,b) => a === b ? 0 : a < b ? -1 : 1,
    lex_compare(a,b,cmp) {
      for (let j=0;j<Math.min(a.length,b.length);j++) {budgetTick(); const c=cmp(a[j],b[j]); if(c)return c;}
      return Math.sign(a.length-b.length);
    },
    tuple_lex_compare(a,b,comparators) {
      for(let j=0;j<comparators.length;j++) {budgetTick(); const c=comparators[j]?.(a[j],b[j])??0;if(c)return c;}
      return 0;
    },
  };
  // Exact default LNZ rule, without the upstream unbounded result cache.
  // This explorer intentionally uses that SAME default rule in all FS slots.
  const notationUtils = {
    FS_default_LNZ_variant(expand, compare, isInfinity, infinityFS, isLimit) {
      const FS = (a,n) => isInfinity(a) ? infinityFS(n) : expand(a,isLimit(a)?n:0);
      return {FS, FS_short: FS};
    },
  };
  const B = (function (exports, require) {
    "use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.TBM = void 0;
exports.entry_compare = entry_compare;
exports.column_compare = column_compare;
exports.compare = compare;
exports.vertical_compare = vertical_compare;
exports.index_after = index_after;
exports.vertical_parent = vertical_parent;
exports.vertical_add = vertical_add;
exports.parents = parents;
exports.column_verticals = column_verticals;
exports.is_one = is_one;
exports.to_vertical = to_vertical;
exports.expand_limit = expand_limit;
exports.column_sub = column_sub;
exports.const_column = const_column;
exports.ascension_threshold = ascension_threshold;
exports.column_add = column_add;
exports.column_truncate = column_truncate;
exports.column_mul = column_mul;
exports.copy_column = copy_column;
exports.expand = expand;
exports.is_infinity = is_infinity;
exports.ONE = ONE;
exports.INFINITY = INFINITY;
exports.display = display;
exports.from_display = from_display;
exports.infinity_FS = infinity_FS;
const utils_ts_1 = require("@/utils.ts");
const notation_utils_ts_1 = require("@/notations/notation_utils.ts");
function entry_compare(e1, e2) {
    budgetTick();
    return (0, utils_ts_1.tuple_lex_compare)(e1, e2, [utils_ts_1.number_compare, compare]);
}
function column_compare(c1, c2) {
    budgetTick();
    return (0, utils_ts_1.lex_compare)(c1, c2, entry_compare);
}
function compare(a, b) {
    budgetTick();
    return (0, utils_ts_1.lex_compare)(a, b, column_compare);
}
function vertical_compare(v1, v2) {
    budgetTick();
    return (0, utils_ts_1.lex_compare)(v1, v2, compare);
}
function index_after(V, pos) {
    budgetTick();
    for (let k = 0; k < V.length; k++) {
        budgetTick();
        if (vertical_compare(V[k], pos) > 0)
            return k;
    }
    return V.length;
}
function vertical_parent(v, Pi, Vi) {
    budgetTick();
    for (let k = 0; k < Vi.length; k++) {
        budgetTick();
        if (vertical_compare(Vi[k], v) >= 0)
            return Pi[k];
    }
    return undefined;
}
function vertical_add(v1, v2) {
    budgetTick();
    if (v1.length === 0)
        return v2.slice();
    if (v2.length === 0)
        return v1.slice();
    const first2 = v2[0];
    let i = v1.length;
    while (i > 0 && compare(v1[i - 1], first2) < 0) {
        budgetTick();
        i--;
    }
    return v1.slice(0, i).concat(v2);
}
function parents(m, V) {
    budgetTick();
    const P = [];
    for (let i = 0; i < m.length; i++) {
        budgetTick();
        const Pi = [];
        for (let j = 0; j < m[i].length; j++) {
            budgetTick();
            const [value] = m[i][j];
            const pos = j === 0 ? [] : V[i][j - 1];
            let p = j === 0 ? i - 1 : Pi[j - 1][0];
            while (p >= 0) {
                budgetTick();
                if (m[p].length === 0) {
                    if (0 < value) {
                        Pi.push([p, 0]);
                        break;
                    }
                    p = -1;
                    break;
                }
                const j_p = j === 0 ? 0 : index_after(V[p], pos);
                if (j_p >= m[p].length) {
                    Pi.push([p, j_p]);
                    break;
                }
                const value_p = m[p][j_p][0];
                if (value_p < value) {
                    Pi.push([p, j_p]);
                    break;
                }
                const next = j === 0 ? [p - 1, 0] : vertical_parent(pos, P[p], V[p]);
                if (!next) {
                    p = -1;
                    break;
                }
                p = next[0];
            }
            if (p < 0)
                break;
        }
        P.push(Pi);
    }
    return P;
}
function column_verticals(col) {
    budgetTick();
    const result = [];
    let acc = [];
    for (const [, height_expr] of col) {
        budgetTick();
        acc = vertical_add(acc, [height_expr]);
        result.push(acc.slice());
    }
    return result;
}
function is_one(expr) {
    budgetTick();
    return expr.length === 1 && expr[0].length === 0;
}
function to_vertical(m) {
    budgetTick();
    const v = [];
    let prev = 0;
    for (let i = 1; i <= m.length; i++) {
        budgetTick();
        if (i === m.length || m[i].length === 0) {
            v.push(m.slice(prev, i));
            prev = i;
        }
    }
    return v;
}
function expand_limit(m, index) {
    budgetTick();
    const right = m.length - 1;
    const col = m[right];
    const last_idx = col.length - 1;
    const [v, h] = col[last_idx];
    const new_h = exports.TBM.FS(h, index);
    const segs = to_vertical(new_h);
    const result = m.slice();
    const new_entries = col.slice(0, last_idx);
    for (const seg of segs) {
        budgetTick();
        new_entries.push([v, seg]);
    }
    result[right] = new_entries;
    return result;
}
function expand_successor(m, index) {
    budgetTick();
    const V = m.map(column_verticals);
    const P = parents(m, V);
    const N = m.length - 1;
    const r = P[N][m[N].length - 1][0];
    const result = m.slice(0, N);
    const b = m[N].length > 1 ? V[N][m[N].length - 2] : [];
    const offset = column_sub(m[N], m[r]);
    const A = ascension_threshold(V, P, r, b);
    for (let w = 1; w <= index; w++) {
        budgetTick();
        for (let i = r; i < N; i++) {
            budgetTick();
            result.push(copy_column(m[i], offset, A[i], w));
        }
    }
    return result;
}
function column_sub(a, b) {
    budgetTick();
    const off = [];
    const Va = column_verticals(a);
    const Vb = column_verticals(b);
    for (let j = 0; j < a.length; j++) {
        budgetTick();
        const pos = j === 0 ? [] : Va[j - 1];
        const j_r = index_after(Vb, pos);
        const delta = a[j][0] - (j_r < Vb.length ? b[j_r][0] : 0);
        if (delta <= 0)
            break;
        off.push([delta, a[j][1]]);
    }
    return off;
}
function const_column(value, vertical) {
    budgetTick();
    return vertical.map((s) => [value, s]);
}
function ascension_threshold(V, P, r, b) {
    budgetTick();
    const A = [];
    for (let i = 0; i < V.length; i++) {
        budgetTick();
        if (i < r) {
            A.push([]);
            continue;
        }
        if (i === r) {
            A.push(b);
            continue;
        }
        let found;
        for (let j = 0; j < V[i].length; j++) {
            budgetTick();
            const pos = j === 0 ? [] : V[i][j - 1];
            const [col_p] = P[i][j];
            if (col_p < r) {
                found = pos;
                break;
            }
            if (vertical_compare(pos, A[col_p]) >= 0) {
                found = pos;
                break;
            }
            let new_pos = V[i][j];
            if (vertical_compare(new_pos, A[col_p]) >= 0) {
                found = A[col_p];
                break;
            }
        }
        A.push(found ?? V[i][V[i].length - 1]);
    }
    return A;
}
function column_add(a, b) {
    budgetTick();
    const res = [];
    let ai = 0, bi = 0;
    while (ai < a.length || bi < b.length) {
        budgetTick();
        if (ai >= a.length) {
            res.push([b[bi][0], b[bi][1]]);
            bi++;
        }
        else if (bi >= b.length) {
            res.push([a[ai][0], a[ai][1]]);
            ai++;
        }
        else {
            const ea = a[ai], eb = b[bi];
            const cmp = compare(ea[1], eb[1]);
            const h = cmp < 0 ? ea[1] : eb[1];
            res.push([ea[0] + eb[0], h]);
            if (cmp <= 0)
                ai++;
            if (cmp >= 0)
                bi++;
        }
    }
    return res;
}
function column_truncate(col, b) {
    budgetTick();
    const res = [];
    let ci = 0, vi = 0;
    while (ci < col.length && vi < b.length) {
        budgetTick();
        const e = col[ci];
        const vh = b[vi];
        const cmp = compare(e[1], vh);
        const h = cmp < 0 ? e[1] : vh;
        res.push([e[0], h]);
        if (cmp <= 0)
            ci++;
        if (cmp >= 0)
            vi++;
    }
    return res;
}
function column_mul(col, w) {
    budgetTick();
    return col.map(([v, e]) => [v * w, e]);
}
function copy_column(col_i, offset, A_i, w) {
    budgetTick();
    return column_add(col_i, column_mul(column_truncate(offset, A_i), w));
}
function expand(m, index) {
    budgetTick();
    if (m.length === 0)
        return m;
    const N = m.length - 1;
    const last_col = m[N];
    if (last_col.length === 0)
        return m.slice(0, N);
    const [, last_height] = last_col[last_col.length - 1];
    if (is_one(last_height)) {
        return expand_successor(m, index);
    }
    else {
        return expand_limit(m, index);
    }
}
function is_infinity(a) {
    budgetTick();
    return a.length > 0 && a[0].length > 0 && a[0][0][0] === Infinity;
}
function ONE() {
    budgetTick();
    return [[]];
}
function OMEGA() {
    budgetTick();
    return [[], [[1, ONE()]]];
}
function INFINITY() {
    budgetTick();
    return [[[Infinity, []]]];
}
function height_display(s, html) {
    budgetTick();
    if (s.length === 1)
        return undefined;
    if (compare(s, OMEGA()) === 0)
        return 'ω';
    return display(s, html);
}
function entry_display([v, s], html) {
    budgetTick();
    let sd = height_display(s, html);
    if (sd === undefined)
        return '' + v;
    if (html)
        return v + '<sup>' + sd + '</sup>';
    return v + '^' + sd;
}
function column_display(col, html) {
    budgetTick();
    return '(' + col.map((e) => entry_display(e, html)).join(',') + ')';
}
function display(m, html = false) {
    budgetTick();
    if (is_infinity(m))
        return 'Limit';
    return m.map((col) => column_display(col, html)).join('');
}
function from_display(str) {
    budgetTick();
    let i = 0;
    const s = str;
    function error() {
        budgetTick();
        throw new Error(`Illegal input string: ${s}`);
    }
    function skip_spaces() {
        budgetTick();
        while (i < s.length && s[i] === ' ') {
            budgetTick();
            i++;
        }
    }
    function parse_number() {
        budgetTick();
        skip_spaces();
        const start = i;
        while (i < s.length && s[i] >= '0' && s[i] <= '9') {
            budgetTick();
            i++;
        }
        if (start === i)
            error();
        return parseInt(s.substring(start, i), 10);
    }
    function parse_expr() {
        budgetTick();
        const result = [];
        skip_spaces();
        while (i < s.length && s[i] === '(') {
            budgetTick();
            result.push(parse_column());
            skip_spaces();
        }
        return result;
    }
    function parse_column() {
        budgetTick();
        skip_spaces();
        if (i >= s.length || s[i] !== '(')
            error();
        i++;
        const entries = [];
        skip_spaces();
        if (i < s.length && s[i] !== ')') {
            entries.push(parse_entry());
            skip_spaces();
            while (i < s.length && s[i] === ',') {
                budgetTick();
                i++;
                skip_spaces();
                if (i < s.length && s[i] === ')')
                    break;
                entries.push(parse_entry());
                skip_spaces();
            }
        }
        skip_spaces();
        if (i >= s.length || s[i] !== ')')
            error();
        i++;
        return entries;
    }
    function parse_height() {
        budgetTick();
        skip_spaces();
        if (i < s.length && (s[i] === 'ω' || s[i] === 'w')) {
            i++;
            return OMEGA();
        }
        return parse_expr();
    }
    function parse_entry() {
        budgetTick();
        const v = parse_number();
        skip_spaces();
        if (i < s.length && s[i] === '^') {
            i++;
            return [v, parse_height()];
        }
        return [v, ONE()];
    }
    skip_spaces();
    if (i + 5 <= s.length && s.slice(i, i + 5) === 'Limit') {
        i += 5;
        skip_spaces();
        if (i !== s.length)
            error();
        return INFINITY();
    }
    const result = parse_expr();
    skip_spaces();
    if (i !== s.length)
        error();
    return result;
}
function infinity_FS(index) {
    budgetTick();
    if (index === 0)
        return [[]];
    return [[], [[1, infinity_FS(index - 1)]]];
}
function is_limit(m) {
    budgetTick();
    if (is_infinity(m))
        return true;
    if (m.length === 0)
        return false;
    return m[m.length - 1].length > 0;
}
exports.TBM = {
    id: 'tbm',
    name: 'Transfinite Bashicu matrix',
    simple_name: 'TBMS',
    category_id: 'category-bm-like',
    display: {
        plain: (m) => display(m, false),
        html: (m) => display(m, true),
        from_display,
    },
    is_limit: is_limit,
    compare,
    ...(0, notation_utils_ts_1.FS_default_LNZ_variant)(expand, compare, is_infinity, infinity_FS, is_limit, display),
    credit_text_id: 'credit.tbm',
    init: () => {
        budgetTick();
        return [INFINITY(), []];
    },
};

    return exports;
  })({}, name => {
    if (name === '@/utils.ts') return utils;
    if (name === '@/notations/notation_utils.ts') return notationUtils;
    throw Error('Unexpected bundled import: '+name);
  });
  const EPSILON = B.TBM.FS(B.infinity_FS(3),1);

  // Small CNF helpers used by the published simulation; rows stay below e0.
  const nat = n => {natural(n);return n?[{exp:[],coeff:n}]:[];};
  function ordCompare(a,b) {
    budgetTick();
    for(let i=0;i<Math.min(a.length,b.length);i++) {
      const c=ordCompare(a[i].exp,b[i].exp);if(c)return c;
      if(a[i].coeff!==b[i].coeff)return Math.sign(a[i].coeff-b[i].coeff);
    }return Math.sign(a.length-b.length);
  }
  function ordAdd(a,b) {
    budgetTick();if(!b.length)return clone(a);
    let i=0;while(i<a.length&&ordCompare(a[i].exp,b[0].exp)>0){budgetTick();i++;}
    const out=clone(a.slice(0,i));
    if(i<a.length&&!ordCompare(a[i].exp,b[0].exp)) {
      const coeff=a[i].coeff+b[0].coeff;natural(coeff);
      return out.concat([{exp:clone(b[0].exp),coeff}],clone(b.slice(1)));
    }return out.concat(clone(b));
  }
  function ordRightDiff(a,b) {
    const c=ordCompare(a,b);assert(c<=0);if(!c)return [];
    let i=0;while(i<a.length&&i<b.length&&!ordCompare(a[i].exp,b[i].exp)&&a[i].coeff===b[i].coeff){budgetTick();i++;}
    if(i===a.length)return clone(b.slice(i));
    assert(i<b.length);
    const e=ordCompare(a[i].exp,b[i].exp);
    if(e<0)return clone(b.slice(i));
    assert(!e&&a[i].coeff<b[i].coeff);
    return [{exp:clone(b[i].exp),coeff:b[i].coeff-a[i].coeff},...clone(b.slice(i+1))];
  }
  function ordFS(src,n) {
    budgetTick();natural(n);if(!src.length)return [];
    const out=clone(src),last=out.at(-1);
    if(!last.exp.length){if(last.coeff===1)out.pop();else last.coeff--;return out;}
    out.pop();if(last.coeff>1)out.push({exp:clone(last.exp),coeff:last.coeff-1});
    const exponent=ordFS(last.exp,n);
    if(!last.exp.at(-1).exp.length){if(n)out.push({exp:exponent,coeff:n});}
    else out.push({exp:exponent,coeff:1});
    return out;
  }

  // Keep the proof program's sparse edge coordinates internally. Every finite
  // target FS delegates to the NEW SRPD rule, via an exact parent-list adapter.
  const M_TOP=[[],[{a:1,x:[{exp:nat(1),coeff:1}]}]];
  const isMTop=g=>g.length===2&&!g[0].length&&g[1].length===1&&g[1][0].a===1&&
    ordCompare(g[1][0].x,M_TOP[1][0].x)===0;
  function toLists(graph) {
    if(isMTop(graph))return [[0]];
    let cells=0;
    return graph.map(column=>{
      budgetTick();const out=[];
      for(const e of column) {
        assert(e.x.length===1&&!e.x[0].exp.length,'有限行适配器只接受有限行');
        const h=e.x[0].coeff;natural(h);natural(e.a);
        assert(h>out.length&&h<=e.a,'有限稀疏边行高／父号错误');
        cells+=h-out.length;if(cells>LIMITS.cells)throw new BudgetStop('SRPD 格数上限');
        while(out.length<h){budgetTick();out.push(e.a);}
      }return out;
    });
  }
  function fromLists(graph) {
    return graph.map(column=>{
      budgetTick();const out=[];
      for(let r=0;r<column.length;r++) {
        budgetTick();if(r+1===column.length||column[r+1]!==column[r])out.push({a:column[r],x:nat(r+1)});
      }return out;
    });
  }
  function graphCheck(g) {
    if(isMTop(g))return true;
    S.check(toLists(g),budgetTick);return true;
  }
  function targetFS(g,n) {
    natural(n);
    try {
      // SRPD[seed+1] equals the old M13[seed]; do not prepend an old root.
      return fromLists(S.expand(toLists(g),isMTop(g)?n+1:n,budgetTick));
    } catch(e) {
      if(/budget|Too many|oversize/i.test(e.message))throw new BudgetStop(e.message);
      throw e;
    }
  }
  function targetDown(g) {
    const lists=toLists(g),column=lists.at(-1),p=column.at(-1);
    assert(column.length>0&&p>0);
    return fromLists(lists.slice(0,-1).concat([
      column.slice(0,-1).concat(S.parentColumn(lists,p).slice(column.length-1))]));
  }
  function targetCompare(a,b) {
    // Exact sparse e0MN lexicographic comparison. It agrees with the finite
    // parent lists, without materializing both whole graphs for every macro.
    return utils.lex_compare(a,b,(c,d)=>utils.lex_compare(c,d,(e,f)=>
      e.a===f.a?ordCompare(e.x,f.x):Math.sign(e.a-f.a)));
  }
  const M={FS:targetFS,compare:targetCompare,
    debug:{ordAdd,ordRightDiff,ordFS,isLegalExpr:graphCheck,down:targetDown,
      parseExpr(text){assert(text==='()(1:ω)');return clone(M_TOP);}}};
  function expose(graph,parent,threshold,emit) {
    const q=threshold[0].coeff;assert(threshold.length===1&&!threshold[0].exp.length);
    let out=graph;
    for(let rounds=0;rounds<graph.length;rounds++) {
      budgetTick();const column=out.at(-1),i=column.findIndex(e=>e.x[0].coeff>=q);
      assert(i>=0,'目标缺少请求的行高');
      const next=out.slice(0,-1).concat([column.slice(0,i).concat([{a:column[i].a,x:nat(q)}])]);
      if(M.compare(next,out)!==0)emit({kind:'macro',before:out,after:next});
      out=next;const control=out.at(-1).at(-1);
      assert(control.a>=parent+1,'目标缺少请求的祖先');
      if(control.a===parent+1)return out;
      const down=targetDown(out);emit({kind:'down',before:out,after:down});out=down;
    }throw Error('控制父暴露未终止于有限父链');
  }
  function validateSource(source) {
    let cells=0;
    function walk(expr,depth) {
      budgetTick();if(expr.length>LIMITS.sourceWidth||depth>128)throw new BudgetStop('TBMS 宽度／嵌套上限');
      cells+=expr.length;
      for(const col of expr)for(const [v,h] of col) {
        budgetTick();natural(v);cells++;if(cells>LIMITS.sourceCells)throw new BudgetStop('TBMS 格数上限');
        walk(h,depth+1);
      }
    }walk(source,0);return source;
  }
  function loadTBM() {
    const context={};return {B,context,hashes:provenance,
      run:()=>validateSource(B.TBM.FS(context.expr,context.n))};
  }
  "use strict";
function makeCover(options = {}) {
    budgetTick();
    const loader = loadTBM(), B = loader.B;
    const tick = options.tick ?? (() => { budgetTick(); }), emit = options.emit ?? (() => { budgetTick(); });
    const maxWidth = options.maxWidth ?? 320;
    const stats = { sourceSteps: 0, limits: 0, units: 0, deletions: 0, pumps: 0,
        newNodes: 0, checks: 0, parentChecks: 0, labelChecks: 0, orderChecks: 0, maxWidth: 0,
        maxPumpsPerStep: 0, maxHeight: 0 };
    const key = a => JSON.stringify(a), add = M.debug.ordAdd;
    const one = [{ exp: [], coeff: 1 }];
    const power = exp => [{ exp, coeff: 1 }];
    function cmp(a, b) {
        budgetTick();
        for (let i = 0; i < Math.min(a.length, b.length); i++) {
            budgetTick();
            const c = cmp(a[i].exp, b[i].exp);
            if (c)
                return c;
            if (a[i].coeff !== b[i].coeff)
                return Math.sign(a[i].coeff - b[i].coeff);
        }
        return Math.sign(a.length - b.length);
    }
    const eq = (a, b) => cmp(a, b) === 0;
    function tower(h) { budgetTick(); let a = one; while (h--) {
        budgetTick();
        a = power(a);
    } return a; }
    function guard(width) {
        budgetTick();
        tick();
        if (width > maxWidth) {
            const e = Error('width budget: ' + width);
            e.name = 'BudgetStop';
            throw e;
        }
    }
    function rowOrdinal(h) {
        budgetTick();
        assert(h.length && !h[0].length);
        const depths = Array.from(h, col => {
            budgetTick();
            if (!col.length)
                return 0;
            assert(col.length === 1 && B.is_one(col[0][1]), 'one-row native label');
            assert(Number.isSafeInteger(col[0][0]) && col[0][0] > 0);
            return col[0][0];
        });
        let i = 0;
        function forest(depth) {
            budgetTick();
            const out = [];
            while (i < depths.length && depths[i] === depth) {
                budgetTick();
                i++;
                const exp = forest(depth + 1), last = out.at(-1);
                assert(!last || cmp(last.exp, exp) >= 0, 'canonical one-row forest');
                if (last && eq(last.exp, exp))
                    last.coeff++;
                else
                    out.push({ exp, coeff: 1 });
            }
            assert(i === depths.length || depths[i] < depth, 'no skipped tree depth');
            return out;
        }
        const value = forest(0);
        assert.equal(i, depths.length);
        assert(value.length === 1 && value[0].coeff === 1, 'primitive monomial label');
        return value;
    }
    function endpoints(source) {
        budgetTick();
        return Array.from(source, col => {
            budgetTick();
            let a = [];
            return Array.from(col, ([value, h]) => {
                budgetTick();
                assert(Number.isSafeInteger(value) && value > 0, 'safe positive source entry');
                a = add(a, rowOrdinal(h));
                return a;
            });
        });
    }
    function sourceFS(source, n) {
        budgetTick();
        tick();
        assert(Number.isSafeInteger(n) && n >= 0);
        guard(n + 3);
        loader.context.expr = source;
        loader.context.n = n;
        return loader.run('B.TBM.FS(expr,n)', 1000);
    }
    function fs(s, n) {
        budgetTick();
        const z = s.target.length, last = s.target.at(-1);
        guard(last?.length && n ? z - 1 + n * (z - last.at(-1).a) : Math.max(0, z - 1));
        const before = s.target;
        s.target = M.FS(before, n);
        emit({ kind: 'FS', before, after: s.target, n });
        stats.maxWidth = Math.max(stats.maxWidth, s.target.length);
    }
    function trim(s, width) {
        budgetTick();
        assert(s.target.length >= width);
        while (s.target.length > width) {
            budgetTick();
            fs(s, 0);
        }
    }
    const auxCount = s => s.target.length - (s.start + s.source.length - 1);
    const nodesOf = s => s.dicts.slice(1).flatMap(d => [...d.byEnd.values()]);
    function grade(s, d, a) {
        budgetTick();
        if (!a.length)
            return 0;
        if (!d) {
            assert(eq(a, one), 'level zero contains only zero and one');
            return 1;
        }
        const node = s.dicts[d].byEnd.get(key(a));
        assert(node && node.anchor !== null, 'unprepared ordinal endpoint at level ' + d);
        return node.anchor + 1;
    }
    const resource = (s, node) => grade(s, node.level - 1, node.exp) + 1;
    function capacityTable(graph) {
        budgetTick();
        const table = [];
        for (let j = 0; j < graph.length; j++) {
            budgetTick();
            tick();
            const row = new Float64Array(j);
            for (const e of graph[j]) {
                budgetTick();
                assert(e.x.length === 1 && !e.x[0].exp.length);
                const p = e.a - 1, r = e.x[0].coeff;
                assert(Number.isSafeInteger(r) && 0 < r && r <= e.a);
                row[p] = Math.max(row[p], r);
                for (let k = 0; k < p; k++) {
                    budgetTick();
                    row[k] = Math.max(row[k], Math.min(r, table[p][k]));
                }
            }
            table.push(row);
        }
        return (p, j) => 0 < p && p < j ? table[j - 1][p - 1] : 0;
    }
    function check(s, ready = true) {
        budgetTick();
        tick();
        stats.checks++;
        assert(M.debug.isLegalExpr(s.target));
        if (!s.source.length)
            return;
        const aux = auxCount(s);
        assert(0 <= aux && aux <= s.reserve);
        if (ready)
            assert.equal(aux, s.reserve);
        const Q = grade(s, s.height, tower(s.height)), nodes = nodesOf(s), cap = capacityTable(s.target);
        assert(s.start >= Q);
        for (const col of s.target) {
            budgetTick();
            for (const e of col) {
                budgetTick();
                assert(e.x[0].coeff <= Q, 'global row ceiling');
            }
        }
        for (let d = 1; d <= s.height; d++) {
            budgetTick();
            const sorted = [...s.dicts[d].byEnd.values()].sort((a, b) => cmp(a.end, b.end));
            let previous = d === 1 ? 0 : s.dicts[d - 1].root.anchor + 1;
            for (const node of sorted) {
                budgetTick();
                assert(previous < node.anchor, 'dictionary layering and strict endpoint order');
                assert(resource(s, node) <= node.anchor);
                previous = node.anchor + 1;
                let base = node.base;
                for (const child of node.children) {
                    budgetTick();
                    assert(eq(base, child.base) && cmp(child.end, node.end) < 0);
                    assert(cmp(child.exp, node.exp) < 0);
                    base = child.end;
                }
                assert(eq(add(node.base, power(node.exp)), node.end));
                // Every monomial-unit prefix is registered, including predecessor of
                // a successor endpoint. This is essential to one-pump-per-level.
                let prefix = [];
                for (const term of node.end) {
                    budgetTick();
                    for (let k = 0; k < term.coeff; k++) {
                        budgetTick();
                        assert(!prefix.length || s.dicts[d].byEnd.has(key(prefix)), 'prefix closure');
                        prefix = add(prefix, power(term.exp));
                    }
                }
            }
        }
        const ports = [...nodes.map(n => n.anchor),
            ...Array.from({ length: s.target.length - s.start + 1 }, (_, i) => s.start + i)];
        for (const node of nodes) {
            budgetTick();
            for (const p of ports) {
                budgetTick();
                if (node.anchor < p)
                    assert(cap(node.anchor, p) >= resource(s, node), `background d${node.level}, ${node.anchor}->${p}: ${cap(node.anchor, p)} < ${resource(s, node)}`);
            }
        }
        const E = endpoints(s.source), V = s.source.map(B.column_verticals), P = B.parents(s.source, V);
        const paired = [];
        for (let j = 0; j < E.length; j++) {
            budgetTick();
            for (let k = 0; k < E[j].length; k++) {
                budgetTick();
                paired.push({ a: E[j][k], v: V[j][k] });
            }
        }
        paired.sort((a, b) => cmp(a.a, b.a));
        for (let j = 1; j < paired.length; j++) {
            budgetTick();
            assert.equal(Math.sign(B.vertical_compare(paired[j - 1].v, paired[j].v)), cmp(paired[j - 1].a, paired[j].a), 'native cumulative endpoint order equals CNF order');
            stats.orderChecks++;
        }
        for (let j = 0; j < s.source.length; j++) {
            budgetTick();
            assert.equal(P[j].length, s.source[j].length);
            for (let k = 0; k < P[j].length; k++) {
                budgetTick();
                assert(cap(s.start + P[j][k][0], s.start + j) >= grade(s, s.height, E[j][k]), 'source parent cover');
            }
        }
    }
    function pump(s, cut, q, count) {
        budgetTick();
        assert(count > 0 && auxCount(s) > 0 && q <= cut);
        const z = s.target.length, span = z - cut, delta = count * span;
        guard(z - 1 + (count + 1) * span);
        s.target = expose(s.target, cut - 1, nat(q), emit);
        fs(s, count + 1);
        s.start += delta;
        for (const node of nodesOf(s)) {
            budgetTick();
            if (node.anchor >= cut)
                node.anchor += delta;
        }
        trim(s, z - 1 + delta);
        return { span, delta };
    }
    function ensure(s, d, a, allocations) {
        budgetTick();
        if (!a.length || !d || s.dicts[d].byEnd.has(key(a))) {
            grade(s, d, a);
            return;
        }
        let node = s.dicts[d].root;
        for (;;) {
            budgetTick();
            assert(cmp(node.base, a) < 0 && cmp(a, node.end) < 0);
            const child = node.children.find(c => cmp(a, c.end) <= 0);
            if (!child)
                break;
            node = child;
        }
        const base = node.children.at(-1)?.end ?? node.base;
        const difference = M.debug.ordRightDiff(base, a);
        assert.equal(difference.length, 1, 'one new exponent per dictionary level');
        const { exp, coeff: count } = difference[0];
        assert(cmp(exp, node.exp) < 0);
        ensure(s, d - 1, exp, allocations);
        assert(!allocations.some(x => x.level === d), 'at most one pump per level');
        const cut = node.anchor, q = resource(s, node), newResource = grade(s, d - 1, exp) + 1;
        assert(newResource <= q - 1);
        const { span, delta } = pump(s, cut, q, count);
        let nextBase = base;
        for (let k = 0; k < count; k++) {
            budgetTick();
            const end = add(nextBase, power(exp));
            const child = { level: d, base: nextBase, end, exp, anchor: cut + k * span, children: [] };
            assert(!s.dicts[d].byEnd.has(key(end)));
            node.children.push(child);
            s.dicts[d].byEnd.set(key(end), child);
            nextBase = end;
            stats.newNodes++;
        }
        assert(eq(nextBase, a));
        allocations.push({ level: d, cut, row: q, count, span, delta, newResource });
        stats.pumps++;
        check(s, false);
    }
    function checkSourceUnit(before, after, n) {
        budgetTick();
        const E = endpoints(before), En = endpoints(after), P = B.parents(before, before.map(B.column_verticals)), Pn = B.parents(after, after.map(B.column_verticals));
        const x = before.length - 1, alpha = E[x].at(-1), cut = P[x].at(-1)[0], L = x - cut;
        const oldEnds = new Set(E.flat().map(key)), cells = new Map();
        for (const col of E.concat(En)) {
            budgetTick();
            for (const a of col) {
                budgetTick();
                cells.set(key(a), a);
            }
        }
        for (const col of En) {
            budgetTick();
            for (const a of col) {
                budgetTick();
                assert(oldEnds.has(key(a)));
            }
        }
        function query(ends, parents, col, a) {
            budgetTick();
            const i = ends[col].findIndex(b => cmp(b, a) >= 0);
            return i < 0 ? null : parents[col][i][0];
        }
        for (let b = 1; b <= n; b++) {
            budgetTick();
            for (let j = cut; j < x; j++) {
                budgetTick();
                for (const a of cells.values()) {
                    budgetTick();
                    const out = x + (b - 1) * L + j - cut, from = j === cut && cmp(a, alpha) < 0 ? x : j, shift = j === cut && cmp(a, alpha) < 0 ? b - 1 : b, p = query(E, P, from, a), want = p === null ? null : p < cut ? p : p + shift * L;
                    assert.equal(query(En, Pn, out, a), want, 'native parent-copy law');
                    stats.parentChecks++;
                }
            }
        }
    }
    function initialize(height) {
        budgetTick();
        assert(Number.isSafeInteger(height) && height >= 0 && height <= LIMITS.height);
        guard(3 * height + 6);
        let epsilonSource = B.infinity_FS(3);
        epsilonSource = sourceFS(epsilonSource, 1);
        assert.equal(B.display(epsilonSource), '()(1^()(1,1))');
        const source = sourceFS(epsilonSource, height);
        assert(eq(rowOrdinal(source[1][0][1]), tower(height)));
        const top = M.debug.parseExpr('()(1:ω)'), seedIndex = 2 * height + 2;
        const s = { source, height, seedIndex, seed: null, target: top, start: 2 * height + 1,
            reserve: Math.max(1, height), dicts: [null], path: [], allocationLog: [] };
        for (let d = 1; d <= height; d++) {
            budgetTick();
            const node = { level: d, base: [], end: tower(d), exp: tower(d - 1), anchor: 2 * d, children: [] };
            s.dicts.push({ root: node, byEnd: new Map([[key(node.end), node]]) });
        }
        fs(s, seedIndex);
        s.seed = s.target;
        fs(s, s.reserve);
        assert(M.compare(s.target, s.seed) < 0, 'proper descendant of the uniform height seed');
        check(s);
        stats.maxHeight = Math.max(stats.maxHeight, height);
        return s;
    }
    function initializeForSource(source, height) {
        budgetTick();
        // Local invariant audit only: build an actual STANDARD diagonal cover of
        // this finite source and all its current endpoints. This does not replace
        // initialize(height) in the uniform all-descendant theorem.
        assert(source.length && Number.isSafeInteger(height) && height >= 0 && height <= LIMITS.height);
        const values = Array.from({ length: height + 1 }, () => new Map());
        function collect(d, a) {
            budgetTick();
            if (!a.length)
                return;
            if (!d) {
                assert(eq(a, one));
                return;
            }
            if (values[d].has(key(a)))
                return;
            assert(cmp(a, tower(d)) <= 0);
            values[d].set(key(a), a);
            let prefix = [];
            for (const term of a) {
                budgetTick();
                collect(d - 1, term.exp);
                guard(term.coeff);
                for (let k = 0; k < term.coeff; k++) {
                    budgetTick();
                    prefix = add(prefix, power(term.exp));
                    if (!eq(prefix, a))
                        collect(d, prefix);
                }
            }
        }
        for (let d = 1; d <= height; d++) {
            budgetTick();
            collect(d, tower(d));
        }
        for (const col of endpoints(source)) {
            budgetTick();
            for (const a of col) {
                budgetTick();
                collect(height, a);
            }
        }
        let address = 0;
        const dicts = [null];
        for (let d = 1; d <= height; d++) {
            budgetTick();
            const sorted = [...values[d].values()].sort(cmp), children = [], byEnd = new Map();
            let base = [];
            for (const a of sorted.slice(0, -1)) {
                budgetTick();
                const diff = M.debug.ordRightDiff(base, a);
                assert(diff.length === 1 && diff[0].coeff === 1, 'adjacent prefix-closed endpoints');
                address += 2;
                const node = { level: d, base, end: a, exp: diff[0].exp, anchor: address, children: [] };
                children.push(node);
                byEnd.set(key(a), node);
                base = a;
            }
            address += 2;
            const root = { level: d, base: [], end: tower(d), exp: tower(d - 1), anchor: address, children };
            byEnd.set(key(root.end), root);
            dicts.push({ root, byEnd });
        }
        const start = address + 1, seedIndex = start + 1;
        const s = { source, height, start, seedIndex, seed: null, target: M.debug.parseExpr('()(1:ω)'),
            reserve: Math.max(1, height), dicts, path: [], allocationLog: [], localAuditInitialization: true };
        fs(s, seedIndex);
        s.seed = s.target;
        fs(s, source.length + s.reserve - 2);
        assert(M.compare(s.target, s.seed) < 0, 'proper standard local-audit initialization');
        check(s);
        stats.maxHeight = Math.max(stats.maxHeight, height);
        return s;
    }
    function step(s, n) {
        budgetTick();
        check(s);
        if (!s.source.length)
            return s;
        const before = s.target, old = s.source, x = old.length - 1, col = old.at(-1);
        const kind = !col.length ? 'delete' : B.is_one(col.at(-1)[1]) ? 'unit' : 'limit';
        const P = B.parents(old, old.map(B.column_verticals)), E = endpoints(old);
        if (kind === 'unit')
            guard(x + n * (x - P[x].at(-1)[0]));
        const next = sourceFS(old, n), allocations = [];
        if (kind === 'unit' && n)
            checkSourceUnit(old, next, n);
        if (kind === 'delete' || kind === 'unit' && !n) {
            s.source = next;
            trim(s, next.length ? s.start + next.length - 1 + s.reserve : 1);
            stats.deletions++;
        }
        else {
            const alpha = E[x].at(-1), parent = P[x].at(-1)[0];
            if (kind === 'limit') {
                const En = endpoints(next), alphaNew = En[x].at(-1), oldHeight = rowOrdinal(col.at(-1)[1]);
                const prefix = col.length > 1 ? E[x][col.length - 2] : [];
                const expected = add(prefix, M.debug.ordFS(oldHeight, n + 1));
                assert(eq(alphaNew, expected), 'native one-row refinement matches epsilon-zero CNF');
                stats.labelChecks++;
                ensure(s, s.height, alphaNew, allocations);
                const Pn = B.parents(next, next.map(B.column_verticals));
                for (const p of Pn[x].slice(col.length - 1)) {
                    budgetTick();
                    assert.equal(p[0], parent);
                }
                for (const a of En[x]) {
                    budgetTick();
                    grade(s, s.height, a);
                }
                assert(grade(s, s.height, alphaNew) < grade(s, s.height, alpha));
            }
            const predecessor = M.debug.ordFS(alpha, 0);
            const q = kind === 'unit' ? grade(s, s.height, predecessor) + 1 : grade(s, s.height, alpha);
            assert(q <= grade(s, s.height, alpha));
            trim(s, s.start + x);
            s.target = expose(s.target, s.start + parent - 1, nat(q), emit);
            const z = s.target.length, L = z - (s.start + parent);
            if (kind === 'limit') {
                fs(s, Math.ceil((s.reserve + 1) / L));
                trim(s, z + s.reserve);
                stats.limits++;
            }
            else {
                fs(s, n + Math.ceil(s.reserve / L));
                trim(s, s.start + next.length - 1 + s.reserve);
                stats.units++;
            }
            s.source = next;
        }
        assert(allocations.length <= s.height);
        assert(M.compare(s.target, before) < 0, 'strict real target descent');
        s.path.push(n);
        s.allocationLog.push(allocations);
        stats.sourceSteps++;
        stats.maxPumpsPerStep = Math.max(stats.maxPumpsPerStep, allocations.length);
        check(s);
        return s;
    }
    return { B, M, stats, initialize, initializeForSource, step, check, grade, resource, endpoints, nodesOf, rowOrdinal,
        sourceFS, cmp, eq, tower, auxCount, capacityTable, hashes: loader.hashes };
}


  const Symmetric = (function (makeCNF) {
    "use strict";
function symmetricSeed(n) {
    budgetTick();
    assert(Number.isSafeInteger(n) && n >= 1);
    const column = j => [{ a: j, x: nat(j) }];
    return [[], ...Array.from({ length: n + 1 }, (_, i) => column(i + 1)),
        ...Array.from({ length: n }, (_, i) => column(n - i))];
}
function makeCover(options = {}) {
    budgetTick();
    const tick = options.tick ?? (() => { budgetTick(); }), emit = options.emit ?? (() => { budgetTick(); });
    const maxWidth = options.maxWidth ?? 700;
    const cnf = makeCNF({ tick, maxWidth });
    const { B, endpoints, sourceFS, cmp, eq, rowOrdinal, capacityTable } = cnf;
    const add = M.debug.ordAdd, key = a => JSON.stringify(a);
    const power = exp => [{ exp, coeff: 1 }];
    const stats = { sourceSteps: 0, limits: 0, units: 0, deletions: 0, pumps: 0,
        lowPumps: 0, skippedWeakAux: 0, checks: 0, parentChecks: 0,
        orderChecks: 0, labelChecks: 0, maxWidth: 0, maxNodes: 0,
        maxPumpsPerStep: 0, maxDepth: 0 };
    function guard(width) {
        budgetTick();
        tick();
        assert(Number.isSafeInteger(width) && width >= 0);
        if (width > maxWidth) {
            const e = Error('width budget: ' + width);
            e.name = 'BudgetStop';
            throw e;
        }
    }
    function fs(s, n) {
        budgetTick();
        const z = s.target.length, last = s.target.at(-1);
        guard(last?.length && n ? z - 1 + n * (z - last.at(-1).a) : Math.max(0, z - 1));
        const before = s.target;
        s.target = M.FS(before, n);
        emit({ kind: 'FS', before, after: s.target, n });
        stats.maxWidth = Math.max(stats.maxWidth, s.target.length);
    }
    function trim(s, width) { budgetTick(); assert(s.target.length >= width); while (s.target.length > width) {
        budgetTick();
        fs(s, 0);
    } }
    function lowNodes(s) {
        budgetTick();
        const result = [];
        function visit(node) { budgetTick(); result.push(node); for (const child of node.children) {
            budgetTick();
            visit(child);
        } }
        visit(s.low);
        return result;
    }
    const nodesOf = s => [...lowNodes(s), ...s.dicts.slice(2).flatMap(d => [...d.byEnd.values()])];
    const auxCount = s => s.target.length - (s.start + s.source.length - 1);
    function pcmp(a, b) {
        budgetTick();
        for (let i = a.length - 1; i >= 0; i--) {
            budgetTick();
            if (a[i] !== b[i])
                return Math.sign(a[i] - b[i]);
        }
        return 0;
    }
    function pend(node) { budgetTick(); const a = node.base.slice(); a[node.rank]++; return a; }
    function asPolynomial(a, d) {
        budgetTick();
        const out = Array(d + 1).fill(0);
        for (const term of a) {
            budgetTick();
            const e = term.exp;
            assert(!e.length || e.length === 1 && !e[0].exp.length, 'finite polynomial exponent');
            const j = e.length ? e[0].coeff : 0;
            assert(Number.isSafeInteger(j) && 0 <= j && j <= d);
            out[j] = term.coeff;
        }
        return out;
    }
    function lowGradeVector(s, a) {
        budgetTick();
        if (a.every(v => !v))
            return s.degree;
        function at(node) {
            budgetTick();
            const end = pend(node);
            assert(pcmp(node.base, a) < 0 && pcmp(a, end) <= 0, 'polynomial interval');
            if (!pcmp(a, end))
                return node.anchor + 1;
            if (node.rank === 1) {
                const q = lowGradeVector(s, node.base) + a[0];
                assert(q < node.anchor, 'unprepared finite interval');
                return q;
            }
            const tail = a.slice(0, node.rank - 1).some(Boolean);
            const index = a[node.rank - 1] - (tail ? 0 : 1);
            assert(0 <= index && index < node.children.length, 'unprepared polynomial child');
            return at(node.children[index]);
        }
        return at(s.low);
    }
    function grade(s, level, a) {
        budgetTick();
        // Positive zero offsets remove the redundant resource +1 at EVERY layer.
        // The offset is not a source row: all positive source endpoints lie above it.
        if (!a.length)
            return s.degree;
        if (level === 1)
            return lowGradeVector(s, asPolynomial(a, s.degree));
        const node = s.dicts[level].byEnd.get(key(a));
        assert(node, 'unprepared CNF endpoint at layer ' + level);
        return node.anchor + 1;
    }
    const resource = (s, node) => node.level === 1 ? node.rank : grade(s, node.level - 1, node.exp);
    function check(s, ready = true) {
        budgetTick();
        tick();
        stats.checks++;
        assert(M.debug.isLegalExpr(s.target));
        if (!s.source.length)
            return;
        const aux = auxCount(s), nodes = nodesOf(s), Q = grade(s, s.reserve, s.top);
        assert(aux >= 0 && aux <= s.reserve && aux === s.auxStrengths.length);
        if (ready)
            assert.equal(aux, s.reserve);
        assert(s.auxStrengths.every((v, i, a) => v >= 1 && v <= s.reserve && (!i || a[i - 1] >= v)));
        assert(s.start >= Q);
        for (const col of s.target) {
            budgetTick();
            for (const e of col) {
                budgetTick();
                assert(e.x.length === 1 && !e.x[0].exp.length && e.x[0].coeff <= e.a && e.x[0].coeff <= Q);
            }
        }
        for (const node of lowNodes(s)) {
            budgetTick();
            assert(node.anchor > s.degree && node.anchor <= s.low.anchor);
            let prev = lowGradeVector(s, node.base);
            for (const child of node.children) {
                budgetTick();
                assert(prev < child.anchor && child.anchor + 1 < node.anchor);
                assert.equal(child.rank, node.rank - 1);
                prev = child.anchor + 1;
            }
        }
        for (let level = 2; level <= s.reserve; level++) {
            budgetTick();
            const dict = s.dicts[level];
            const sorted = [...dict.byEnd.values()].sort((a, b) => cmp(a.end, b.end));
            let previous = s.dicts[level - 1].root.anchor; // Adjacent roots allowed.
            for (const node of sorted) {
                budgetTick();
                assert(previous < node.anchor, 'layering / within-layer gap');
                previous = node.anchor + 1;
                assert(s.degree <= resource(s, node) && resource(s, node) <= node.anchor);
                assert(eq(add(node.base, power(node.exp)), node.end));
                let base = node.base;
                for (const child of node.children) {
                    budgetTick();
                    assert(eq(base, child.base) && cmp(child.end, node.end) < 0 && cmp(child.exp, node.exp) < 0);
                    base = child.end;
                }
                let prefix = [];
                for (const term of node.end) {
                    budgetTick();
                    for (let k = 0; k < term.coeff; k++) {
                        budgetTick();
                        assert(!prefix.length || dict.byEnd.has(key(prefix)), 'monomial-prefix closure');
                        prefix = add(prefix, power(term.exp));
                    }
                }
            }
        }
        const lastMain = s.start + s.source.length - 1;
        const ports = [...nodes.map(node => node.anchor),
            ...Array.from({ length: s.target.length - s.start + 1 }, (_, i) => s.start + i)];
        const cap = capacityTable(s.target);
        for (const node of nodes) {
            budgetTick();
            for (const p of ports) {
                budgetTick();
                if (node.anchor < p) {
                    if (p > lastMain && s.auxStrengths[p - lastMain - 1] < node.level)
                        continue;
                    assert(cap(node.anchor, p) >= resource(s, node), `layer ${node.level} background ${node.anchor}->${p}: ${cap(node.anchor, p)} < ${resource(s, node)}`);
                }
            }
        }
        const E = endpoints(s.source), V = s.source.map(B.column_verticals), P = B.parents(s.source, V);
        const ordered = [];
        for (let j = 0; j < E.length; j++) {
            budgetTick();
            for (let k = 0; k < E[j].length; k++) {
                budgetTick();
                assert(cmp(E[j][k], s.top) <= 0);
                assert(cap(s.start + P[j][k][0], s.start + j) >= grade(s, s.reserve, E[j][k]), 'source cover');
                ordered.push({ a: E[j][k], v: V[j][k] });
            }
        }
        ordered.sort((a, b) => cmp(a.a, b.a));
        for (let i = 1; i < ordered.length; i++) {
            budgetTick();
            assert.equal(Math.sign(B.vertical_compare(ordered[i - 1].v, ordered[i].v)), cmp(ordered[i - 1].a, ordered[i].a));
            stats.orderChecks++;
        }
        stats.maxNodes = Math.max(stats.maxNodes, nodes.length);
    }
    function pump(s, level, cut, q, count) {
        budgetTick();
        assert(count > 0 && q > 0 && q <= cut);
        // An unused weaker slot may be discarded; it is not upgraded for free.
        while (s.auxStrengths.length && s.auxStrengths.at(-1) < level) {
            budgetTick();
            fs(s, 0);
            s.auxStrengths.pop();
            stats.skippedWeakAux++;
        }
        assert(s.auxStrengths.length && s.auxStrengths.at(-1) >= level);
        const z = s.target.length, span = z - cut, delta = count * span;
        guard(z - 1 + (count + 1) * span);
        s.target = expose(s.target, cut - 1, nat(q), emit);
        fs(s, count + 1);
        s.start += delta;
        for (const node of nodesOf(s)) {
            budgetTick();
            if (node.anchor >= cut)
                node.anchor += delta;
        }
        trim(s, z - 1 + delta);
        s.auxStrengths.pop();
        return { span, delta };
    }
    function ensureLow(s, alpha, allocations) {
        budgetTick();
        if (!alpha.length)
            return;
        const a = asPolynomial(alpha, s.degree);
        let node = s.low;
        for (;;) {
            budgetTick();
            const end = pend(node);
            assert(pcmp(node.base, a) < 0 && pcmp(a, end) <= 0);
            if (!pcmp(a, end)) {
                lowGradeVector(s, a);
                return;
            }
            if (node.rank === 1)
                break;
            const tail = a.slice(0, node.rank - 1).some(Boolean);
            const index = a[node.rank - 1] - (tail ? 0 : 1);
            assert(index >= 0);
            if (index >= node.children.length) {
                assert(!tail, 'a single source refinement only appends polynomial child endpoints');
                break;
            }
            node = node.children[index];
        }
        const cut = node.anchor, span = s.target.length - cut;
        const count = node.rank === 1
            ? Math.max(0, Math.ceil((lowGradeVector(s, node.base) + a[0] + 1 - cut) / span))
            : a[node.rank - 1] - node.children.length;
        if (count) {
            const oldCount = node.children.length, rank = node.rank;
            const moved = pump(s, 1, cut, rank, count);
            if (rank > 1)
                for (let i = 0; i < count; i++) {
                    budgetTick();
                    const base = node.base.slice();
                    base[rank - 1] = oldCount + i;
                    node.children.push({ level: 1, rank: rank - 1, base, anchor: cut + i * moved.span, children: [] });
                }
            allocations.push({ level: 1, cut, row: rank, count, ...moved });
            stats.pumps++;
            stats.lowPumps++;
            check(s, false);
        }
        lowGradeVector(s, a);
    }
    function ensure(s, level, alpha, allocations) {
        budgetTick();
        if (level === 1) {
            ensureLow(s, alpha, allocations);
            return;
        }
        if (!alpha.length || s.dicts[level].byEnd.has(key(alpha))) {
            grade(s, level, alpha);
            return;
        }
        let node = s.dicts[level].root;
        for (;;) {
            budgetTick();
            assert(cmp(node.base, alpha) < 0 && cmp(alpha, node.end) < 0);
            const child = node.children.find(c => cmp(alpha, c.end) <= 0);
            if (!child)
                break;
            node = child;
        }
        const base = node.children.at(-1)?.end ?? node.base;
        const diff = M.debug.ordRightDiff(base, alpha);
        assert.equal(diff.length, 1, 'one new exponent per CNF layer');
        const { exp, coeff: count } = diff[0];
        assert(cmp(exp, node.exp) < 0);
        ensure(s, level - 1, exp, allocations);
        assert(!allocations.some(a => a.level >= level), 'strictly increasing allocation layers');
        const cut = node.anchor, q = resource(s, node), newResource = grade(s, level - 1, exp);
        assert(newResource <= q - 1);
        const moved = pump(s, level, cut, q, count);
        let nextBase = base;
        for (let i = 0; i < count; i++) {
            budgetTick();
            const end = add(nextBase, power(exp));
            const child = { level, base: nextBase, end, exp, anchor: cut + i * moved.span, children: [] };
            assert(!s.dicts[level].byEnd.has(key(end)));
            s.dicts[level].byEnd.set(key(end), child);
            node.children.push(child);
            nextBase = end;
        }
        assert(eq(nextBase, alpha));
        allocations.push({ level, cut, row: q, count, newResource, ...moved });
        stats.pumps++;
        check(s, false);
    }
    function checkSourceUnit(before, after, n) {
        budgetTick();
        const E = endpoints(before), En = endpoints(after), P = B.parents(before, before.map(B.column_verticals)), Pn = B.parents(after, after.map(B.column_verticals));
        const x = before.length - 1, alpha = E[x].at(-1), cut = P[x].at(-1)[0], L = x - cut;
        const oldEnds = new Set(E.flat().map(key)), cells = new Map();
        for (const col of E.concat(En)) {
            budgetTick();
            for (const a of col) {
                budgetTick();
                cells.set(key(a), a);
            }
        }
        for (const col of En) {
            budgetTick();
            for (const a of col) {
                budgetTick();
                assert(oldEnds.has(key(a)));
            }
        }
        const query = (es, ps, j, a) => { budgetTick(); const i = es[j].findIndex(b => cmp(b, a) >= 0); return i < 0 ? null : ps[j][i][0]; };
        for (let b = 1; b <= n; b++) {
            budgetTick();
            for (let j = cut; j < x; j++) {
                budgetTick();
                for (const a of cells.values()) {
                    budgetTick();
                    const out = x + (b - 1) * L + j - cut, low = j === cut && cmp(a, alpha) < 0;
                    const p = query(E, P, low ? x : j, a), shift = low ? b - 1 : b;
                    assert.equal(query(En, Pn, out, a), p === null ? null : p < cut ? p : p + shift * L);
                    stats.parentChecks++;
                }
            }
        }
    }
    function initialize(depth, degree) {
        budgetTick();
        assert(Number.isSafeInteger(depth) && depth >= 2);
        assert(Number.isSafeInteger(degree) && degree >= 1);
        guard(Math.max(depth + 3, degree + 3));
        const reserve = depth - 1;
        const epsilon = sourceFS(B.infinity_FS(3), 1), S = sourceFS(epsilon, depth);
        const source = sourceFS(S, degree - 1);
        const k = Math.ceil((degree - 1) / (2 * depth + 1)), delta = (2 * depth + 1) * k;
        const low = { level: 1, rank: degree, base: Array(degree + 1).fill(0), anchor: 2 + delta, children: [] };
        const dicts = [null, { root: low }];
        let top = power(nat(degree));
        for (let level = 2; level <= reserve; level++) {
            budgetTick();
            const exp = top;
            top = power(top);
            const root = { level, base: [], end: top, exp, anchor: level + 1 + delta, children: [] };
            dicts.push({ root, byEnd: new Map([[key(top), root]]) });
        }
        assert(eq(rowOrdinal(source[1][0][1]), top), 'native first branch has the predicted tower');
        const seed = symmetricSeed(depth);
        const s = { depth, degree, reserve, source, top, seed, target: seed,
            start: depth + 1 + delta, low, dicts,
            auxStrengths: Array.from({ length: reserve }, (_, i) => reserve - i), path: [], allocationLog: [] };
        fs(s, k);
        check(s);
        stats.maxDepth = Math.max(stats.maxDepth, depth);
        return s;
    }
    function step(s, n) {
        budgetTick();
        check(s);
        if (!s.source.length)
            return s;
        const before = s.target, old = s.source, x = old.length - 1, col = old.at(-1);
        const kind = !col.length ? 'delete' : B.is_one(col.at(-1)[1]) ? 'unit' : 'limit';
        const E = endpoints(old), P = B.parents(old, old.map(B.column_verticals));
        if (kind === 'unit')
            guard(x + n * (x - P[x].at(-1)[0]));
        const next = sourceFS(old, n), allocations = [];
        if (kind === 'unit' && n)
            checkSourceUnit(old, next, n);
        if (kind === 'delete' || kind === 'unit' && !n) {
            assert(s.auxStrengths.every(v => v === s.reserve), 'only initial limit state has graded auxiliaries');
            s.source = next;
            trim(s, next.length ? s.start + next.length - 1 + s.reserve : 1);
            stats.deletions++;
        }
        else {
            const alpha = E[x].at(-1), parent = P[x].at(-1)[0];
            if (kind === 'limit') {
                const En = endpoints(next), alphaNew = En[x].at(-1), height = rowOrdinal(col.at(-1)[1]);
                const prefix = col.length > 1 ? E[x][col.length - 2] : [];
                assert(eq(alphaNew, add(prefix, M.debug.ordFS(height, n + 1))), 'native row refinement law');
                stats.labelChecks++;
                ensure(s, s.reserve, alphaNew, allocations);
                for (const a of En[x]) {
                    budgetTick();
                    grade(s, s.reserve, a);
                }
                const Pn = B.parents(next, next.map(B.column_verticals));
                for (const p of Pn[x].slice(col.length - 1)) {
                    budgetTick();
                    assert.equal(p[0], parent);
                }
                assert(grade(s, s.reserve, alphaNew) < grade(s, s.reserve, alpha));
            }
            const pred = M.debug.ordFS(alpha, 0);
            const q = kind === 'unit' ? grade(s, s.reserve, pred) + 1 : grade(s, s.reserve, alpha);
            assert(q <= grade(s, s.reserve, alpha));
            trim(s, s.start + x);
            s.auxStrengths = [];
            s.target = expose(s.target, s.start + parent - 1, nat(q), emit);
            const z = s.target.length, L = z - (s.start + parent);
            if (kind === 'limit') {
                fs(s, Math.ceil((s.reserve + 1) / L));
                trim(s, z + s.reserve);
                stats.limits++;
            }
            else {
                fs(s, n + Math.ceil(s.reserve / L));
                trim(s, s.start + next.length - 1 + s.reserve);
                stats.units++;
            }
            s.source = next;
            s.auxStrengths = Array(s.reserve).fill(s.reserve);
        }
        assert(allocations.length <= s.reserve);
        assert(M.compare(s.target, before) < 0, 'strict actual M descent');
        s.path.push(n);
        s.allocationLog.push(allocations);
        stats.sourceSteps++;
        stats.maxPumpsPerStep = Math.max(stats.maxPumpsPerStep, allocations.length);
        check(s);
        return s;
    }
    return { B, M, initialize, step, check, stats, grade, resource, lowNodes, nodesOf,
        endpoints, sourceFS, rowOrdinal, cmp, eq, auxCount, hashes: cnf.hashes };
}

    return {makeCover,symmetricSeed};
  })(makeCover);

  // Reach W_depth by actual SRPD operations, not by a display-only substitution.
  // D_(depth+2), local exposure, ordinary [1], and trailing [0] operations are
  // the uniform standardness path from SYMMETRIC-TOWER-BOUND, section 2.1.
  function reachSymmetric(depth,emit=()=>{}) {
    natural(depth);if(depth>LIMITS.height)throw new BudgetStop('对称塔高度上限');
    let target=clone(M_TOP);
    const fs=n=>{budgetTick();const before=target;target=M.FS(target,n);emit({kind:'FS',before,after:target,n});};
    fs(depth===0?1:depth+2);
    if(depth===0)return target;
    for(let r=depth;r>=1;r--) {
      budgetTick();const z=target.length;
      target=expose(target,r,nat(1),emit);fs(1);
      const width=r===1?z:z+1;while(target.length>width)fs(0);
    }
    assert(M.compare(target,Symmetric.symmetricSeed(depth))===0,'对称式标准路径错误');
    return target;
  }
  function makeSymmetricSimulation(options={}) {
    const emit=options.emit??(()=>{}),maxWidth=options.maxWidth??LIMITS.width;
    const cnf=makeCover({tick:budgetTick,maxWidth}),general=Symmetric.makeCover({tick:budgetTick,maxWidth,emit});
    function fs(state,n) {
      const before=state.target,z=before.length,last=before.at(-1);
      const width=last?.length&&n?z-1+n*(z-last.at(-1).a):Math.max(0,z-1);
      if(width>maxWidth)throw new BudgetStop('width budget: '+width);
      state.target=M.FS(before,n);emit({kind:'FS',before,after:state.target,n});
    }
    function finiteCheck(state) {
      graphCheck(state.target);if(!state.source.length)return;
      assert(state.target.length===state.start+state.source.length-1,'有限行主点对齐');
      for(const col of state.target)for(const e of col)assert(e.x[0].coeff<=state.ceiling);
      const parents=B.parents(state.source,state.source.map(B.column_verticals));
      const cap=cnf.capacityTable(state.target);
      for(let j=0;j<state.source.length;j++)for(let r=0;r<state.source[j].length;r++) {
        budgetTick();assert(B.is_one(state.source[j][r][1]));
        assert(cap(state.start+parents[j][r][0],state.start+j)>=r+1,'有限行祖先覆盖');
      }
    }
    function initialize(depth) {
      const source=cnf.sourceFS(EPSILON,depth),target=reachSymmetric(depth,emit);
      return {mode:depth===0?'exact-zero-layer':'symmetric-tower',depth,source,target,path:[],allocationLog:[]};
    }
    function initializeFiniteRows(source,rowCount) {
      natural(rowCount);assert(rowCount>0);
      const k=Math.max(0,Math.ceil((rowCount-2)/3)),ceiling=3*k+2;
      const state={mode:'finite-row-cover',depth:1,source,target:reachSymmetric(1,emit),
        start:ceiling,ceiling,path:[],allocationLog:[]};
      fs(state,k);finiteCheck(state);return state;
    }
    function step(state,n) {
      budgetTick();if(!state.source.length)return state;
      const before=state.target,source=state.source;
      if(state.mode==='symmetric-tower') {
        if(state.depth>=2) {
          // The first index fixes the polynomial degree once, not future indices.
          const next=general.initialize(state.depth,n+1);
          assert(M.compare(next.seed,before)===0,'不得重新选择更大的对称种子');
          next.mode='symmetric-cover';
          assert(B.compare(next.source,cnf.sourceFS(source,n))===0);
          assert(M.compare(next.target,before)<0);return next;
        }
        // B_(n+1) <= W_1[k], with 3k+2 >= n+1. Do not replay the root
        // standardness path here: this is one descent from the retained W_1.
        const k=Math.max(0,Math.ceil((n-1)/3)),ceiling=3*k+2;
        const next={mode:'finite-row-cover',depth:1,source:cnf.sourceFS(source,n),target:before,
          start:ceiling,ceiling,path:[],allocationLog:[]};
        fs(next,k);finiteCheck(next);return next;
      }
      if(state.mode==='symmetric-cover'){general.step(state,n);return state;}
      const nextSource=cnf.sourceFS(source,n);
      if(state.mode==='exact-zero-layer') {
        fs(state,n);state.source=nextSource;
        // S_0 and W_0 have the same finite-empty-column descendants.
        assert(state.source.every(c=>!c.length)&&state.target.every(c=>!c.length));
        assert(state.source.length===state.target.length);return state;
      }
      assert(state.mode==='finite-row-cover');finiteCheck(state);
      const column=source.at(-1);
      if(!column.length||!n)fs(state,0);
      else {
        const parents=B.parents(source,source.map(B.column_verticals));
        const cut=state.start+parents.at(-1).at(-1)[0];
        assert(cut>=state.ceiling,'所有有限行操作必须不插行');
        state.target=expose(state.target,cut-1,nat(column.length),emit);fs(state,n);
      }
      state.source=nextSource;assert(M.compare(state.target,before)<0);finiteCheck(state);return state;
    }
    return {initialize,initializeFiniteRows,step,check:finiteCheck};
  }

  // Expressions store ONLY the source route. This is JSON-safe for NER and
  // reconstructs the same history after import; no arbitrary source reseeding.
  const version='tbms-srpd-descent-v1';
  function parse(raw) {
    let route;
    if(raw&&raw.version===version&&Array.isArray(raw.route))route=raw.route.slice();
    else if(typeof raw==='string') {
      const text=raw.trim(),m=/(?:^|@\s*)(?:E|Limit|TBMS)((?:\[\d+\])*)\s*$/i.exec(text);
      if(m)route=Array.from(m[1].matchAll(/\[(\d+)\]/g),x=>Number(x[1]));
      else if(['()(1^e0)','()(1^ε₀)','()(1^()(1,1))'].includes(text))route=[];
      else throw Error('请输入 E、E[2][1] 等展开路径；单独的 TBMS 式子不能确定模拟历史。');
    }else throw Error('无效的 TBMS—SRPD 路径状态');
    if(route.length>LIMITS.route)throw new BudgetStop('路径长度上限');
    for(const n of route){natural(n);if(n>LIMITS.index)throw new BudgetStop('基本列指标上限');}
    return {version,route};
  }
  const routeKey=route=>route.join('/');
  const routeText=route=>'E'+route.map(n=>'['+n+']').join('');
  class Cache {
    constructor(entries,weightLimit){this.entries=entries;this.weightLimit=weightLimit;this.weight=0;this.data=new Map();}
    get(key){const v=this.data.get(key);if(!v)return undefined;this.data.delete(key);this.data.set(key,v);return v.value;}
    set(key,value,weight=1){this.delete(key);if(weight>this.weightLimit)return;
      this.data.set(key,{value,weight});this.weight+=weight;
      while(this.data.size>this.entries||this.weight>this.weightLimit)this.delete(this.data.keys().next().value);
    }
    delete(key){const old=this.data.get(key);if(old){this.weight-=old.weight;this.data.delete(key);}}
    clear(){this.data.clear();this.weight=0;}
  }
  const sourceCache=new Cache(128,500000),stateCache=new Cache(LIMITS.stateEntries,LIMITS.stateChars),
    resultCache=new Cache(96,2000000),reseedCache=new Cache(96,2000000);
  function getSource(route) {
    let source=EPSILON,start=0;
    for(let j=route.length;j>0;j--){const found=sourceCache.get(routeKey(route.slice(0,j)));if(found){source=found;start=j;break;}}
    for(let j=start;j<route.length;j++) {
      budgetTick();source=validateSource(B.TBM.FS(source,route[j]));
      sourceCache.set(routeKey(route.slice(0,j+1)),source,JSON.stringify(source).length);
    }return source;
  }
  function source(raw){return bounded(()=>clone(getSource(parse(raw).route)));}
  function simulated(raw,options={}) {
    const expr=parse(raw),route=expr.route,key=routeKey(route);
    if(!options.fresh){const cached=resultCache.get(key);if(cached)return cached;}
    let completed=0;
    const events=[],emit=e=>{
      budgetTick();assert(M.compare(e.after,e.before)<0,'模拟事件必须严格下降');
      events.push(e.kind==='FS'?{kind:'FS',n:isMTop(e.before)?e.n+1:e.n}:{kind:e.kind});
      if(events.length>12000)throw new BudgetStop('局部事件数上限');
      if(options.emit)options.emit(e);
    };
    try {
      const result=bounded(()=>{
        const src=getSource(route);
        if(!route.length)return {status:'ok',source:src,target:[[0]],events:[],route};
        if(route[0]>LIMITS.height)throw new BudgetStop('初始塔高度超过网页计算保护上限');
        const cover=makeSymmetricSimulation({maxWidth:LIMITS.width,emit});
        let state;
        if(!options.fresh)for(let j=route.length;j>0;j--){
          const cached=stateCache.get(routeKey(route.slice(0,j)));
          if(cached){state=clone(cached);completed=j;break;}
        }
        if(!state){state=cover.initialize(route[0]);completed=1;saveState(state,route.slice(0,1));}
        for(;completed<route.length;completed++) {
          // Work on a PRIVATE copy. A failed child must not mutate its sibling's
          // source, dictionary aliases, or persistent target state.
          state=clone(state);state.path=[];state.allocationLog=[];
          state=cover.step(state,route[completed]);
          saveState(state,route.slice(0,completed+1));
        }
        assert(B.compare(src,state.source)===0,'源端路线与模拟状态不一致');
        return {status:'ok',source:src,target:toLists(state.target),events,route};
      },options);
      const weight=JSON.stringify(result).length;resultCache.set(key,result,weight);
      return result;
    }catch(e){
      const budget=e.name==='BudgetStop'||e.name==='SRPDBudget';
      const result={status:budget?'budget':'error',reason:e.message,route,
        lastVerifiedRoute:route.slice(0,completed)};
      // No guessed target and no larger replacement seed on failure.
      resultCache.set(key,result,JSON.stringify(result).length);return result;
    }
  }
  function saveState(state,route) {
    state.path=[];state.allocationLog=[];
    // JSON is only a conservative cache-size estimate, never the clone format:
    // the actual dictionaries are Maps with shared nodes and must retain aliases.
    const weight=JSON.stringify(state,(_,v)=>v instanceof Map?[...v]:v).length;
    stateCache.set(routeKey(route),clone(state),weight);
  }
  function reseeded(raw,options={}) {
    const expr=parse(raw),route=expr.route,key=routeKey(route);
    if(!options.fresh){const old=reseedCache.get(key);if(old)return old;}
    try {
      const result=bounded(()=>{
        const src=getSource(route);
        if(!route.length)return {status:'ok',source:src,target:[[0]],route,seedRoute:[]};
        if(!src.length)return {status:'ok',source:src,target:[],route,seedRoute:[0],height:0};
        const emit=e=>{budgetTick();if(options.emit)options.emit(e);};
        const cover=makeCover({tick:budgetTick,maxWidth:LIMITS.width,emit});
        const twoColumns=src.length===2&&!src[0].length&&src[1].length&&src[1].every(e=>e[0]===1);
        if(twoColumns&&src[1].every(e=>B.is_one(e[1]))) {
          const rows=src[1].length;
          if(rows===1)return {status:'ok',source:src,target:toLists(reachSymmetric(0,emit)),route,
            method:'symmetric-tower',depth:0};
          const state=makeSymmetricSimulation({emit}).initializeFiniteRows(src,rows);
          return {status:'ok',source:src,target:toLists(state.target),route,
            method:'symmetric-finite-rows',rows};
        }
        if(twoColumns&&src[1].length===1) {
          // Recognize only the already proved S_h / first-branch normal forms.
          // Other sources use the separate general local-cover initializer.
          let alpha=cover.rowOrdinal(src[1][0][1]),powers=0;
          while(alpha.length===1&&alpha[0].coeff===1&&alpha[0].exp.length){budgetTick();powers++;alpha=alpha[0].exp;}
          if(alpha.length===1&&!alpha[0].exp.length&&powers>0) {
            const degree=alpha[0].coeff;
            if(degree===1)return {status:'ok',source:src,target:toLists(reachSymmetric(powers,emit)),route,
              method:'symmetric-tower',depth:powers};
            const depth=powers+1;if(depth>LIMITS.height)throw new BudgetStop('重选对称塔高度上限');
            // Rebuild the seed from the actual root, then use the proven
            // first-branch initialization of that symmetric seed.
            reachSymmetric(depth,emit);
            const state=Symmetric.makeCover({tick:budgetTick,maxWidth:LIMITS.width,emit}).initialize(depth,degree);
            assert(B.compare(state.source,src)===0);
            return {status:'ok',source:src,target:toLists(state.target),route,
              method:'symmetric-first-branch',depth,degree};
          }
        }
        // Choose the least FINITE tower bound on CURRENT cumulative row
        // endpoints, not on the largest old label or on future FS indices.
        const ends=cover.endpoints(src).flat();let height=0;
        while(ends.some(a=>cover.cmp(a,cover.tower(height))>0)) {
          budgetTick();if(++height>LIMITS.height)throw new BudgetStop('重选所需塔高度超过保护上限');
        }
        const state=cover.initializeForSource(src,height);
        return {status:'ok',source:src,target:toLists(state.target),route,height,method:'general-local-cover',
          seedRoute:[state.seedIndex+1,src.length+state.reserve-2]};
      },options);
      reseedCache.set(key,result,JSON.stringify(result).length);return result;
    }catch(e) {
      const result={status:e.name==='BudgetStop'||e.name==='SRPDBudget'?'budget':'error',
        reason:e.message,route};
      reseedCache.set(key,result,JSON.stringify(result).length);return result;
    }
  }
  function countText(graph) {
    const tick=S.budget({ms:180,work:600000});
    return S.countResult(graph,tick).values.map(v=>v===null?'?':String(v)).join(',')||'0';
  }
  function sourcePlain(raw){const a=source(raw);return a.length?B.display(a):'0';}
  function sourceHTML(raw){const a=source(raw);return a.length?B.display(a,true):'0';}
  function failureText(result){return result.status==='budget'?'?（模拟未算出：'+result.reason+'）':'?（模拟校验失败：'+result.reason+'）';}
  function paired(raw,mode='count',asHTML=false,freshSeed=false) {
    const expr=parse(raw),result=freshSeed?reseeded(expr):simulated(expr),a=asHTML?sourceHTML(expr):sourcePlain(expr);
    const value=result.status==='ok'?(mode==='list'?S.plainGraph(result.target):countText(result.target)):failureText(result);
    const suffix=freshSeed?'（重选）':'';
    if(asHTML)return '<span style="font-family:inherit" title="'+htmlEscape(routeText(expr.route))+'">'+
      'TBMS '+a+' ≤ SRPD '+htmlEscape(value+suffix)+'</span>';
    return 'TBMS '+a+' <= SRPD '+value+suffix+' @ '+routeText(expr.route);
  }
  function FS(raw,n) {
    natural(n);if(n>LIMITS.index)throw new BudgetStop('基本列指标上限');
    const expr=parse(raw);
    return bounded(()=>{
      const before=getSource(expr.route);if(!before.length)return expr;
      const next={version,route:expr.route.concat(n)};
      assert(next.route.length<=LIMITS.route,'路径长度上限');
      const after=getSource(next.route);assert(B.compare(after,before)<0,'TBMS 基本列未严格下降');
      return next;
    });
  }
  function compare(a,b){return bounded(()=>B.compare(getSource(parse(a).route),getSource(parse(b).route)));}
  function isLimit(raw){return bounded(()=>B.TBM.is_limit(getSource(parse(raw).route)));}
  function clearCaches(){sourceCache.clear();stateCache.clear();resultCache.clear();reseedCache.clear();}
  const debug={parse,source,simulated,reseeded,toLists,fromLists,clearCaches,provenance,LIMITS,S,B,M,
    cacheInfo:()=>({source:sourceCache.data.size,states:stateCache.data.size,results:resultCache.data.size,
      reseeded:reseedCache.data.size,stateWeight:stateCache.weight}),makeCover,Symmetric,
    makeSymmetricSimulation,reachSymmetric,bounded,engine:'symmetric-v2'};
  const definition={
    id:'tbms-epsilon0-le-srpd-history-v1',name:'TBMS ≤ SRPD',simple_name:'TBMS ≤ SRPD',
    description:[
      '范围：普通 TBMS 的 E=()(1^()(1,1))，即 ()(1^ε₀)，及从 E 出发的全部基本列后代；不是整个 TBMS。',
      '按 TBMS 展开，右边显示当前历史下的 SRPD 模拟状态。源一步通常对应若干目标基本列步及经过认证的局部下降宏。',
      '这是下降秩下界／历史依赖模拟，不是内部保序嵌入，也不声称同指标基本列交换或两边相等。',
      'SRPD 使用更新后的隐含根版：起点 [0]，计数 2；不再添加旧版首空列或首个 1。',
      '对称式版：E[0] 对应 1,2；E[h]（h≥1）对应 1,2,4,…,2^(h+1),2^h,…,4,2；后续沿此状态持续下降。',
      'h≥2 时下一次指标 n 用对称式的 [ceil(n/(2h+1))] 建立固定次数 n+1 的分层字典，不重选更大起点。',
      '默认对照计数；可切换对照父列表、重选起点、TBMS 原式、展开路径。输入 E[2][1] 可精确恢复模拟历史。',
      '重选视图优先识别已证明的对称塔、第一分支与有限单位行承载；其余式子仍使用通用局部对角覆盖，不伪称都已压入同一对称式。',
      '重选有时显著缩小 SRPD 上界，但不保证比历史版小，也不保证沿展开下降；这不是同一个目标的持续模拟。',
      '所有 FS 接口均采用 TBMS 默认 FS；NER 的比较只比较 TBMS 原式，不比较右侧 SRPD 状态。',
      '单次模拟约 0.9 秒保护，并限制宽度、格数及缓存。? 表示当前对应尚未算出；仍可继续展开 TBMS，不猜测对应。',
      '同一个 TBMS 式子沿不同路径出现时可以显示不同 SRPD 状态。大小符号的依据是纸面模拟不变量，不是有限测试。'
    ],
    display:{name:'对照·计数',plain:raw=>paired(raw),html:raw=>paired(raw,'count',true),from_display:parse},
    display_equiv:{
      '对照·父列表':{name:'对照·父列表',plain:raw=>paired(raw,'list'),html:raw=>paired(raw,'list',true),from_display:parse},
      '重选起点·计数':{name:'重选起点·计数',plain:raw=>paired(raw,'count',false,true),html:raw=>paired(raw,'count',true,true),from_display:parse},
      '重选起点·父列表':{name:'重选起点·父列表',plain:raw=>paired(raw,'list',false,true),html:raw=>paired(raw,'list',true,true),from_display:parse},
      'TBMS 原式':{name:'TBMS 原式',plain:sourcePlain,html:sourceHTML},
      '展开路径':{name:'展开路径',plain:raw=>routeText(parse(raw).route),from_display:parse},
    },
    FS,FS_alter:FS,FS_short:FS,compare,is_limit:isLimit,
    init:()=>[{version,route:[]},{version,route:[0,0,0]}],debug,
  };
  if(typeof register_notation==='function')register_notation(definition);
  if(typeof module!=='undefined'&&module.exports)module.exports=definition;
})();
