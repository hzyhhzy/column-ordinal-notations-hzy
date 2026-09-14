/* IPD — Iterated Profile Diagrams, zero-start version, 2026-09-14.
   Standalone ne-rewritten custom notation. No network, dependencies, eval,
   operation-history representation, or call to another notation.
   The mathematical rules are in Pool.seed/lower and expand below.
   Well-ordering and wY/TPD comparisons have concrete research arguments,
   not a completed independent audit or a Lean certificate. */
(() => {
'use strict';

const TOP = 'Limit of IPD', CAP = -1;
const LIMITS = Object.freeze({
    eventMs:900, countMs:180, work:1500000, countWork:700000,
    columns:4096, edges:100000, level:1000000, arity:8192, depth:160,
    nodes:60000, slots:800000, comparisonCache:180000, lowerCache:40000,
    text:1000000, renderedChars:8000000, path:256,
    countPhases:40000, countBits:65536, countText:60000,
    countMemo:12000, countMemoSlots:140000, countMemoChars:3000000,
    countCacheEntries:512, countCacheChars:4000000
});

function limit(reason, counting=false) {
    const error = new Error('IPD：'+(counting?'计数':'操作')+'预算内未算完（'+reason+'）；没有返回截断项。');
    error.name = 'IPDLimit';
    throw error;
}
function invalid(reason) { throw new Error('IPD：'+reason); }
function natural(value) {
    if (typeof value==='bigint' && value>=0n) return value;
    if (typeof value==='number' && Number.isSafeInteger(value) && value>=0) return BigInt(value);
    invalid('指标必须是非负安全整数或 BigInt。');
}
function boundedNatural(value, maximum, reason, counting=false) {
    const n=natural(value);
    if (n>BigInt(maximum)) limit(reason,counting);
    return Number(n);
}

class Context {
    constructor(counting=false) {
        this.counting=counting;
        this.end=Date.now()+(counting?LIMITS.countMs:LIMITS.eventMs);
        this.work=0; this.depth=0; this.rendered=0; this.phases=0; this.memoHits=0;
        this.parsed=new Map(); this.renderCache=new Map(); this.countContext=null;
        this.pool=new Pool(this);
    }
    tick(amount=1) {
        this.work+=amount;
        if (this.work>(this.counting?LIMITS.countWork:LIMITS.work)) limit('工作量',this.counting);
        if (Date.now()>this.end) limit('时间',this.counting);
    }
    enter() { this.tick(); if (++this.depth>LIMITS.depth) {this.depth--;limit('树递归深度',this.counting);} }
    leave() { this.depth--; }
    integer(value) {
        if (value<0n || value.toString(2).length>LIMITS.countBits) limit('准确整数位数',true);
        return value;
    }
}
let active=null;
function context() {
    if (!active) {
        active=new Context();
        const current=active;
        queueMicrotask(()=>{if(active===current) active=null;});
    }
    return active;
}

// A level-zero value is a moving column address. At positive levels it is
// a shared node ID; ID 0 is ZERO. Head trees and child trees both share nodes.
class Pool {
    constructor(b) {
        this.b=b; this.nodes=[null]; this.index=new Map(); this.slots=0;
        this.comparisons=new Map(); this.lowers=new Map();
    }
    make(d,h,children=[]) {
        this.b.tick();
        if (children.length>LIMITS.arity) limit('节点元数',this.b.counting);
        const key=d+':'+h+':'+children.join(',');
        if (this.index.has(key)) return this.index.get(key);
        if (this.nodes.length>=LIMITS.nodes || this.slots+children.length+1>LIMITS.slots)
            limit('共享树容量',this.b.counting);
        const id=this.nodes.length;
        this.nodes.push({d,h,children:children.slice()}); this.index.set(key,id);
        this.slots+=children.length+1;
        return id;
    }
    seed(d,n,p,j) {
        if (d===0) return n===0?p:j;
        return n===0?0:this.make(d,CAP,Array(n-1).fill(0));
    }
    cmp(d,a,c) {
        this.b.tick();
        if (a===c) return 0;
        if (d===0 || a===0 || c===0) return Math.sign(a-c);
        const key=d+':'+a+':'+c;
        if (this.comparisons.has(key)) return this.comparisons.get(key);
        this.b.enter();
        let result;
        try {
            const x=this.nodes[a], y=this.nodes[c];
            if (x.children.some(t=>this.cmp(d,t,c)>=0)) result=1;
            else if (y.children.some(t=>this.cmp(d,t,a)>=0)) result=-1;
            else {
                result=x.h===y.h?0:x.h===CAP?1:y.h===CAP?-1:this.cmp(d-1,x.h,y.h);
                if (!result) result=Math.sign(x.children.length-y.children.length);
                for (let i=0;!result && i<x.children.length;i++) result=this.cmp(d,x.children[i],y.children[i]);
                if (!result) invalid('共享树规范化内部错误。');
            }
        } finally {this.b.leave();}
        if (this.comparisons.size<LIMITS.comparisonCache) this.comparisons.set(key,result);
        return result;
    }
    profile(a,c) { return Math.sign(a[1]-c[1]) || this.cmp(a[1],a[2],c[2]); }
    maximum(d,values) { let m=0;for(const v of values) if(this.cmp(d,v,m)>0)m=v;return m; }
    lower(d,t,p,j,n) {
        this.b.tick();
        if (d===0) return t===0?null:t===j?p:t-1;
        if (t===0) return null;
        const key=[d,t,p,j,n].join(':');
        if (this.lowers.has(key)) return this.lowers.get(key);
        this.b.enter();
        let result;
        try {
            const {h,children:a}=this.nodes[t], k=a.length;
            const smaller=h===CAP?this.seed(d-1,n,p,j):this.lower(d-1,h,p,j,n);
            let m=k?this.maximum(d,[this.make(d,h),...a]):0;
            const heads=k?[[h,k-1]]:[];
            if (smaller!==null) heads.push([smaller,n]);
            // Exact pruning: the rightmost NON-FINAL nonzero position, plus
            // the final position when nonzero. Keeping just one is incorrect.
            const positions=[];
            for(let i=k-2;i>=0;i--) if(a[i]!==0){positions.push(i);break;}
            if(k && a[k-1]!==0) positions.push(k-1);
            const lowered=positions.map(i=>[i,this.lower(d,a[i],p,j,n)]);
            for(let round=0;round<=n;round++) {
                this.b.tick();
                const candidates=[m];
                for(const [head,arity] of heads) candidates.push(this.make(d,head,Array(arity).fill(m)));
                for(const [i,low] of lowered)
                    candidates.push(this.make(d,h,[...a.slice(0,i),low,...Array(k-i-1).fill(m)]));
                m=this.maximum(d,candidates);
            }
            result=m;
        } finally {this.b.leave();}
        if(this.lowers.size<LIMITS.lowerCache) this.lowers.set(key,result);
        return result;
    }
    lowerEdge(e,j,n) {
        const [p,d,t]=e, low=this.lower(d,t,p,j,n);
        return low!==null?[p,d,low]:d?[p,d-1,this.seed(d-1,n,p,j)]:null;
    }
    mover(phi) {
        const memo=new Map();
        const visit=(d,t)=>{
            this.b.tick();
            if(d===0)return phi(t);
            if(t===0)return 0;
            const key=d+':'+t;
            if(memo.has(key))return memo.get(key);
            this.b.enter();
            let result;
            try {
                const a=this.nodes[t], h=a.h===CAP?CAP:visit(d-1,a.h);
                result=this.make(d,h,a.children.map(c=>visit(d,c)));
            } finally {this.b.leave();}
            memo.set(key,result);return result;
        };
        return e=>[phi(e[0]),e[1],visit(e[1],e[2])];
    }
}

function normalize(column,b) {
    const values=new Map();
    for(const e of column) {
        b.tick();
        if(!values.has(e[0]) || b.pool.profile(e,values.get(e[0]))>0) values.set(e[0],e);
    }
    return [...values.values()].sort((a,c)=>c[0]-a[0]);
}
function edgeOrder(a,c,b) { return c===null?1:b.pool.profile(a,c)||Math.sign(a[0]-c[0]); }
function controller(column,b) {
    let best=null;
    for(const e of column) if(edgeOrder(e,best,b)>0) best=e;
    return best;
}
function graphOrder(g,h,b) {
    for(let j=0;j<Math.min(g.cols.length,h.cols.length);j++) {
        const a=g.cols[j], c=h.cols[j];
        for(let i=0;i<Math.min(a.length,c.length);i++) {
            const order=Math.sign(a[i][0]-c[i][0])||b.pool.profile(a[i],c[i]);
            if(order)return order;
        }
        if(a.length!==c.length)return Math.sign(a.length-c.length);
    }
    return Math.sign(g.cols.length-h.cols.length);
}

function termText(d,t,j,b) {
    b.tick();
    if(d===0)return t===j?'*':String(t);
    if(t===0)return '.';
    const key=[d,t,j].join(':');
    if(b.renderCache.has(key))return b.renderCache.get(key);
    b.enter();
    let result;
    try {
        const a=b.pool.nodes[t];
        let h=a.h===CAP?'^':termText(d-1,a.h,j,b);
        if(a.h!==CAP && d>1)h='{'+h+'}';
        const chunks=[];
        for(let i=0;i<a.children.length;) {
            let end=i+1;
            while(end<a.children.length && a.children[end]===a.children[i]) {b.tick();end++;}
            chunks.push(termText(d,a.children[i],j,b)+(end-i>1?'~'+(end-i):''));i=end;
        }
        result=h+(chunks.length?'('+chunks.join(',')+')':'');
        b.rendered+=result.length;
        if(result.length>LIMITS.text || b.rendered>LIMITS.renderedChars)limit('树文本长度',b.counting);
    } finally {b.leave();}
    b.renderCache.set(key,result);return result;
}
function makeGraph(columns,b) {
    if(columns.length>LIMITS.columns)limit('列数',b.counting);
    const cols=[], texts=[];let edges=0, chars=0;
    for(let j=0;j<columns.length;j++) {
        const col=normalize(columns[j],b);edges+=col.length;
        if(edges>LIMITS.edges)limit('边数',b.counting);
        const text='['+col.map(e=>e[0]+':'+e[1]+'/'+termText(e[1],e[2],j,b)).join(';')+']';
        chars+=text.length;if(chars>LIMITS.text)limit('表达式文本长度',b.counting);
        cols.push(col);texts.push(text);
    }
    return {cols,texts,key:texts.join('')||'0'};
}
function seed(index,b) {
    const n=boundedNatural(index,LIMITS.level,'层号',b.counting);
    return makeGraph([[],[[0,n,0]]],b);
}
function expand(g,index,b) {
    const naturalIndex=natural(index);
    if(g===null)return seed(naturalIndex,b);
    if(!g.cols.length)return g;
    if(naturalIndex===0n || !g.cols.at(-1).length)return makeGraph(g.cols.slice(0,-1),b);
    const x=g.cols.length-1, cut=controller(g.cols[x],b)[0], width=x-cut;
    if(BigInt(x)+naturalIndex*BigInt(width)>BigInt(LIMITS.columns))limit('展开列数',b.counting);
    const n=Number(naturalIndex), result=Array.from({length:x+n*width},()=>[]);
    for(let j=0;j<cut;j++)result[j].push(...g.cols[j]);
    for(let block=0;block<=n;block++) {
        const phi=k=>k<cut?k:k+block*width, move=b.pool.mover(phi);
        for(let j=cut;j<x;j++) {
            b.tick();
            for(const e of g.cols[j])result[phi(j)].push(move(e));
        }
        if(block===n)break;
        for(const e of g.cols[x]) {
            let moved=move(e);
            if(e[0]===cut)moved=b.pool.lowerEdge(moved,phi(x),block);
            if(moved!==null)result[phi(x)].push(moved);
        }
    }
    return makeGraph(result,b);
}

function parse(raw,b) {
    b.tick();
    if(typeof raw!=='string')invalid('请输入列列表、A0 或 Limit。');
    if(raw.length>LIMITS.text)limit('输入文本长度',b.counting);
    if(b.parsed.has(raw))return b.parsed.get(raw);
    const s=raw.replace(/\s+/g,'');let i=0,g;
    function take(c){if(s[i]!==c)invalid('位置 '+i+' 应为 '+c+'。');i++;}
    function integer(max=LIMITS.level) {
        const begin=i;while(i<s.length && /[0-9]/.test(s[i]))i++;
        if(i===begin)invalid('位置 '+i+' 需要非负整数。');
        if(i-begin>16)limit('结构整数长度',b.counting);
        const n=Number(s.slice(begin,i));
        if(!Number.isSafeInteger(n) || n>max)limit('结构整数范围',b.counting);
        return n;
    }
    function term(d,p,j) {
        b.enter();
        try {
            if(d===0) {
                if(s[i]==='*'){i++;return j;}
                const q=integer(LIMITS.columns);
                if(!(q<=p || q===j))invalid('引用必须是父列以前的 ROOT 或当前 SELF。');
                return q;
            }
            if(s[i]==='.'){i++;return 0;}
            let h;
            if(s[i]==='^'){i++;h=CAP;}
            else if(d>1){take('{');h=term(d-1,p,j);take('}');}
            else h=term(0,p,j);
            const children=[];
            if(s[i]==='(') {
                i++;
                if(s[i]!==')')for(;;) {
                    const child=term(d,p,j);let repeat=1;
                    if(s[i]==='~'){i++;repeat=integer(LIMITS.arity);if(repeat===0)invalid('重复次数不能为零。');}
                    if(children.length+repeat>LIMITS.arity)limit('节点元数',b.counting);
                    for(let k=0;k<repeat;k++){b.tick();children.push(child);}
                    if(s[i]!==',')break;i++;
                }
                take(')');
            }
            return b.pool.make(d,h,children);
        } finally {b.leave();}
    }
    const alias=/^(?:A|T)(\d+)/i.exec(s), top=/^(?:LimitofIPD|Limit|TOP)/i.exec(s);
    if(alias){if(alias[1].length>16)limit('结构整数长度',b.counting);i=alias[0].length;g=seed(BigInt(alias[1]),b);}
    else if(top){i=top[0].length;g=null;}
    else if(/^\d+$/.test(s)) {
        const n=integer(LIMITS.columns);g=makeGraph(Array.from({length:n},()=>[]),b);
    } else {
        const cols=[];
        while(s[i]==='[') {
            if(cols.length>=LIMITS.columns)limit('列数',b.counting);
            i++;const column=[],j=cols.length;
            if(s[i]!==']')for(;;) {
                const p=integer(LIMITS.columns);if(p>=j)invalid('父列必须严格早于本列。');
                take(':');const d=integer();take('/');column.push([p,d,term(d,p,j)]);
                if(s[i]!==';')break;i++;
            }
            take(']');cols.push(column);
        }
        if(!cols.length)invalid('请输入 A0、A1[3]、Limit 或完整列列表。');
        g=makeGraph(cols,b);
    }
    let steps=0;
    while((alias||top) && s[i]==='[') {
        if(++steps>LIMITS.path)limit('输入展开路径',b.counting);
        take('[');const n=integer();take(']');g=expand(g,n,b);
    }
    if(i!==s.length)invalid('表达式后有未识别内容。');
    if(b.parsed.size<128)b.parsed.set(raw,g);
    return g;
}

// COUNTING AND REGISTRATION ARE BELOW. Count code is an optional display,
// not part of the definition or of graph comparison.

function heightFunction(p,j,b) {
    const memo=new Map();
    const height=(d,t)=>{
        b.tick();
        if(d===0)return BigInt(t===j?p+1:t);
        if(t===0)return 0n;
        const key=d+':'+t;
        if(memo.has(key))return memo.get(key);
        b.enter();let result=null;
        try {
            const a=b.pool.nodes[t];
            let leafHeight;
            if(a.h===CAP)leafHeight=BigInt(d===1?p+2:2);
            else {const low=height(d-1,a.h);leafHeight=low===null?null:low+1n;}
            if(leafHeight!==null) {
                const leaf=b.pool.make(d,a.h), radix=leafHeight+1n;
                if(a.children.every(c=>b.pool.cmp(d,c,leaf)<=0)) {
                    let tail=0n, supported=true;
                    for(const c of a.children) {
                        const digit=height(d,c);
                        if(digit===null){supported=false;break;}
                        tail=b.integer(tail*radix+digit+1n);
                    }
                    if(supported)result=b.integer(leafHeight+tail);
                }
            }
        } finally {b.leave();}
        memo.set(key,result);return result;
    };
    return e=>{
        const h=height(e[1],e[2]);
        return h===null?null:b.integer(h+BigInt(e[1]===0?1:p+e[1]+1));
    };
}

function staircaseFlags(g,b) {
    const result=[];let self=true,root=true,mixed=true;
    for(let j=0;j<g.cols.length;j++) {
        b.tick();const c=g.cols[j], e=c[0];
        if(j===0)self=root=mixed=c.length===0;
        else {
            const single=c.length===1 && e[0]===j-1 && e[1]===0;
            self=self && single && e[2]===j;
            root=root && (j===1?c.length===0:single && e[2]===j-2);
            mixed=mixed && single && e[2]===(j===1?0:j);
        }
        result.push({self,root,mixed});
    }
    return result;
}

function countColumn(g,j,b,flags) {
    b.tick();
    if(flags.self)return j===0?1n:b.integer(BigInt(j+2)*(1n<<BigInt(j-1)));
    if(flags.root)return j<2?1n:1n<<BigInt(j-1);
    if(flags.mixed)return j===0?1n:b.integer(BigInt(j)*(1n<<BigInt(j-1))+1n);
    const column=g.cols[j];
    if(column.every(e=>g.cols[e[0]].length===0)) {
        let total=1n, supported=true;
        for(const e of column) {
            const h=heightFunction(e[0],j,b)(e);
            if(h===null){supported=false;break;}
            total=b.integer(total+h);
        }
        if(supported)return total;
    }
    const sources=new Map(), memo=new Map();let memoSlots=0,memoChars=0;
    const source=p=>{
        if(!sources.has(p)) {
            const move=b.pool.mover(k=>k===p?j:k);
            sources.set(p,normalize(g.cols[p].map(move),b));
        }
        return sources.get(p);
    };
    function restore(original,result) {
        return {state:normalize([...original.filter(e=>!result.touched.has(e[0])),...result.state],b),
                cost:result.cost,touched:result.touched};
    }
    function* descend(initial,barrier) {
        let state=initial,cost=0n;const touched=new Set();
        while(state.length) {
            b.tick();const selected=controller(state,b);
            if(edgeOrder(selected,barrier,b)<=0)break;
            if(++b.phases>LIMITS.countPhases)limit('局部阶段数',true);
            const p=selected[0];touched.add(p);
            const lowered=b.pool.lowerEdge(selected,j,0);
            const base=normalize([...state.filter(e=>e[0]!==p),...(lowered?[lowered]:[])],b);
            let bound=barrier;const other=controller(base,b);
            if(other && edgeOrder(other,bound,b)>0)bound=other;
            const part=yield {state:source(p),barrier:bound};
            // An activated edge overwrote the old same-parent value even if
            // its final approximation jumped BELOW that dormant old value.
            state=normalize([...base.filter(e=>!part.touched.has(e[0])),...part.state],b);
            for(const q of part.touched)touched.add(q);
            cost=b.integer(cost+1n+part.cost);
        }
        return {state,cost,touched};
    }
    // Explicit stack: the number of graph columns does not consume the JS
    // recursion stack. Tree recursion has its own independent depth guard.
    const stack=[];let request={state:column,barrier:null}, result;
    for(;;) {
        b.tick();const original=request.state;
        let barrier=request.barrier;
        const awake=barrier?original.filter(e=>edgeOrder(e,barrier,b)>0):original;
        if(!awake.length)result={state:original,cost:0n,touched:new Set()};
        else {
            if(barrier && barrier[0]>awake[0][0]+1)barrier=[awake[0][0]+1,barrier[1],barrier[2]];
            const key=(barrier?barrier.join(','):'-')+'|'+awake.map(e=>e.join(',')).join(';');
            if(memo.has(key)){b.memoHits++;result=restore(original,memo.get(key));}
            else {stack.push({key,original,slots:awake.length,iterator:descend(awake,barrier)});result=undefined;}
        }
        while(stack.length) {
            const frame=stack.at(-1), next=frame.iterator.next(result);
            if(!next.done){request=next.value;break;}
            stack.pop();result=next.value;
            const slots=frame.slots+result.state.length+result.touched.size;
            if(memo.size<LIMITS.countMemo && memoSlots+slots<LIMITS.countMemoSlots
                && memoChars+frame.key.length<LIMITS.countMemoChars) {
                memo.set(frame.key,result);memoSlots+=slots;memoChars+=frame.key.length;
            }
            result=restore(frame.original,result);
        }
        if(!stack.length)return b.integer(result.cost+1n); // Delete the empty column.
    }
}

const countCache=new Map();let countCacheChars=0;
function saveCount(key,value) {
    const size=key.length+value.toString().length;
    if(size>LIMITS.countCacheChars)return;
    if(countCache.has(key)){countCacheChars-=countCache.get(key).size;countCache.delete(key);}
    while(countCache.size && (countCache.size>=LIMITS.countCacheEntries
        || countCacheChars+size>LIMITS.countCacheChars)) {
        const first=countCache.keys().next().value;
        countCacheChars-=countCache.get(first).size;countCache.delete(first);
    }
    countCache.set(key,{value,size});countCacheChars+=size;
}
function countResult(raw) {
    const event=context(), g=parse(raw,event);
    if(g===null)return {values:null,complete:true};
    const values=[];let prefix='', chars=0, countedGraph=null, flags=null;
    for(let j=0;j<g.cols.length;j++) {
        prefix+=g.texts[j];
        try {
            let value;
            if(countCache.has(prefix))value=countCache.get(prefix).value;
            else {
                const b=event.countContext??(event.countContext=new Context(true));
                b.tick();
                if(!countedGraph){countedGraph=parse(g.key,b);flags=staircaseFlags(countedGraph,b);}
                value=countColumn(countedGraph,j,b,flags[j]);saveCount(prefix,value);
            }
            chars+=value.toString().length+1;
            if(chars>LIMITS.countText)limit('计数文本长度',true);
            values.push(value);
        } catch(error) {
            if(error.name==='IPDLimit')return {values,complete:false};
            throw error;
        }
    }
    return {values,complete:true};
}
function countPlain(raw) {
    try {
        const r=countResult(raw);
        if(r.values===null)return TOP;
        const prefix=r.values.join(',');
        return r.complete?(prefix||'0'):(prefix?prefix+',…（预算内未算完）':'预算内未算完');
    } catch(error) {
        if(error.name==='IPDLimit')return '预算内未算完';
        throw error;
    }
}

function importTerm(raw,d,p,j,b) {
    b.enter();
    try {
        if(d===0) {
            if(!Number.isSafeInteger(raw) || raw<0 || !(raw<=p || raw===j))invalid('非法底层引用。');
            return raw;
        }
        if(!Array.isArray(raw))invalid('正层树应为 [] 或 [head,children]。');
        if(raw.length===0)return 0;
        if(raw.length!==2 || !Array.isArray(raw[1]))invalid('非法树节点。');
        if(raw[1].length>LIMITS.arity)limit('节点元数',b.counting);
        const h=raw[0]===CAP?CAP:importTerm(raw[0],d-1,p,j,b);
        return b.pool.make(d,h,raw[1].map(c=>importTerm(c,d,p,j,b)));
    } finally {b.leave();}
}
function exportTerm(d,t,b) {
    b.enter();
    try {
        if(d===0)return t;
        if(t===0)return [];
        const a=b.pool.nodes[t];
        return [a.h===CAP?CAP:exportTerm(d-1,a.h,b),a.children.map(c=>exportTerm(d,c,b))];
    } finally {b.leave();}
}
function fromColumns(columns) {
    const b=context();if(!Array.isArray(columns))invalid('需要列数组。');
    if(columns.length>LIMITS.columns)limit('列数');
    const cols=columns.map((column,j)=>{
        if(!Array.isArray(column))invalid('每列应为边数组。');
        return column.map(e=>{
            if(!Array.isArray(e) || e.length!==2 || !Array.isArray(e[1]) || e[1].length!==2)invalid('边应为 [parent,[level,tree]]。');
            const p=e[0],d=e[1][0];
            if(!Number.isSafeInteger(p)||p<0||p>=j)invalid('非法父列。');
            if(!Number.isSafeInteger(d)||d<0||d>LIMITS.level)invalid('非法树层。');
            return [p,d,importTerm(e[1][1],d,p,j,b)];
        });
    });
    return makeGraph(cols,b).key;
}

// Compact keys remain an internal storage format so saved NER trees and the
// expansion/counting budgets are unchanged. Visible lists never abbreviate
// repeated children. Check lengths BEFORE joining shared subtrees.
function expandedList(g,b) {
    if(g===null)return TOP;
    const memo=new Map();
    function term(d,t,j) {
        b.enter();
        try {
            if(d===0)return t===j?'*':String(t);
            if(t===0)return '.';
            const key=[d,t,j].join(':');
            if(memo.has(key))return memo.get(key);
            const a=b.pool.nodes[t];
            let h=a.h===CAP?'^':term(d-1,a.h,j);
            if(a.h!==CAP && d>1)h='{'+h+'}';
            const children=[];let size=h.length+(a.children.length?2:0);
            for(const child of a.children) {
                const text=term(d,child,j);size+=text.length+(children.length?1:0);
                if(size>LIMITS.text)limit('完整列表长度');
                children.push(text);
            }
            const text=h+(children.length?'('+children.join(',')+')':'');
            memo.set(key,text);return text;
        } finally {b.leave();}
    }
    const columns=[];let size=0;
    for(let j=0;j<g.cols.length;j++) {
        const edges=[];size+=2;
        for(const [p,d,t] of g.cols[j]) {
            const edge=p+':'+d+'/'+term(d,t,j);
            size+=edge.length+(edges.length?1:0);
            if(size>LIMITS.text)limit('完整列表长度');
            edges.push(edge);
        }
        columns.push('['+edges.join(';')+']');
    }
    return columns.join('')||'0';
}
const canonical=raw=>parse(raw,context())?.key??TOP;
const plain=raw=>{const b=context();return expandedList(parse(raw,b),b);};
const fs=(raw,n)=>{const b=context();return expand(parse(raw,b),n,b).key;};
const escape=s=>s.replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;');
const span=s=>'<span style="font-family:inherit;white-space:nowrap">'+escape(s)+'</span>';
const latex=raw=>{
    const s=plain(raw);if(s===TOP)return '\\text{Limit of IPD}';
    return '\\mathtt{'+s.replace(/[{}*^~]/g,c=>({'{':'\\{','}':'\\}','*':'\\ast ',
        '^':'\\mathsf{C}','~':'\\mathord{\\sim}'}[c]))+'}';
};

// FULL TREE VIEW. Ordinary children are joined below their node; a composite
// head is a complete lower-level tree INSIDE that node's violet frame.
// No subtree folding, run-length shorthand, external libraries, or event code.
const TREE_LIMITS=Object.freeze({milliseconds:180,occurrences:6000,chars:5000000,extent:32000});
const TREE_STYLE='<style>'+
    '.ipd-trees{display:inline-flex;flex-direction:column;align-items:flex-start;gap:7px;'+
    'font-family:inherit;line-height:1.35;vertical-align:top;white-space:normal;'+
    '--ipd-head:var(--color-primary,#8056b5);--ipd-line:var(--color-text-secondary,#777);'+
    '--ipd-border:var(--color-border,#ccc);--ipd-bg:var(--color-bg,Canvas)}'+
    '.ipd-trees .ipd-tree-counts{white-space:nowrap;font-variant-numeric:tabular-nums}'+
    '.ipd-trees .ipd-tree-columns{display:inline-flex;align-items:flex-start;gap:10px}'+
    '.ipd-trees .ipd-tree-column{display:inline-flex;flex-direction:column;align-items:center;'+
    'gap:7px;min-width:32px;padding:0 5px 5px;border-top:1px solid var(--ipd-border)}'+
    '.ipd-trees .ipd-tree-index{font-size:12px;padding:3px 0 0;font-variant-numeric:tabular-nums}'+
    '.ipd-trees .ipd-tree-edge{display:inline-flex;flex-direction:column;align-items:center;gap:3px}'+
    '.ipd-trees .ipd-tree-edge-label{display:flex;gap:10px;font-size:12px;white-space:nowrap}'+
    '.ipd-trees .ipd-tree-parent{color:var(--color-accent,#06c)}'+
    '.ipd-trees .ipd-tree-level{color:var(--ipd-head)}'+
    '.ipd-trees .ipd-tree-empty{font-size:16px;opacity:.55;padding:4px}'+
    '.ipd-trees .ipd-tree-legend{font-size:11px;opacity:.8;white-space:nowrap}'+
    '.ipd-trees svg{display:block;overflow:visible;font-family:inherit}'+
    '.ipd-trees svg text{fill:currentColor;font-family:inherit}'+
    '.ipd-trees .ipd-head-frame{fill:var(--ipd-head);fill-opacity:.055;'+
    'stroke:var(--ipd-head);stroke-opacity:.65}'+
    '.ipd-trees .ipd-node-frame{fill:var(--ipd-bg);stroke:var(--ipd-line);stroke-opacity:.65}'+
    '.ipd-trees .ipd-child-link{fill:none;stroke:var(--ipd-line);stroke-width:1.2}'+
    '.ipd-trees .ipd-head-level{fill:var(--ipd-head);font-size:11px}'+
    '</style>';

function treeLayout(g,b) {
    const deadline=Date.now()+TREE_LIMITS.milliseconds;
    let occurrences=0;
    function tick() {
        if(++occurrences>TREE_LIMITS.occurrences || Date.now()>deadline) {
            const error=new Error('完整树超出绘图预算');error.name='IPDTreeLimit';throw error;
        }
    }
    function visit(d,t,j) {
        tick();
        const a=d>0 && t!==0?b.pool.nodes[t]:null;
        let head=null,label,kind='node';
        if(d===0){label=t===j?'*':String(t);kind='atom';}
        else if(t===0){label='·';kind='zero';}
        else if(a.h===CAP)label='^';
        else if(d===1)label=a.h===j?'*':String(a.h);
        else head=visit(d-1,a.h,j);
        const children=a?a.children.map(child=>visit(d,child,j)):[];
        const boxWidth=head?Math.max(head.width+18,42+String(d-1).length*7):
            kind==='zero'?20:Math.max(28,14+label.length*8);
        const boxHeight=head?head.height+27:kind==='zero'?20:26;
        const childrenWidth=children.reduce((n,c)=>n+c.width,0)+Math.max(0,children.length-1)*10;
        const width=Math.max(boxWidth,childrenWidth);
        const height=boxHeight+(children.length?22+Math.max(...children.map(c=>c.height)):0);
        if(width>TREE_LIMITS.extent || height>TREE_LIMITS.extent) {
            const error=new Error('完整树尺寸超出绘图预算');error.name='IPDTreeLimit';throw error;
        }
        return {d,kind,label,head,children,boxWidth,boxHeight,childrenWidth,width,height};
    }
    // Build the WHOLE forest before emitting anything. On failure there is no
    // misleading partial forest, and a display failure never alters the graph.
    const columns=g.cols.map((column,j)=>column.map(([p,d,t])=>({p,d,tree:visit(d,t,j)})));
    return {columns,occurrences};
}
function treeSVG(tree,j,p) {
    const parts=[];let chars=0;
    function add(text) {
        chars+=text.length;
        if(chars>TREE_LIMITS.chars){const e=new Error('完整树图文本超限');e.name='IPDTreeLimit';throw e;}
        parts.push(text);
    }
    function draw(t,x,y) {
        const center=x+t.width/2, left=center-t.boxWidth/2;
        let childX=x+(t.width-t.childrenWidth)/2;
        for(const child of t.children) {
            const toX=childX+child.width/2,fromY=y+t.boxHeight,toY=fromY+22;
            add('<path class="ipd-child-link" data-ipd-link="child" d="M'+center+','+fromY+
                ' C'+center+','+(fromY+11)+' '+toX+','+(toY-11)+' '+toX+','+toY+'"/>');
            childX+=child.width+10;
        }
        add('<g data-ipd-node="'+t.kind+'" data-level="'+t.d+'">');
        if(t.head) {
            add('<rect class="ipd-head-frame" x="'+left+'" y="'+y+'" width="'+t.boxWidth+
                '" height="'+t.boxHeight+'" rx="7"/><text class="ipd-head-level" x="'+(left+7)+
                '" y="'+(y+13)+'">头 '+(t.d-1)+'</text>');
            add('<g data-ipd-head="'+(t.d-1)+'">');
            draw(t.head,center-t.head.width/2,y+20);add('</g>');
        } else {
            const detail=t.kind==='zero'?'第 '+t.d+' 层零树':
                t.kind==='atom'?(t.label==='*'?'SELF，当前列 '+j:'ROOT，列 '+t.label):
                '第 '+t.d+' 层节点；头 '+(t.label==='^'?'CAP':t.label==='*'?'SELF':t.label);
            add('<title>'+escape(detail)+'</title>');
            if(t.kind==='zero')add('<circle class="ipd-node-frame" cx="'+center+'" cy="'+(y+10)+'" r="9"/>');
            else add('<rect class="ipd-node-frame" x="'+left+'" y="'+y+'" width="'+t.boxWidth+
                '" height="'+t.boxHeight+'" rx="'+(t.kind==='atom'?4:7)+'"/>');
            add('<text x="'+center+'" y="'+(y+t.boxHeight/2)+'" text-anchor="middle" '+
                'dominant-baseline="central" font-size="'+(t.kind==='zero'?18:15)+'">'+escape(t.label)+'</text>');
        }
        add('</g>');
        childX=x+(t.width-t.childrenWidth)/2;
        for(const child of t.children){draw(child,childX,y+t.boxHeight+22);childX+=child.width+10;}
    }
    add('<svg xmlns="http://www.w3.org/2000/svg" role="img" aria-label="第 '+j+' 列指向第 '+p+
        ' 列的第 '+tree.d+' 层完整树" width="'+(tree.width+8)+'" height="'+(tree.height+8)+
        '" viewBox="0 0 '+(tree.width+8)+' '+(tree.height+8)+'">');
    add('<desc>实线连接同层子树；紫框内部是低一层的头树。子树从左到右有序，重复项全部画出。</desc>');
    draw(tree,4,4);add('</svg>');return parts.join('');
}
function treeHtml(raw) {
    const b=context(),g=parse(raw,b);
    if(g===null)return span(TOP);
    if(!g.cols.length)return span('0');
    try {
        const forest=treeLayout(g,b),columns=[];let size=0;
        for(let j=0;j<forest.columns.length;j++) {
            const edges=[];
            for(const {p,d,tree} of forest.columns[j]) {
                const svg=treeSVG(tree,j,p);size+=svg.length;
                if(size>TREE_LIMITS.chars){const e=new Error('完整森林文本超限');e.name='IPDTreeLimit';throw e;}
                edges.push('<span class="ipd-tree-edge" data-parent="'+p+'" data-level="'+d+'">'+
                    '<span class="ipd-tree-edge-label"><span class="ipd-tree-parent">→ '+p+'</span>'+
                    '<span class="ipd-tree-level">层 '+d+'</span></span>'+svg+'</span>');
            }
            columns.push('<span class="ipd-tree-column" data-column="'+j+'"><span class="ipd-tree-index" '+
                'title="第 '+j+' 列（从 0 编号）">'+j+'</span>'+
                (edges.join('')||'<span class="ipd-tree-empty" title="空列，没有边">∅</span>')+'</span>');
        }
        // Counting has its existing independent budget; an unfinished count
        // never suppresses or truncates a successfully drawn forest.
        const counts=countPlain(raw);
        return '<span class="ipd-trees" data-ipd-tree-view="complete">'+TREE_STYLE+
            '<span class="ipd-tree-counts">'+escape(counts)+'</span>'+
            '<span class="ipd-tree-columns">'+columns.join('')+'</span>'+
            '<span class="ipd-tree-legend">实线：同层子树　紫框：低层头树　∅：空列　·：零树</span></span>';
    } catch(error) {
        if(error.name==='IPDTreeLimit')return span('完整树超出绘图预算，请切换列表；未显示局部图。');
        throw error;
    }
}

register_notation({
    id:'ipd-v01',name:'IPD',simple_name:'IPD',
    description:[
        'IPD（Iterated Profile Diagrams，迭代轮廓图），2026-09-14 零起始版。良序及超过 wY/TPD 有具体论证路线，尚未完成独立审计。',
        '每列 [...]；边为 父列:层号/树。例如 [][0:2/.]。列号从 0 起；. 是零树，* 是 SELF，^ 是本层 CAP。',
        '正层树的头可以是更低层的树，用 {...} 包住，例如 [][0:2/{*(.)}(.,.)]；复制时树头里面的 ROOT/SELF 也移动。',
        '列表逐项写出全部子树，不使用重复省略。树形图也完整画出每个重复项；旧版省略输入仍可读取。',
        '输入 A0、A1[3]、T2、Limit[2][3]、自然数或完整列列表。自然数表示该数量的空列；计数序列不能作为一般输入。',
        'Top[n]=A_n，真实计数为 1,n+2，且 A_(n+1)[1]=A_n。有限项第 0 项删末列，A[n] 是 A[n+1] 的完整列前缀。',
        '逐列比较；列内先看父列，再看轮廓。轮廓先比树层，再用头优先级为（头标签,元数）的 LPO；不搜索展开路径来比较。',
        '默认列表；等价表示提供计数序列、树形图。图按列排列，指向父列写为 →p；普通子树用实线连接，低层头树嵌在紫框内。',
        '空列计数 1，正展开使旧末列计数减 1。计数仅作显示，不参与大小比较。树形图须使用网页的 HTML 显示模式。',
        '计数使用 BigInt、共享树、精确闭式和局部屏障缓存；预算不足保留已完成的计数前缀，不返回近似数。',
        '一次浏览器事件共享约 0.9 秒结构预算，计数另有约 0.18 秒共享预算。保护只限制执行，不改变数学规则。',
        '手写列表只检查结构合法性，不证明它从 Top 可达；良序主张的列序范围是标准可达域。'
    ],
    display:{name:'列表',plain,html:raw=>span(plain(raw)),latex,from_display:canonical},
    display_equiv:{
        '计数序列':{name:'计数序列',plain:countPlain,html:raw=>span(countPlain(raw)),
            latex:raw=>{const s=countPlain(raw);if(s===TOP)return '\\text{Limit of IPD}';
                const prefix=/^[0-9,]+/.exec(s)?.[0]??'';
                return /^[0-9,]+$/.test(s)?s:prefix+'\\ldots\\;\\text{not yet computed}';}},
        '树形图':{name:'树形图',plain,html:treeHtml,latex,from_display:canonical}
    },
    FS:fs,FS_alter:fs,FS_short:fs,
    is_limit:raw=>{const g=parse(raw,context());return g===null||!!g.cols.at(-1)?.length;},
    compare:(a,c)=>{const b=context(),g=parse(a,b),h=parse(c,b);
        return g===null?(h===null?0:1):h===null?-1:graphOrder(g,h,b);},
    init:()=>[TOP,'[]','0'],
    debug:{
        limits:LIMITS,tree_limits:TREE_LIMITS,version:'zero-start-2026-09-14',display_version:'full-trees-2026-09-14',from_columns:fromColumns,
        columns:raw=>{const b=context(),g=parse(raw,b);return g===null?null:
            g.cols.map(c=>c.map(e=>[e[0],[e[1],exportTerm(e[1],e[2],b)]]));},
        counts:raw=>{const r=countResult(raw);if(!r.complete)limit('尚有未完成列',true);return r.values;},
        count_result:countResult,
        count_stats:()=>active?.countContext?{work:active.countContext.work,phases:active.countContext.phases,
            memoHits:active.countContext.memoHits,nodes:active.countContext.pool.nodes.length}:null,
        storage:()=>active?{nodes:active.pool.nodes.length,slots:active.pool.slots,work:active.work}:null
    }
});

})();
