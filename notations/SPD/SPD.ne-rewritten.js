/* SPD — Slot Profile Diagrams (research candidate, 2026-09-14).
   Real input is a finite list of integer quadruple columns, not a tree.
   Canonical guarded connectors; visible-head carry; no external dependency.
   See definition.zh-CN.md for the rule and proof boundary. >= IPD is not
   claimed as a theorem. Resource errors never return a truncated expansion. */
(() => {
'use strict';

const TOP='Limit of SPD';
const LIMITS=Object.freeze({ms:900,countMs:200,work:2400000,columns:2048,
    rows:60000,nodes:80000,slots:400000,pairs:200000,instances:140000,
    text:1200000,paths:128});
function fail(message) { throw new Error('SPD：'+message); }
function limited(message) {
    const error=new Error('SPD：预算内未算完（'+message+'）；没有返回截断项。');
    error.name='SPDLimit';throw error;
}
const sign=(a,b)=>(a>b)-(a<b);
function natural(n) {
    if(typeof n==='bigint'&&n>=0n)return n;
    if(typeof n==='number'&&Number.isSafeInteger(n)&&n>=0)return BigInt(n);
    fail('指标必须是非负整数。');
}
function small(n,maximum,what) {
    n=natural(n);if(n>BigInt(maximum))limited(what);return Number(n);
}

class Context {
    constructor(ms=LIMITS.ms) {
        this.end=Date.now()+ms;this.work=0;this.parsed=new Map();
        this.pool=new Outlines(this);
    }
    tick(n=1) {
        this.work+=n;
        if(this.work>LIMITS.work)limited('工作量');
        if(Date.now()>this.end)limited('时间');
    }
}
let active=null;
function context() {
    if(!active) {
        const current=active=new Context();
        queueMicrotask(()=>{if(active===current)active=null;});
    }
    return active;
}

// Temporary shared outlines reconstructed from the actual column relations.
// Kinds: 0=Z, 1=fixed ROOT, 2=N(head;arguments), 3=PARENT, 4=SELF.
class Outlines {
    constructor(b) {
        this.b=b;this.nodes=[{kind:0,value:0,depth:0,args:[]}];
        this.intern=new Map([['z',0]]);this.pairs=new Map();
        this.instances=new Map();this.slots=0;
    }
    add(key,node) {
        this.b.tick();
        if(this.intern.has(key))return this.intern.get(key);
        if(this.nodes.length>=LIMITS.nodes||this.slots+node.args.length>LIMITS.slots)
            limited('共享轮廓容量');
        const id=this.nodes.length;this.nodes.push(node);this.intern.set(key,id);
        this.slots+=node.args.length;return id;
    }
    atom(value) {return this.add('r'+value,{kind:1,value,depth:0,args:[]});}
    parent() {return this.add('a',{kind:3,value:0,depth:0,args:[]});}
    self() {return this.add('b',{kind:4,value:0,depth:0,args:[]});}
    node(head,args) {
        let depth=this.nodes[head].depth+1;
        for(const a of args)depth=Math.max(depth,this.nodes[a].depth);
        return this.add('n'+head+':'+args.join(','),{kind:2,head,args:args.slice(),depth});
    }
    known(a,b) {
        if(a===b)return 0;
        const x=this.nodes[a],y=this.nodes[b];
        if(x.depth!==y.depth)return sign(x.depth,y.depth);
        if(x.kind!==2||y.kind!==2)return sign(x.kind,y.kind)||sign(x.value,y.value);
        return this.pairs.get(a+':'+b);
    }
    remember(a,b,r) {
        if(this.pairs.size+2>LIMITS.pairs)limited('轮廓比较缓存');
        this.pairs.set(a+':'+b,r);this.pairs.set(b+':'+a,-r);
    }
    compare(a,b) {
        const stack=[[a,b,0,0]];
        while(stack.length) {
            this.b.tick();
            const [u,v,phase,i]=stack.pop();
            if(this.known(u,v)!==undefined)continue;
            const x=this.nodes[u],y=this.nodes[v];
            if(phase<2) {
                const children=phase===0?x.args:y.args,other=phase===0?v:u;
                if(i===children.length){stack.push([u,v,phase+1,0]);continue;}
                const r=this.known(children[i],other);
                if(r===undefined){stack.push([u,v,phase,i],[children[i],other,0,0]);}
                else if(r>=0)this.remember(u,v,phase===0?1:-1);
                else stack.push([u,v,phase,i+1]);
            } else if(phase===2) {
                const r=this.known(x.head,y.head);
                if(r===undefined)stack.push([u,v,2,0],[x.head,y.head,0,0]);
                else if(r)this.remember(u,v,r);
                else if(x.args.length!==y.args.length)this.remember(u,v,sign(x.args.length,y.args.length));
                else stack.push([u,v,3,0]);
            } else {
                if(i===x.args.length)fail('轮廓规范化内部校验失败。');
                const r=this.known(x.args[i],y.args[i]);
                if(r===undefined)stack.push([u,v,3,i],[x.args[i],y.args[i],0,0]);
                else if(r)this.remember(u,v,r);
                else stack.push([u,v,3,i+1]);
            }
        }
        return this.known(a,b);
    }
    atParent(root,p) {
        const stack=[root];
        while(stack.length) {
            this.b.tick();
            const id=stack[stack.length-1],key=id+':'+p;
            if(this.instances.has(key)){stack.pop();continue;}
            const n=this.nodes[id];let result;
            if(n.kind===0||n.kind===1||n.kind===4)result=id;
            else if(n.kind===3)result=this.atom(p);
            else {
                const children=[n.head,...n.args];
                const missing=children.find(x=>!this.instances.has(x+':'+p));
                if(missing!==undefined){stack.push(missing);continue;}
                result=this.node(this.instances.get(n.head+':'+p),n.args.map(x=>this.instances.get(x+':'+p)));
            }
            if(this.instances.size>=LIMITS.instances)limited('父上下文缓存');
            this.instances.set(key,result);stack.pop();
        }
        return this.instances.get(root+':'+p);
    }
}

class Diagram {
    constructor(b,columns=[]) {
        this.b=b;this.pool=b.pool;this.cols=[];this.heads=[];this.rows=0;
        for(const c of columns)this.append(c);
    }
    at(h,p) {return this.pool.atParent(this.heads[h],p);}
    headKey(h,k,p) {return this.pool.compare(this.at(h,p),this.at(k,p))||sign(h,k);}
    pair(h,s,k,t,p) {return this.headKey(h,k,p)||this.headKey(s,t,p);}
    profile(a,b) {
        return this.pool.compare(this.at(a[0],a[1]),this.at(b[0],b[1]))||sign(a[0],b[0])||
            this.pool.compare(this.at(a[2],a[1]),this.at(b[2],b[1]))||sign(a[2],b[2])||sign(a[3],b[3]);
    }
    edge(a,b) {return sign(a[1],b[1])||this.profile(a,b);}
    append(input) {
        this.b.tick();const j=this.cols.length;
        if(j>=LIMITS.columns)limited('列数');
        const best=new Map();
        for(const e of input) {
            this.b.tick();
            if(!Array.isArray(e)||e.length!==4||e.some(x=>!Number.isSafeInteger(x)||x<0))
                fail('每条关系需要四个非负整数。');
            const [h,p,s,q]=e;
            if(!(h<=p&&s<=p&&p<j&&(q<=p||q===j||q===j+1)))
                fail('第 '+j+' 列有越界关系；须 h,s≤p<j，q≤p 或为 */+。');
            const key=h+','+p+','+s,old=best.get(key);
            if(!old||old[3]<q)best.set(key,e.slice());
            if(best.size+this.rows>LIMITS.rows)limited('关系数');
        }
        const rows=Array.from(best.values()).sort((a,b)=>-this.edge(a,b));
        this.cols.push(rows);this.rows+=rows.length;
        const visible=rows.filter(e=>e[3]!==j+1);
        if(!visible.length){this.heads.push(0);return j;}
        let h=visible[0][0];
        for(const e of visible)if((this.pool.compare(this.heads[e[0]],this.heads[h])||sign(e[0],h))>0)h=e[0];
        const fiber=visible.filter(e=>e[0]===h).sort((a,b)=>sign(b[1],a[1])||sign(b[2],a[2])||sign(b[3],a[3]));
        const args=[];
        for(const [,p,s,q] of fiber)args.push(this.heads[s],q===p?this.pool.parent():q===j?this.pool.self():this.pool.atom(q));
        this.heads.push(this.pool.node(this.heads[h],args));return j;
    }
    control() {
        let best=this.cols.at(-1)[0];
        for(const e of this.cols.at(-1))if((this.profile(e,best)||sign(e[1],best[1]))>0)best=e;
        return best;
    }
}

function moveRow(e,oldChild,newChild,move) {
    const [h,p,s,q]=e;
    return [move(h),move(p),move(s),q===oldChild+1?newChild+1:q===oldChild?newChild:move(q)];
}
function seed(n,b) {
    n=small(n,LIMITS.columns-1,'种子长度');
    return new Diagram(b,Array.from({length:n+1},(_,j)=>j?[[j-1,j-1,j-1,j]]:[]));
}
function connector(d,e,j) {
    const [h,c,s]=e;
    // Preserve OLD outline templates. Only their cut-address coordinates rise.
    const H=d.at(h,j),hi=h===c?j:h,S=d.at(s,j),si=s===c?j:s;
    const rows=[];
    for(let k=0;k<=j;k++) {
        const r=d.pool.compare(d.at(k,j),H)||sign(k,hi);
        if(r>0)continue;
        for(let t=0;t<=j;t++) {
            d.b.tick();
            if(r<0||(d.pool.compare(d.at(t,j),S)||sign(t,si))<0)rows.push([k,j,t,j+2]);
            if(rows.length+d.rows>LIMITS.rows)limited('连接关系数');
        }
    }
    return rows;
}
function expand(d,n,b) {
    n=natural(n);
    if(d===null)return seed(small(n,LIMITS.columns-1,'顶端指标'),b);
    const x=d.cols.length-1;
    if(x<0)return d;
    if(n===0n||!d.cols[x].length)return new Diagram(b,d.cols.slice(0,-1));
    n=small(n,LIMITS.columns,'展开指标');
    const chosen=d.control(),[h,c]=chosen,result=new Diagram(b,d.cols.slice(0,-1));
    let shift=0;
    for(let block=0;block<n;block++) {
        b.tick();
        const move=i=>i<c?i:i+shift,j=x+shift;
        const moved=moveRow(chosen,x,j,move),[hh,cc,ss,qq]=moved,seam=[];
        for(const e of d.cols[x]) {
            if(e!==chosen)seam.push(moveRow(e,x,j,move));
            else if(qq)seam.push([hh,cc,ss,qq===j+1?j:qq===j?cc:qq-1]);
        }
        for(let k=0;k<=cc;k++)for(let t=0;t<=cc;t++) {
            b.tick();if(result.pair(k,t,hh,ss,cc)<0)seam.push([k,cc,t,j+1]);
            if(seam.length+result.rows>LIMITS.rows)limited('低行包容量');
        }
        if(block)for(const e of d.cols[c])
            if(e[3]===c+1||e[0]===h)seam.push(moveRow(e,c,j,move));
        result.append(seam);
        const bridge=connector(result,moved,j);
        if(bridge.length)result.append(bridge);
        shift+=x-c+1+(bridge.length?1:0);
        const next=i=>i<c?i:i+shift;
        for(let i=c;i<x;i++)result.append(d.cols[i].map(e=>moveRow(e,i,next(i),next)));
    }
    return result;
}

function write(d) {
    if(d===null)return TOP;
    if(!d.cols.length)return '0';
    return d.cols.map((c,j)=>'['+c.map(([h,p,s,q])=>h+','+p+','+s+','+(q===j+1?'+':q===j?'*':q)).join(';')+']').join('');
}
function parse(raw,b) {
    if(typeof raw!=='string')fail('表达式必须是文字。');
    if(raw.length>LIMITS.text)limited('输入长度');
    if(b.parsed.has(raw))return b.parsed.get(raw);
    let text=raw.replace(/\s+/g,''),paths=[];
    while(/\[\d+\]$/.test(text)) {
        const match=/\[(\d+)\]$/.exec(text);
        if(match[1].length>100)limited('指标长度');
        paths.unshift(BigInt(match[1]));
        text=text.slice(0,match.index);if(paths.length>LIMITS.paths)limited('输入展开路径');
    }
    let d;
    if(/^(?:LimitofSPD|Limit|TOP|Top|T)$/i.test(text))d=null;
    else if(/^S\d+$/i.test(text)) {
        if(text.length>10)limited('种子指标长度');
        d=seed(BigInt(text.slice(1)),b);
    }
    else if(/^C\((?:\d+(?:,\d+)*)?\)$/i.test(text)||/^\d+(?:,\d+)+$/.test(text)) {
        const digits=/^C/i.test(text)?text.slice(2,-1):text;
        const parts=digits?digits.split(','):[];
        if(parts.some(x=>x.length>100))limited('计数数字长度');
        d=fromCounts(parts.map(BigInt),b);
    }
    else if(/^\d+$/.test(text)) {
        if(text.length>10)limited('自然数长度');
        const n=small(BigInt(text),LIMITS.columns,'自然数长度');
        d=new Diagram(b,Array.from({length:n},()=>[]));
    } else {
        if(!/^(?:\[[^\[\]]*\])+$/.test(text))fail('请输入 S3、Top[3]、自然数或完整列列表。');
        d=new Diagram(b);
        for(const match of text.matchAll(/\[([^\[\]]*)\]/g)) {
            b.tick();const j=d.cols.length;
            const rows=match[1]===''?[]:match[1].split(';').map(row=>{
                const parts=row.split(',');
                if(parts.length!==4||!parts.slice(0,3).every(x=>/^\d+$/.test(x))||! /^(?:\d+|\*|\+)$/.test(parts[3]))
                    fail('关系列表格式为 [h,p,s,q;…]，q 可写 * 或 +。');
                return parts.map((x,i)=>i===3&&x==='*'?j:i===3&&x==='+'?j+1:Number(x));
            });d.append(rows);
        }
    }
    for(const n of paths)d=expand(d,n,b);
    b.parsed.set(raw,d);return d;
}
function order(a,b) {
    if(a===null)return b===null?0:1;
    if(b===null)return -1;
    for(let j=0;j<Math.min(a.cols.length,b.cols.length);j++) {
        const x=a.cols[j],y=b.cols[j];
        for(let i=0;i<Math.min(x.length,y.length);i++) {const r=a.edge(x[i],y[i]);if(r)return r;}
        if(x.length!==y.length)return sign(x.length,y.length);
    }
    return sign(a.cols.length,b.cols.length);
}
function counts(d) {
    if(d===null)return null;
    const result=[],cache=new Map();
    for(let j=0;j<d.cols.length;j++) {
        const best=new Map();let total=1n;
        for(const e of d.cols[j])if(!best.has(e[1])||d.profile(e,best.get(e[1]))>0)best.set(e[1],e);
        for(const [p,[h,,s,q]] of best) {
            if(!cache.has(p)) {
                const indices=Array.from({length:p+1},(_,i)=>i).sort((a,b)=>d.headKey(a,b,p));
                const rank=[];indices.forEach((i,r)=>{rank[i]=r;});cache.set(p,rank);
            }
            const rank=cache.get(p),digit=q===j+1?p+3:q===j?p+2:q+1;
            total+=BigInt(digit)+BigInt(p+3)*(BigInt(p+1)*BigInt(rank[h])+BigInt(rank[s]));
        }
        result.push(total);
    }
    return result;
}
// Decode ONLY standard count sequences, using maximal descendants of a fixed
// width. No raw-list inverse is claimed. All loops share the event budget.
function fromCounts(target,b) {
    const m=target.length;
    if(m>LIMITS.columns)limited('计数序列长度');
    if(!m)return new Diagram(b);
    for(let j=0;j<m;j++) {
        const k=BigInt(j),upper=1n+(k*(k+1n)/2n)**2n+k*(k+1n)*(2n*k+1n)/3n;
        if(target[j]<1n||target[j]>upper)fail('这不是标准 SPD 的计数序列。');
    }
    let d=seed(m-1,b);
    for(let j=0;j<m;j++) {
        b.tick();
        if(d.cols.length<=j)fail('这不是标准 SPD 的计数序列。');
        const value=counts(d)[j];
        if(value<target[j])fail('这不是标准 SPD 的计数序列。');
        if(value===target[j])continue;
        d=new Diagram(b,d.cols.slice(0,j+1));
        // Freeze the prefix until just before the desired final digit.
        for(let left=value-target[j]-1n;left>0n;left--) {
            b.tick();
            d=new Diagram(b,expand(d,1,b).cols.slice(0,j+1));
        }
        // Any sufficient block count has the same first m columns as G[m].
        // Each block has at least L+1 columns; avoid building unused tails.
        const blocks=Math.ceil((m-j)/(j-d.control()[1]+1));
        d=new Diagram(b,expand(d,blocks,b).cols.slice(0,m));
    }
    const actual=counts(d);
    if(actual.length!==m||actual.some((v,j)=>v!==target[j]))
        fail('这不是标准 SPD 的计数序列。');
    return d;
}
const escape=s=>String(s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const span=s=>'<span style="font-family:inherit;white-space:nowrap">'+escape(s)+'</span>';
function plain(raw) {return write(parse(raw,context()));}
function countPlain(raw) {
    try {const b=new Context(LIMITS.countMs),r=counts(parse(raw,b));return r===null?TOP:r.length?r.join(','):'0';}
    catch(error){if(error.name==='SPDLimit')return '计数预算内未算完';throw error;}
}
function latex(raw) {return '\\texttt{'+plain(raw).replace(/[\\{}_$%&#^]/g,c=>'\\'+c)+'}';}

register_notation({
    id:'spd-research-20260914',name:'SPD',simple_name:'SPD',
    description:[
        'SPD（Slot Profile Diagrams，潜边轮廓图），研究候选；与 IPD 的整体大小尚未证明。',
        '每列 [...]；每条关系四个整数 h,p,s,q：头引用、父列、参数引用、根状态。h,s≤p<当前列号。',
        'q≤p 为 ROOT；* 为 SELF；+ 为待激活（LATENT），不是指向下一列。展开中 +→*→p→p−1→…→0→删除。',
        '待激活行仍参与比较和展开，但暂不进入该列的派生轮廓。轮廓只读取可见的最高头纤维。',
        '输入 S0、S3[2]、Top[3][2]、自然数、完整列表，或标准计数序列 C(1,3,16)/1,3,16。',
        '计数解码返回唯一标准式；不合法的数列与预算不足分开报错，不反解任意 raw 图。单个自然数仍表示空列个数。',
        'Top[n]=S_n：S_n 是长度 n+1 的相邻引用链。有限项[0]删末列；A[n]总是A[n+1]的完整列前缀。',
        '按列首差比较，不搜索展开路径。正展开只改变旧末列并追加有限块；来源列保持纯副本。',
        '后续块携带源切点的全部待激活行及与当前控制同头的可见行。规范连接守卫允许引用新生成的列。',
        '计数为精确闭式，空列计数1，正展开使旧末列计数恰减1。使用BigInt，不逐步清空来计数。',
        '列表检查结构合法性，不保证手写输入从Top可达。良序列序的主张只针对标准可达域。',
        '有 KPω+存在不可数序数下的纸面后端论证；本版本没有Lean证书。执行预算不属于数学定义。'
    ],
    display:{name:'列表',plain,html:raw=>span(plain(raw)),latex,from_display:plain},
    display_equiv:{'计数序列':{name:'计数序列',plain:countPlain,html:raw=>span(countPlain(raw)),
        latex:raw=>{const s=countPlain(raw);return /^[\d,]+$/.test(s)?s:'\\text{'+s+'}';}}},
    FS:(raw,n)=>{const b=context();return write(expand(parse(raw,b),n,b));},
    FS_alter:(raw,n)=>{const b=context();return write(expand(parse(raw,b),n,b));},
    FS_short:(raw,n)=>{const b=context();return write(expand(parse(raw,b),n,b));},
    compare:(a,b)=>{const c=context();return order(parse(a,c),parse(b,c));},
    is_limit:raw=>{const d=parse(raw,context());return d===null||!!d.cols.at(-1)?.length;},
    init:()=>[TOP,'[]','0'],
    debug:{limits:LIMITS,columns:raw=>{const d=parse(raw,context());return d===null?null:d.cols.map(c=>c.map(e=>e.slice()));},
        from_columns:columns=>write(new Diagram(context(),columns)),
        counts:raw=>{const b=new Context();return counts(parse(raw,b));},
        storage:()=>active?{nodes:active.pool.nodes.length,pairs:active.pool.pairs.size,work:active.work}:null}
});
})();
