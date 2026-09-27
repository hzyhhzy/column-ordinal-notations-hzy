'use strict';

// Actual-M simulation for EPSILON-ROW-BOUND.zh-CN.md: TBMS rows below each
// fixed finite omega tower. The paper closure proof is separate from tests.
// The native source and target FS functions are NOT modified.
const assert = require('node:assert/strict');
const {loadTBM} = require('./load-tbm.cjs');
const {M, nat, expose} = require('../e0mn-y134258-hierarchical-20260920/ladder-cover.cjs');

function makeCover(options = {}) {
  const loader = loadTBM(), B = loader.B;
  const tick = options.tick ?? (() => {}), emit = options.emit ?? (() => {});
  const maxWidth = options.maxWidth ?? 320;
  const stats = {sourceSteps: 0, limits: 0, units: 0, deletions: 0, pumps: 0,
    newNodes: 0, checks: 0, parentChecks: 0, labelChecks: 0, orderChecks: 0, maxWidth: 0,
    maxPumpsPerStep: 0, maxHeight: 0};
  const key = a => JSON.stringify(a), add = M.debug.ordAdd;
  const one = [{exp: [], coeff: 1}];
  const power = exp => [{exp, coeff: 1}];
  function cmp(a,b) {
    for (let i = 0; i < Math.min(a.length,b.length); i++) {
      const c = cmp(a[i].exp,b[i].exp);
      if (c) return c;
      if (a[i].coeff !== b[i].coeff) return Math.sign(a[i].coeff-b[i].coeff);
    }
    return Math.sign(a.length-b.length);
  }
  const eq = (a,b) => cmp(a,b) === 0;
  function tower(h) {let a = one; while (h--) a = power(a); return a;}
  function guard(width) {
    tick();
    if (width > maxWidth) {
      const e = Error('width budget: ' + width); e.name = 'BudgetStop'; throw e;
    }
  }
  function rowOrdinal(h) {
    assert(h.length && !h[0].length);
    const depths = Array.from(h, col => {
      if (!col.length) return 0;
      assert(col.length === 1 && B.is_one(col[0][1]), 'one-row native label');
      assert(Number.isSafeInteger(col[0][0]) && col[0][0] > 0);
      return col[0][0];
    });
    let i = 0;
    function forest(depth) {
      const out = [];
      while (i < depths.length && depths[i] === depth) {
        i++;
        const exp = forest(depth + 1), last = out.at(-1);
        assert(!last || cmp(last.exp,exp) >= 0, 'canonical one-row forest');
        if (last && eq(last.exp,exp)) last.coeff++;
        else out.push({exp, coeff: 1});
      }
      assert(i === depths.length || depths[i] < depth, 'no skipped tree depth');
      return out;
    }
    const value = forest(0);
    assert.equal(i,depths.length);
    assert(value.length === 1 && value[0].coeff === 1, 'primitive monomial label');
    return value;
  }
  function endpoints(source) {
    return Array.from(source, col => {
      let a = [];
      return Array.from(col, ([value,h]) => {
        assert(Number.isSafeInteger(value) && value > 0, 'safe positive source entry');
        a = add(a,rowOrdinal(h)); return a;
      });
    });
  }
  function sourceFS(source,n) {
    tick(); assert(Number.isSafeInteger(n) && n >= 0);
    guard(n + 3);
    loader.context.expr = source; loader.context.n = n;
    return loader.run('B.TBM.FS(expr,n)',1000);
  }
  function fs(s,n) {
    const z = s.target.length, last = s.target.at(-1);
    guard(last?.length && n ? z-1+n*(z-last.at(-1).a) : Math.max(0,z-1));
    const before = s.target;
    s.target = M.FS(before,n); emit({kind:'FS',before,after:s.target,n});
    stats.maxWidth = Math.max(stats.maxWidth,s.target.length);
  }
  function trim(s,width) {
    assert(s.target.length >= width);
    while (s.target.length > width) fs(s,0);
  }
  const auxCount = s => s.target.length - (s.start+s.source.length-1);
  const nodesOf = s => s.dicts.slice(1).flatMap(d => [...d.byEnd.values()]);
  function grade(s,d,a) {
    if (!a.length) return 0;
    if (!d) {assert(eq(a,one), 'level zero contains only zero and one'); return 1;}
    const node = s.dicts[d].byEnd.get(key(a));
    assert(node && node.anchor !== null, 'unprepared ordinal endpoint at level '+d);
    return node.anchor + 1;
  }
  const resource = (s,node) => grade(s,node.level-1,node.exp)+1;
  function capacityTable(graph) {
    const table = [];
    for (let j = 0; j < graph.length; j++) {
      tick();
      const row = new Float64Array(j);
      for (const e of graph[j]) {
        assert(e.x.length === 1 && !e.x[0].exp.length);
        const p = e.a-1, r = e.x[0].coeff;
        assert(Number.isSafeInteger(r) && 0 < r && r <= e.a);
        row[p] = Math.max(row[p],r);
        for (let k = 0; k < p; k++) row[k] = Math.max(row[k],Math.min(r,table[p][k]));
      }
      table.push(row);
    }
    return (p,j) => 0 < p && p < j ? table[j-1][p-1] : 0;
  }
  function check(s,ready=true) {
    tick(); stats.checks++;
    assert(M.debug.isLegalExpr(s.target));
    if (!s.source.length) return;
    const aux = auxCount(s);
    assert(0 <= aux && aux <= s.reserve);
    if (ready) assert.equal(aux,s.reserve);
    const Q = grade(s,s.height,tower(s.height)), nodes = nodesOf(s), cap = capacityTable(s.target);
    assert(s.start >= Q);
    for (const col of s.target) for (const e of col) assert(e.x[0].coeff <= Q,'global row ceiling');
    for (let d = 1; d <= s.height; d++) {
      const sorted = [...s.dicts[d].byEnd.values()].sort((a,b) => cmp(a.end,b.end));
      let previous = d === 1 ? 0 : s.dicts[d-1].root.anchor+1;
      for (const node of sorted) {
        assert(previous < node.anchor, 'dictionary layering and strict endpoint order');
        assert(resource(s,node) <= node.anchor);
        previous = node.anchor+1;
        let base = node.base;
        for (const child of node.children) {
          assert(eq(base,child.base) && cmp(child.end,node.end) < 0);
          assert(cmp(child.exp,node.exp) < 0);
          base = child.end;
        }
        assert(eq(add(node.base,power(node.exp)),node.end));
        // Every monomial-unit prefix is registered, including predecessor of
        // a successor endpoint. This is essential to one-pump-per-level.
        let prefix = [];
        for (const term of node.end) for (let k = 0; k < term.coeff; k++) {
          assert(!prefix.length || s.dicts[d].byEnd.has(key(prefix)), 'prefix closure');
          prefix = add(prefix,power(term.exp));
        }
      }
    }
    const ports = [...nodes.map(n => n.anchor),
      ...Array.from({length:s.target.length-s.start+1},(_,i) => s.start+i)];
    for (const node of nodes) for (const p of ports) if (node.anchor < p)
      assert(cap(node.anchor,p) >= resource(s,node),
        `background d${node.level}, ${node.anchor}->${p}: ${cap(node.anchor,p)} < ${resource(s,node)}`);
    const E = endpoints(s.source), V = s.source.map(B.column_verticals), P = B.parents(s.source,V);
    const paired=[];
    for(let j=0;j<E.length;j++)for(let k=0;k<E[j].length;k++)paired.push({a:E[j][k],v:V[j][k]});
    paired.sort((a,b)=>cmp(a.a,b.a));
    for(let j=1;j<paired.length;j++) {
      assert.equal(Math.sign(B.vertical_compare(paired[j-1].v,paired[j].v)),
        cmp(paired[j-1].a,paired[j].a),'native cumulative endpoint order equals CNF order');
      stats.orderChecks++;
    }
    for (let j = 0; j < s.source.length; j++) {
      assert.equal(P[j].length,s.source[j].length);
      for (let k = 0; k < P[j].length; k++)
        assert(cap(s.start+P[j][k][0],s.start+j) >= grade(s,s.height,E[j][k]), 'source parent cover');
    }
  }
  function pump(s,cut,q,count) {
    assert(count > 0 && auxCount(s) > 0 && q <= cut);
    const z = s.target.length, span = z-cut, delta = count*span;
    guard(z-1+(count+1)*span);
    s.target = expose(s.target,cut-1,nat(q),emit);
    fs(s,count+1);
    s.start += delta;
    for (const node of nodesOf(s)) if (node.anchor >= cut) node.anchor += delta;
    trim(s,z-1+delta);
    return {span,delta};
  }
  function ensure(s,d,a,allocations) {
    if (!a.length || !d || s.dicts[d].byEnd.has(key(a))) {grade(s,d,a); return;}
    let node = s.dicts[d].root;
    for (;;) {
      assert(cmp(node.base,a) < 0 && cmp(a,node.end) < 0);
      const child = node.children.find(c => cmp(a,c.end) <= 0);
      if (!child) break;
      node = child;
    }
    const base = node.children.at(-1)?.end ?? node.base;
    const difference = M.debug.ordRightDiff(base,a);
    assert.equal(difference.length,1,'one new exponent per dictionary level');
    const {exp,coeff:count} = difference[0];
    assert(cmp(exp,node.exp) < 0);
    ensure(s,d-1,exp,allocations);
    assert(!allocations.some(x => x.level === d),'at most one pump per level');
    const cut = node.anchor, q = resource(s,node), newResource = grade(s,d-1,exp)+1;
    assert(newResource <= q-1);
    const {span,delta} = pump(s,cut,q,count);
    let nextBase = base;
    for (let k = 0; k < count; k++) {
      const end = add(nextBase,power(exp));
      const child = {level:d,base:nextBase,end,exp,anchor:cut+k*span,children:[]};
      assert(!s.dicts[d].byEnd.has(key(end)));
      node.children.push(child); s.dicts[d].byEnd.set(key(end),child);
      nextBase = end; stats.newNodes++;
    }
    assert(eq(nextBase,a));
    allocations.push({level:d,cut,row:q,count,span,delta,newResource});
    stats.pumps++;
    check(s,false);
  }
  function checkSourceUnit(before,after,n) {
    const E=endpoints(before), En=endpoints(after), P=B.parents(before,before.map(B.column_verticals)),
      Pn=B.parents(after,after.map(B.column_verticals));
    const x=before.length-1, alpha=E[x].at(-1), cut=P[x].at(-1)[0], L=x-cut;
    const oldEnds=new Set(E.flat().map(key)), cells=new Map();
    for (const col of E.concat(En)) for (const a of col) cells.set(key(a),a);
    for (const col of En) for (const a of col) assert(oldEnds.has(key(a)));
    function query(ends,parents,col,a) {
      const i=ends[col].findIndex(b => cmp(b,a) >= 0); return i<0 ? null : parents[col][i][0];
    }
    for (let b=1;b<=n;b++) for (let j=cut;j<x;j++) for (const a of cells.values()) {
      const out=x+(b-1)*L+j-cut, from=j===cut&&cmp(a,alpha)<0?x:j,
        shift=j===cut&&cmp(a,alpha)<0?b-1:b, p=query(E,P,from,a),
        want=p===null?null:p<cut?p:p+shift*L;
      assert.equal(query(En,Pn,out,a),want,'native parent-copy law'); stats.parentChecks++;
    }
  }
  function initialize(height) {
    assert(Number.isSafeInteger(height) && height >= 0 && height <= 12);
    guard(3*height+6);
    let epsilonSource = B.infinity_FS(3);
    epsilonSource = sourceFS(epsilonSource,1);
    assert.equal(B.display(epsilonSource),'()(1^()(1,1))');
    const source = sourceFS(epsilonSource,height);
    assert(eq(rowOrdinal(source[1][0][1]),tower(height)));
    const top = M.debug.parseExpr('()(1:ω)'), seedIndex = 2*height+2;
    const s={source,height,seedIndex,seed:null,target:top,start:2*height+1,
      reserve:Math.max(1,height),dicts:[null],path:[],allocationLog:[]};
    for (let d=1;d<=height;d++) {
      const node={level:d,base:[],end:tower(d),exp:tower(d-1),anchor:2*d,children:[]};
      s.dicts.push({root:node,byEnd:new Map([[key(node.end),node]])});
    }
    fs(s,seedIndex); s.seed=s.target;
    fs(s,s.reserve);
    assert(M.compare(s.target,s.seed)<0,'proper descendant of the uniform height seed');
    check(s); stats.maxHeight=Math.max(stats.maxHeight,height);
    return s;
  }
  function initializeForSource(source,height) {
    // Local invariant audit only: build an actual STANDARD diagonal cover of
    // this finite source and all its current endpoints. This does not replace
    // initialize(height) in the uniform all-descendant theorem.
    assert(source.length && Number.isSafeInteger(height) && height>=0 && height<=12);
    const values=Array.from({length:height+1},()=>new Map());
    function collect(d,a) {
      if (!a.length) return;
      if (!d) {assert(eq(a,one));return;}
      if(values[d].has(key(a)))return;
      assert(cmp(a,tower(d))<=0);
      values[d].set(key(a),a);
      let prefix=[];
      for(const term of a) {
        collect(d-1,term.exp);
        guard(term.coeff);
        for(let k=0;k<term.coeff;k++) {
          prefix=add(prefix,power(term.exp));
          if(!eq(prefix,a))collect(d,prefix);
        }
      }
    }
    for(let d=1;d<=height;d++)collect(d,tower(d));
    for(const col of endpoints(source))for(const a of col)collect(height,a);
    let address=0;
    const dicts=[null];
    for(let d=1;d<=height;d++) {
      const sorted=[...values[d].values()].sort(cmp),children=[],byEnd=new Map();
      let base=[];
      for(const a of sorted.slice(0,-1)) {
        const diff=M.debug.ordRightDiff(base,a);
        assert(diff.length===1&&diff[0].coeff===1,'adjacent prefix-closed endpoints');
        address+=2;
        const node={level:d,base,end:a,exp:diff[0].exp,anchor:address,children:[]};
        children.push(node);byEnd.set(key(a),node);base=a;
      }
      address+=2;
      const root={level:d,base:[],end:tower(d),exp:tower(d-1),anchor:address,children};
      byEnd.set(key(root.end),root);dicts.push({root,byEnd});
    }
    const start=address+1,seedIndex=start+1;
    const s={source,height,start,seedIndex,seed:null,target:M.debug.parseExpr('()(1:ω)'),
      reserve:Math.max(1,height),dicts,path:[],allocationLog:[],localAuditInitialization:true};
    fs(s,seedIndex);s.seed=s.target;
    fs(s,source.length+s.reserve-2);
    assert(M.compare(s.target,s.seed)<0,'proper standard local-audit initialization');
    check(s);stats.maxHeight=Math.max(stats.maxHeight,height);return s;
  }
  function step(s,n) {
    check(s); if (!s.source.length) return s;
    const before=s.target, old=s.source, x=old.length-1, col=old.at(-1);
    const kind=!col.length?'delete':B.is_one(col.at(-1)[1])?'unit':'limit';
    const P=B.parents(old,old.map(B.column_verticals)), E=endpoints(old);
    if (kind==='unit') guard(x+n*(x-P[x].at(-1)[0]));
    const next=sourceFS(old,n), allocations=[];
    if (kind==='unit'&&n) checkSourceUnit(old,next,n);
    if (kind==='delete'||kind==='unit'&&!n) {
      s.source=next;
      trim(s,next.length?s.start+next.length-1+s.reserve:1);
      stats.deletions++;
    } else {
      const alpha=E[x].at(-1), parent=P[x].at(-1)[0];
      if (kind==='limit') {
        const En=endpoints(next), alphaNew=En[x].at(-1), oldHeight=rowOrdinal(col.at(-1)[1]);
        const prefix=col.length>1?E[x][col.length-2]:[];
        const expected=add(prefix,M.debug.ordFS(oldHeight,n+1));
        assert(eq(alphaNew,expected),'native one-row refinement matches epsilon-zero CNF');
        stats.labelChecks++;
        ensure(s,s.height,alphaNew,allocations);
        const Pn=B.parents(next,next.map(B.column_verticals));
        for (const p of Pn[x].slice(col.length-1)) assert.equal(p[0],parent);
        for (const a of En[x]) grade(s,s.height,a);
        assert(grade(s,s.height,alphaNew)<grade(s,s.height,alpha));
      }
      const predecessor=M.debug.ordFS(alpha,0);
      const q=kind==='unit'?grade(s,s.height,predecessor)+1:grade(s,s.height,alpha);
      assert(q<=grade(s,s.height,alpha));
      trim(s,s.start+x);
      s.target=expose(s.target,s.start+parent-1,nat(q),emit);
      const z=s.target.length,L=z-(s.start+parent);
      if (kind==='limit') {fs(s,Math.ceil((s.reserve+1)/L));trim(s,z+s.reserve);stats.limits++;}
      else {fs(s,n+Math.ceil(s.reserve/L));trim(s,s.start+next.length-1+s.reserve);stats.units++;}
      s.source=next;
    }
    assert(allocations.length<=s.height);
    assert(M.compare(s.target,before)<0,'strict real target descent');
    s.path.push(n);s.allocationLog.push(allocations);
    stats.sourceSteps++;stats.maxPumpsPerStep=Math.max(stats.maxPumpsPerStep,allocations.length);
    check(s);
    return s;
  }
  return {B,M,stats,initialize,initializeForSource,step,check,grade,resource,endpoints,nodesOf,rowOrdinal,
    sourceFS,cmp,eq,tower,auxCount,capacityTable,hashes:loader.hashes};
}

module.exports={makeCover};
