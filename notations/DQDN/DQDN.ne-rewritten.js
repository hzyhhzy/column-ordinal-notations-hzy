/* DQDN — Demand Query Diagram Notation.
 * Standalone NER port of typed_builder.py + dqdn.py, 2026-10-05.
 * Only descendants of the common TOP are admitted by the public interfaces.
 * Natural atoms are BigInt; pointers are bounded array indices. No eval/network.
 * The well-ordering argument is on paper, not machine-certified by this file.
 * UI revision 2: no preloaded 880-column example; a fresh NER tree ID.
 */
(() => {
  'use strict';
  const LIMITS = {milliseconds: 750, work: 2500000, nodes: 150000,
    columns: 50000, characters: 2000000, cacheBytes: 24000000};
  const now = () => typeof performance === 'undefined' ? Date.now() : performance.now();
  class ResourceLimit extends Error {
    constructor(message) { super('DQDN：' + message); this.name = 'ResourceLimit'; }
  }
  class BadConstruction extends Error {}
  const need = (test, message = '不适用的局部构造') => {
    if (!test) throw new BadConstruction(message);
  };
  class Budget {
    constructor() { this.deadline = now() + LIMITS.milliseconds; this.work = 0; this.next = 0; }
    tick(n = 1) {
      this.work += n;
      if (this.work > LIMITS.work) throw new ResourceLimit('超过单次工作量预算；没有截断数学结果。');
      if (this.work >= this.next) {
        this.next = this.work + 128;
        if (now() > this.deadline) throw new ResourceLimit('超过单次网页时间预算；不代表非法或不终止。');
      }
    }
    size(n) {
      this.tick();
      if (n > LIMITS.columns) throw new ResourceLimit('输入或输出列数超过网页保护上限。');
    }
  }
  function natural(n) {
    if (typeof n === 'number' && !Number.isSafeInteger(n))
      throw new SyntaxError('DQDN：不能舍入整数。');
    if (!['bigint', 'number', 'string'].includes(typeof n) || !/^\d+$/.test(String(n)))
      throw new SyntaxError('DQDN：需要非负整数。');
    return BigInt(n);
  }
  function index(n) {
    const b = natural(n);
    if (b > BigInt(Number.MAX_SAFE_INTEGER)) throw new ResourceLimit('下标超过可用数组索引。');
    return Number(b);
  }
  function fairChoice(i) {
    let n = natural(i) + 2n;
    while (!(n & 1n)) n >>= 1n;
    return n < 3n ? 0n : (n - 3n) / 2n;
  }
  const ATOM = {v: 1, n: 1, nil: 0, ks: 0, ke: 0, tn: 0, tx: 1, g: 1};
  const PTR = {l: 1, a: 2, s: 1, r: 3, q: 1, kk: 2, kc: 2, ct: 2,
    dl: 2, ta: 2, tf: 2, tl: 2, tt: 2, tp: 3, ep: 3, eq: 2,
    li: 2, bp: 2, bf: 2, al: 2, b: 3};
  const RULES = [
    ['kind_arrow', ['kind', 'kind']], ['kind_context', ['kctx', 'kind']],
    ['term_context', ['kctx']], ['extend_context', ['ctx', 'type']],
    ['lift_context', ['ctx', 'kind']], ['nat_type', ['kctx']],
    ['type_variable', ['kctx', 'number']], ['type_arrow', ['type', 'type']],
    ['type_forall', ['type']], ['type_lambda', ['type']],
    ['type_application', ['type', 'type']], ['weaken_type', ['type', 'kind']],
    ['variable', ['ctx', 'number']], ['number', ['ctx', 'number']],
    ['lambda', ['term']], ['application', ['term', 'term']],
    ['polymorphic', ['term']], ['instantiate', ['term', 'type']],
    ['successor', ['term']], ['query', ['term']], ['recursor', ['term', 'term', 'term']],
    ['type_of', ['term']], ['equality_refl', ['type']], ['equality_sym', ['equal']],
    ['equality_trans', ['equal', 'equal']], ['type_beta', ['type', 'number']],
    ['type_eta', ['type', 'number']], ['convert', ['term', 'equal']]
  ];
  const SORTS = {kind: ['ks', 'kk'], kctx: ['ke', 'kc'], ctx: ['ct'],
    type: ['tp'], term: ['ep'], equal: ['eq']};
  class Terms {
    constructor(budget = new Budget()) {
      this.budget = budget; this.data = []; this.ids = new Map();
      this.shifts = new Map(); this.substitutions = new Map();
      this.typeWalks = new Map(); this.kindHeights = new Map();
    }
    make(tag, ...args) {
      this.budget.tick();
      if (Object.hasOwn(ATOM, tag)) args = args.map(natural);
      const key = tag + ':' + args.join(',');
      if (!this.ids.has(key)) {
        if (this.data.length >= LIMITS.nodes) throw new ResourceLimit('单次图节点数超过保护上限。');
        this.ids.set(key, this.data.length); this.data.push([tag, ...args]);
      }
      return this.ids.get(key);
    }
    numeral(n) { return this.make('n', n); }
    children(n) { return Object.hasOwn(PTR, this.data[n][0]) ? this.data[n].slice(1) : []; }
    parts(n, tag = null) {
      this.budget.tick(); const [actual, ...args] = this.data[n];
      need(tag === null || tag === actual, '对象种类不匹配'); return args;
    }
    linked(n, tag, end = 'nil') {
      const result = [];
      while (this.data[n][0] !== end) { const [value, next] = this.parts(n, tag); result.push(value); n = next; }
      return result;
    }
    listOf(values, tag) {
      let result = this.make('nil');
      for (let i = values.length - 1; i >= 0; i--) result = this.make(tag, values[i], result);
      return result;
    }
    kindHeight(root) {
      const stack = [[root, false]];
      while (stack.length) {
        const [n, ready] = stack.pop(); if (this.kindHeights.has(n)) continue;
        this.budget.tick(); const [tag, ...args] = this.data[n];
        if (tag === 'ks') this.kindHeights.set(n, 0);
        else if (tag === 'kk' && !ready) { stack.push([n, true]); for (const x of args) stack.push([x, false]); }
        else if (tag === 'kk') this.kindHeights.set(n, 1 + Math.max(...args.map(x => this.kindHeights.get(x))));
        else throw new BadConstruction('不是 kind');
      }
      return this.kindHeights.get(root);
    }
    bindingWalk(root, parameter, depth = 0, substitute = false) {
      const cache = substitute ? this.substitutions : this.shifts;
      const keyOf = (n, d) => [n, parameter, d].join(',');
      const stack = [[root, depth, false]];
      while (stack.length) {
        const [n, d, ready] = stack.pop(), key = keyOf(n, d);
        if (cache.has(key)) continue;
        this.budget.tick(); const [tag, ...args] = this.data[n], children = this.children(n);
        let result;
        if (tag === 'v') {
          const k = args[0], bd = BigInt(d);
          if (substitute) result = k === bd ? this.bindingWalk(parameter, d) : this.make('v', k > bd ? k - 1n : k);
          else result = this.make('v', k >= bd ? k + BigInt(parameter) : k);
        } else if (!children.length) result = n;
        else if (!ready) {
          stack.push([n, d, true]);
          for (let i = children.length - 1; i >= 0; i--) stack.push([children[i], d + (tag === 'l'), false]);
          continue;
        } else result = this.make(tag, ...children.map(x => cache.get(keyOf(x, d + (tag === 'l')))));
        cache.set(key, result);
      }
      return cache.get(keyOf(root, depth));
    }
    substitute(body, argument) { return this.bindingWalk(body, argument, 0, true); }
    typeWalk(root, parameter, substitute = false, depth = 0) {
      const cache = this.typeWalks, keyOf = (n, d) => [n, parameter, +substitute, d].join(',');
      const stack = [[root, depth, false]];
      while (stack.length) {
        const [n, d, ready] = stack.pop(), key = keyOf(n, d);
        if (cache.has(key)) continue;
        this.budget.tick(); const [tag, ...args] = this.data[n]; let result;
        if (tag === 'tn') result = n;
        else if (tag === 'tx') {
          const k = args[0], bd = BigInt(d);
          if (substitute && k === bd) result = this.typeWalk(parameter, d);
          else if (substitute) result = this.make('tx', k > bd ? k - 1n : k);
          else {
            need(!(parameter < 0 && bd <= k && k < bd - BigInt(parameter)), '类型变量逃逸');
            result = this.make('tx', k >= bd ? k + BigInt(parameter) : k);
          }
        } else if (['ta', 'tt', 'tf', 'tl'].includes(tag)) {
          const binder = ['tf', 'tl'].includes(tag), children = binder ? [args[1]] : args;
          if (!ready) {
            stack.push([n, d, true]);
            for (let i = children.length - 1; i >= 0; i--) stack.push([children[i], d + binder, false]);
            continue;
          }
          const translated = children.map(x => cache.get(keyOf(x, d + binder)));
          result = binder ? this.make(tag, args[0], translated[0]) : this.make(tag, ...translated);
        } else throw new BadConstruction('不是类型语法');
        cache.set(key, result);
      }
      return cache.get(keyOf(root, depth));
    }
    typeStep(root, address, eta = false) {
      const directions = []; let a = natural(address) + 1n;
      while (a > 1n) { this.budget.tick(); directions.push(Number(a & 1n)); a >>= 1n; }
      let n = root; const path = [];
      for (const side of directions.reverse()) {
        const [tag, ...args] = this.data[n]; let slot;
        if (['tf', 'tl'].includes(tag)) { need(side === 0); slot = 1; }
        else { need(['ta', 'tt'].includes(tag)); slot = side; }
        path.push([n, slot]); n = args[slot];
      }
      const [tag, ...args] = this.data[n]; let result;
      if (eta) {
        need(tag === 'tl'); const [f, variable] = this.parts(args[1], 'tt');
        need(this.data[variable][0] === 'tx' && this.data[variable][1] === 0n);
        result = this.typeWalk(f, -1);
      } else {
        need(tag === 'tt'); const [, body] = this.parts(args[0], 'tl');
        result = this.typeWalk(body, args[1], true);
      }
      for (const [parent, slot] of path.reverse()) {
        const [tag, ...args] = this.data[parent]; args[slot] = result; result = this.make(tag, ...args);
      }
      return result;
    }
    construct(rule, args, level) {
      const nil = this.make('nil'), star = this.make('ks'), nat = this.make('tn');
      const tp = (d, k, v) => this.make('tp', d, k, v), ep = (c, t, v) => this.make('ep', c, t, v);
      const same = proofs => {
        const p = proofs.map(x => this.parts(x, 'ep')); need(p.every(x => x[0] === p[0][0])); return p;
      };
      if (rule === 'kind_arrow') {
        const k = this.make('kk', ...args); need(level > 0n && BigInt(this.kindHeight(k)) < level); return k;
      }
      if (rule === 'kind_context') { need(level > 0n); return this.make('kc', args[1], args[0]); }
      if (rule === 'term_context') return this.make('ct', args[0], nil);
      if (['extend_context', 'lift_context'].includes(rule)) {
        let [delta, declarations] = this.parts(args[0], 'ct');
        if (rule === 'extend_context') {
          const [d2, k, typ] = this.parts(args[1], 'tp'); need(delta === d2 && k === star);
          declarations = this.make('dl', typ, declarations);
        } else {
          need(level > 0n); delta = this.make('kc', args[1], delta);
          declarations = this.listOf(this.linked(declarations, 'dl').map(a => this.typeWalk(a, 1)), 'dl');
        }
        return this.make('ct', delta, declarations);
      }
      if (rule === 'nat_type') return tp(args[0], star, nat);
      if (rule === 'type_variable') {
        const kinds = this.linked(args[0], 'kc', 'ke'), i = this.parts(args[1], 'n')[0];
        need(i < BigInt(kinds.length)); return tp(args[0], kinds[Number(i)], this.make('tx', i));
      }
      if (['type_arrow', 'type_application'].includes(rule)) {
        const [d1, k1, a1] = this.parts(args[0], 'tp'), [d2, k2, a2] = this.parts(args[1], 'tp');
        need(d1 === d2);
        if (rule === 'type_arrow') { need(k1 === k2 && k2 === star); return tp(d1, star, this.make('ta', a1, a2)); }
        const [domain, codomain] = this.parts(k1, 'kk'); need(domain === k2);
        return tp(d1, codomain, this.make('tt', a1, a2));
      }
      if (['type_forall', 'type_lambda'].includes(rule)) {
        const [delta, kind, typ] = this.parts(args[0], 'tp'), [parameterKind, parent] = this.parts(delta, 'kc');
        if (rule === 'type_forall') { need(kind === star); return tp(parent, star, this.make('tf', parameterKind, typ)); }
        const resultKind = this.make('kk', parameterKind, kind);
        need(level > 0n && BigInt(this.kindHeight(resultKind)) < level);
        return tp(parent, resultKind, this.make('tl', parameterKind, typ));
      }
      if (rule === 'weaken_type') {
        need(level > 0n); const [delta, kind, typ] = this.parts(args[0], 'tp');
        return tp(this.make('kc', args[1], delta), kind, this.typeWalk(typ, 1));
      }
      if (['variable', 'number'].includes(rule)) {
        const [, declarations] = this.parts(args[0], 'ct'), value = this.parts(args[1], 'n')[0];
        if (rule === 'number') return ep(args[0], nat, args[1]);
        const types = this.linked(declarations, 'dl'); need(value < BigInt(types.length));
        return ep(args[0], types[Number(value)], this.make('v', value));
      }
      if (rule === 'lambda') {
        const [context, typ, value] = this.parts(args[0], 'ep'), [delta, declarations] = this.parts(context, 'ct');
        const [domain, parent] = this.parts(declarations, 'dl');
        return ep(this.make('ct', delta, parent), this.make('ta', domain, typ), this.make('l', value));
      }
      if (rule === 'application') {
        const [f, x] = same(args), [domain, codomain] = this.parts(f[1], 'ta'); need(domain === x[1]);
        return ep(f[0], codomain, this.make('a', f[2], x[2]));
      }
      if (rule === 'polymorphic') {
        const [context, typ, value] = this.parts(args[0], 'ep'), [delta, declarations] = this.parts(context, 'ct');
        const [kind, parent] = this.parts(delta, 'kc');
        const old = this.listOf(this.linked(declarations, 'dl').map(a => this.typeWalk(a, -1)), 'dl');
        return ep(this.make('ct', parent, old), this.make('tf', kind, typ), value);
      }
      if (rule === 'instantiate') {
        const [context, typ, value] = this.parts(args[0], 'ep'), [kind, body] = this.parts(typ, 'tf');
        const [delta, actualKind, argument] = this.parts(args[1], 'tp');
        need(delta === this.parts(context, 'ct')[0] && kind === actualKind);
        return ep(context, this.typeWalk(body, argument, true), value);
      }
      if (['successor', 'query'].includes(rule)) {
        const [context, typ, value] = this.parts(args[0], 'ep'); need(typ === nat);
        return ep(context, nat, this.make(rule === 'successor' ? 's' : 'q', value));
      }
      if (rule === 'recursor') {
        const [z, s, n] = same(args); need(n[1] === nat && s[1] === this.make('ta', nat, this.make('ta', z[1], z[1])));
        return ep(z[0], z[1], this.make('r', z[2], s[2], n[2]));
      }
      if (rule === 'type_of') { const [context, typ] = this.parts(args[0], 'ep'); return tp(this.parts(context, 'ct')[0], star, typ); }
      if (rule === 'equality_refl') return this.make('eq', args[0], args[0]);
      if (rule === 'equality_sym') { const [l, r] = this.parts(args[0], 'eq'); return this.make('eq', r, l); }
      if (rule === 'equality_trans') {
        const [l, m1] = this.parts(args[0], 'eq'), [m2, r] = this.parts(args[1], 'eq');
        need(m1 === m2); return this.make('eq', l, r);
      }
      if (['type_beta', 'type_eta'].includes(rule)) {
        const [d, k, typ] = this.parts(args[0], 'tp'), address = this.parts(args[1], 'n')[0];
        return this.make('eq', args[0], tp(d, k, this.typeStep(typ, address, rule === 'type_eta')));
      }
      if (rule === 'convert') {
        const [context, typ, value] = this.parts(args[0], 'ep'), [left, right] = this.parts(args[1], 'eq');
        const [d, k, source] = this.parts(left, 'tp'), [d2, k2, target] = this.parts(right, 'tp');
        need(d === d2 && d === this.parts(context, 'ct')[0] && k === k2 && k === star && typ === source);
        return ep(context, target, value);
      }
      throw new BadConstruction('未知局部规则');
    }
    initialLibrary() {
      const [nil, delta, star, nat] = ['nil', 'ke', 'ks', 'tn'].map(t => this.make(t));
      const context = this.make('ct', delta, nil);
      const entries = [star, delta, context, this.make('tp', delta, star, nat),
        this.make('ep', context, nat, this.numeral(0))];
      let result = nil;
      for (const entry of entries) result = this.make('li', entry, result);
      return result;
    }
    available(library, sort) {
      const stack = [library], seen = new Set(), result = [];
      while (stack.length) {
        const n = stack.pop(); if (seen.has(n)) continue;
        this.budget.tick(); seen.add(n);
        if (SORTS[sort].includes(this.data[n][0])) result.push(n);
        const children = this.children(n);
        for (let i = children.length - 1; i >= 0; i--) stack.push(children[i]);
      }
      return result;
    }
    builder(level, fuel, library, pending = null) {
      if (pending === null) pending = this.make('nil');
      return this.make('b', this.numeral(level), this.numeral(fuel), this.make('bf', library, pending));
    }
    builderChild(root, choice) {
      if (this.data[root][0] === 'g') return this.builder(this.data[root][1], choice, this.initialLibrary());
      const [levelNode, fuelNode, frame] = this.parts(root, 'b');
      const level = this.parts(levelNode, 'n')[0], fuel = this.parts(fuelNode, 'n')[0];
      let [library, pending] = this.parts(frame, 'bf');
      if (fuel === 0n) {
        for (const entry of this.linked(library, 'li')) {
          if (this.data[entry][0] !== 'ep') continue;
          const [context, typ, value] = this.parts(entry, 'ep'), [d, ds] = this.parts(context, 'ct');
          if (this.data[d][0] === 'ke' && this.data[ds][0] === 'nil' && this.data[typ][0] === 'tn') return value;
        }
        return this.numeral(0);
      }
      if (this.data[pending][0] === 'nil') pending = this.make('bp', this.numeral(choice % BigInt(RULES.length)), this.make('nil'));
      else {
        const [ruleNode, argumentsNode] = this.parts(pending, 'bp');
        const [rule, sorts] = RULES[Number(this.parts(ruleNode, 'n')[0])];
        const chosen = this.linked(argumentsNode, 'al').reverse();
        if (chosen.length < sorts.length) {
          const sort = sorts[chosen.length]; let argument;
          if (sort === 'number') argument = this.numeral(choice);
          else {
            const candidates = this.available(library, sort); if (!candidates.length) return this.numeral(0);
            argument = candidates[Number(choice % BigInt(candidates.length))];
          }
          pending = this.make('bp', ruleNode, this.make('al', argument, argumentsNode));
        } else {
          let entry;
          try { entry = this.construct(rule, chosen, level); }
          catch (error) { if (error instanceof BadConstruction) return this.numeral(0); throw error; }
          library = this.make('li', entry, library); pending = this.make('nil');
        }
      }
      return this.builder(level, fuel - 1n, library, pending);
    }
    demand(root) {
      if (['g', 'b'].includes(this.data[root][0])) return [root, []];
      let n = root; const path = [];
      while (true) {
        this.budget.tick(); const [tag, ...args] = this.data[n]; let side;
        if (tag === 'a') { if (this.data[args[0]][0] === 'l') return [n, path]; side = 0; }
        else if (['s', 'q', 'r'].includes(tag)) {
          side = tag === 'r' ? 2 : 0; if (this.data[args[side]][0] === 'n') return [n, path];
        } else return null;
        path.push([n, side]); n = args[side];
      }
    }
    reducible(root) { return this.demand(root) !== null; }
    computationChild(root, i) {
      const choice = fairChoice(i);
      if (['g', 'b'].includes(this.data[root][0])) return this.builderChild(root, choice);
      const selected = this.demand(root); if (selected === null) throw new Error('DQDN：源已停止。');
      const [n, path] = selected, [tag, ...args] = this.data[n]; let child;
      if (tag === 'a') child = this.substitute(this.data[args[0]][1], args[1]);
      else if (tag === 's') child = this.numeral(this.data[args[0]][1] + 1n);
      else if (tag === 'q') child = this.numeral(choice);
      else {
        const [z, step, number] = args, value = this.data[number][1];
        if (value === 0n) child = z;
        else {
          const prev = this.numeral(value - 1n), residual = this.make('r', z, step, prev);
          child = this.make('a', this.make('a', step, prev), residual);
        }
      }
      for (const [parent, side] of path.reverse()) {
        const [tag, ...args] = this.data[parent]; args[side] = child; child = this.make(tag, ...args);
      }
      return child;
    }
  }
  const TOP_COLUMNS = [['top']], isTop = a => a.length === 1 && a[0][0] === 'top';
  function root(k, budget) {
    budget.size(2 * (k + 1)); const result = [];
    for (let j = 0; j <= k; j++) { budget.tick(); result.push(['g', BigInt(j)], ['run', 2 * j]); }
    return result;
  }
  function decode(columns, t) {
    const roots = [];
    for (const [tag, ...args] of columns) {
      t.budget.tick();
      if (Object.hasOwn(ATOM, tag)) roots.push(t.make(tag, ...args));
      else if (tag === 'run') {
        if (!t.reducible(roots[args[0]])) throw new SyntaxError('DQDN：活动列指向已停止的源。');
        roots.push(null);
      } else roots.push(t.make(tag, ...args.map(x => roots[x])));
    }
    return roots;
  }
  function emit(root, columns, positions, t) {
    const stack = [[root, false]];
    while (stack.length) {
      const [n, ready] = stack.pop(); if (positions.has(n)) continue;
      t.budget.tick(); const [tag, ...args] = t.data[n], children = t.children(n);
      if (children.length && !ready) {
        stack.push([n, true]); for (let i = children.length - 1; i >= 0; i--) stack.push([children[i], false]); continue;
      }
      positions.set(n, columns.length); t.budget.size(columns.length + 1);
      columns.push([tag, ...(children.length ? children.map(x => positions.get(x)) : args)]);
    }
    return positions.get(root);
  }
  function expandColumns(columns, n, budget = new Budget(), stopAfterChild = null) {
    n = index(n);
    if (isTop(columns)) return n === 0 ? [] : root(n - 1, budget);
    if (!columns.length) return [];
    const result = columns.slice(0, -1);
    if (n === 0 || columns.at(-1)[0] !== 'run') return result;
    budget.size(result.length + 2 * n);
    const t = new Terms(budget), roots = decode(columns, t), source = roots[columns.at(-1)[1]], positions = new Map();
    for (let i = 0; i < roots.length - 1; i++) if (roots[i] !== null && !positions.has(roots[i])) positions.set(roots[i], i);
    const leaf = t.make('v', 0);
    for (let i = 0; i < n; i++) {
      if (!positions.has(leaf)) positions.set(leaf, result.length);
      budget.size(result.length + 1); result.push(['v', 0n]);
      const child = t.computationChild(source, i);
      if (t.reducible(child)) {
        const pointer = emit(child, result, positions, t); budget.size(result.length + 1); result.push(['run', pointer]);
      } else { budget.size(result.length + 1); result.push(['v', 0n]); }
      // Display reconstruction may stop at a whole child-block boundary.
      // Ordinary FS calls never supply this callback: their rules are unchanged.
      if (stopAfterChild && stopAfterChild(result, i)) break;
    }
    return result;
  }
  const countWord = a => isTop(a) ? '2' : a.map(c => c[0] === 'run' ? '2' : '1').join('');
  const serialize = a => isTop(a) ? 'TOP' : a.map(([tag, ...args]) =>
    '[' + (tag === 'run' ? '!' : tag) + (args.length ? ':' + args.join(',') : '') + ']').join('');
  const known = new Map(); let cacheBytes = 0;
  function remember(columns, budget) {
    budget.size(columns.length); const text = serialize(columns);
    if (text.length > LIMITS.characters) throw new ResourceLimit('完整表达式超过文本保护上限。');
    if (!known.has(text)) {
      const cost = text.length * 2 + columns.length * 128;
      while (known.size && (cacheBytes + cost > LIMITS.cacheBytes || known.size >= 128)) {
        const key = known.keys().next().value; cacheBytes -= known.get(key).cost; known.delete(key);
      }
      if (cost <= LIMITS.cacheBytes) {
        const frozen = Object.freeze(columns.map(c => Object.freeze(c.slice())));
        known.set(text, {columns: frozen, word: countWord(frozen), cost}); cacheBytes += cost;
      }
    }
    return text;
  }
  function fromCounts(word, budget = new Budget()) {
    if (!/^[12]*$/.test(word)) throw new SyntaxError('DQDN：计数列只能是 1 或 2。');
    budget.size(word.length);
    if (!word) return [];
    if (word === '2') return TOP_COLUMNS;
    let current = TOP_COLUMNS;
    for (let step = 0; step <= word.length + 1; step++) {
      budget.tick(); const actual = countWord(current); let common = 0;
      while (common < Math.min(actual.length, word.length) && actual[common] === word[common]) { budget.tick(); common++; }
      if (common === word.length) return current.slice(0, common);
      if (common === actual.length || actual[common] !== '2' || word[common] !== '1')
        throw new SyntaxError('DQDN：这不是从 TOP 可达的计数序列。');
      const n = isTop(current) ? Math.ceil(word.length / 2) : word.length - common;
      current = expandColumns(current.slice(0, common + 1), n, budget);
    }
    throw new Error('DQDN internal: count reconstruction did not advance');
  }
  function parseColumns(raw) {
    const compact = raw.replace(/\s+/g, ''), result = [];
    const matches = [...compact.matchAll(/\[([a-z]+|!)(?::(\d+(?:,\d+)*))?\]/g)];
    if (matches.map(m => m[0]).join('') !== compact) throw new SyntaxError('DQDN：列列表格式错误。');
    for (const m of matches) {
      const tag = m[1] === '!' ? 'run' : m[1], atoms = m[2] ? m[2].split(',') : [];
      const arity = tag === 'run' ? 1 : Object.hasOwn(ATOM, tag) ? ATOM[tag] : PTR[tag];
      if (arity === undefined || atoms.length !== arity) throw new SyntaxError('DQDN：未知列标签或参数个数错误。');
      const args = Object.hasOwn(ATOM, tag) ? atoms.map(natural) : atoms.map(index);
      if (!Object.hasOwn(ATOM, tag) && args.some(x => x >= result.length || result[x][0] === 'run'))
        throw new SyntaxError('DQDN：指针必须指向左侧数据列。');
      result.push([tag, ...args]);
    }
    return result;
  }
  function standard(text, budget = new Budget()) {
    if (typeof text !== 'string') throw new SyntaxError('DQDN：内部表达式应为列列表文本。');
    if (text.length > LIMITS.characters) throw new ResourceLimit('输入文本过长。');
    if (known.has(text)) return known.get(text).columns;
    if (text === 'TOP') { remember(TOP_COLUMNS, budget); return TOP_COLUMNS; }
    if (!text) { remember([], budget); return []; }
    const columns = parseColumns(text); budget.size(columns.length);
    const expected = fromCounts(countWord(columns), budget);
    if (serialize(expected) !== serialize(columns)) throw new SyntaxError('DQDN：此图从 TOP 不可达。');
    remember(columns, budget); return columns;
  }
  function FS(text, n) {
    const budget = new Budget(), columns = standard(text, budget);
    return remember(expandColumns(columns, n, budget), budget);
  }
  function parse(input) {
    const raw = String(input).trim(), budget = new Budget();
    if (raw.length > LIMITS.characters) throw new ResourceLimit('输入文本过长。');
    if (!raw || ['0', '∅', '[]'].includes(raw)) return remember([], budget);
    const path = raw.replace(/\s+/g, '');
    if (/^TOP(?:\[\d+\])*$/i.test(path) || /^Top of DQDN$/i.test(raw)) {
      let columns = TOP_COLUMNS;
      for (const m of path.matchAll(/\[(\d+)\]/g)) columns = expandColumns(columns, index(m[1]), budget);
      return remember(columns, budget);
    }
    let word;
    if (/^(?:\s*\[[12]\]\s*)+$/.test(raw)) word = raw.replace(/[\[\]\s]/g, '');
    else if (/^[12]+(?:\s*[,，\s]\s*[12]+)*$/.test(raw)) word = raw.replace(/[,，\s]/g, '');
    if (word !== undefined) return remember(fromCounts(word, budget), budget);
    const columns = standard(raw, budget); return remember(columns, budget);
  }
  function compare(a, b) {
    const budget = new Budget();
    const left = known.has(a) ? known.get(a).word : countWord(standard(a, budget));
    const right = known.has(b) ? known.get(b).word : countWord(standard(b, budget));
    return left === right ? 0 : left < right ? -1 : 1;
  }
  function sequenceText(s) { const w = countWord(standard(s)); return w ? w.split('').join(',') : '0'; }
  function listText(s) { return serialize(standard(s)) || '[]'; }
  function reconstructViews(s, budget = new Budget()) {
    const target = standard(s, budget), cached = known.get(s);
    if (cached && cached.minimalPath !== undefined && cached.growthView !== undefined)
      return {path: cached.minimalPath, growth: cached.growthView};
    const word = countWord(target), pieces = ['TOP']; let characters = 3;
    const growth = []; let current = TOP_COLUMNS;
    const append = (part, repeats = 1) => {
      budget.tick(repeats); characters += part.length * repeats;
      if (characters > LIMITS.characters) throw new ResourceLimit('最简操作序列超过文本保护上限。');
      if (repeats) pieces.push(part.repeat(repeats));
    };
    const deleteColumns = count => {
      append('[0]', count);
      if (growth.length) growth[growth.length - 1] -= count;
      else if (count && word) throw new Error('DQDN internal: leading deletion on a nonzero path');
    };
    // Every nonzero expansion fixes at least one new target column. Runs of
    // [0] are literal column deletion, so they can be recorded in one batch.
    for (let step = 0; step <= word.length + 1; step++) {
      budget.tick(); const actual = countWord(current); let common = 0;
      while (common < Math.min(actual.length, word.length) && actual[common] === word[common]) {
        budget.tick(); common++;
      }
      if (common === word.length) {
        deleteColumns(current.length - target.length);
        if (growth.some(n => n < 0)) throw new Error('DQDN internal: a merged growth group decreased length');
        const result = {path: pieces.join(''),
          growth: isTop(target) ? 'TOP' : !target.length ? '∅' : growth.join(',')};
        const entry = known.get(s), cost = 2 * (result.path.length + result.growth.length);
        if (entry && cacheBytes + cost <= LIMITS.cacheBytes) {
          entry.minimalPath = result.path; entry.growthView = result.growth;
          entry.cost += cost; cacheBytes += cost;
        }
        return result;
      }
      if (common === actual.length || actual[common] !== '2' || word[common] !== '1')
        throw new SyntaxError('DQDN：无法重建此式的标准操作序列。');
      deleteColumns(current.length - common - 1);
      current = current.slice(0, common + 1);
      if (isTop(current)) {
        // TOP[n]=(1,2)^n in the count view. Find the first sufficient root.
        let p = 0;
        while (p < word.length && word[p] === (p % 2 ? '2' : '1')) { budget.tick(); p++; }
        if (p < word.length && word[p] !== '1') throw new SyntaxError('DQDN：无可达的层根。');
        const n = Math.ceil((p < word.length ? p + 1 : word.length) / 2);
        append('[' + n + ']'); current = expandColumns(current, n, budget);
        growth.push(current.length - 1); // TOP itself has one column.
        continue;
      }
      // Child blocks are nonempty nested prefixes. Stream only as far as the
      // first block making A[n]>=target; this proves every smaller n fails.
      const bound = Math.ceil((word.length - common) / 2);
      let checked = common, selected = 0, reached = false;
      current = expandColumns(current, bound, budget, (columns, child) => {
        selected = child + 1;
        while (checked < Math.min(columns.length, word.length)) {
          budget.tick(); const digit = columns[checked][0] === 'run' ? '2' : '1';
          if (digit !== word[checked]) {
            if (digit < word[checked]) throw new SyntaxError('DQDN：目标不在当前基本列的下段。');
            reached = true; return true;
          }
          checked++;
        }
        reached = columns.length >= word.length;
        return reached;
      });
      if (!reached) throw new Error('DQDN internal: minimal path did not reach its prefix bound');
      append('[' + selected + ']');
      growth.push(current.length - common - 1);
    }
    throw new Error('DQDN internal: minimal path did not advance');
  }
  function minimalOperationText(s) { return reconstructViews(s).path; }
  function growthText(s) { return reconstructViews(s).growth; }
  function parseGrowth(input) {
    const raw = String(input).trim(), budget = new Budget();
    if (raw.length > LIMITS.characters) throw new ResourceLimit('增列序列输入过长。');
    if (/^TOP$/i.test(raw)) return remember(TOP_COLUMNS, budget);
    if (!raw || ['∅', '[]'].includes(raw)) return remember([], budget);
    if (!/^\d+(?:\s*[,，]\s*\d+)*$/.test(raw))
      throw new SyntaxError('DQDN：增列序列用逗号分隔非负整数；零式输入 ∅。');
    const values = raw.split(/[,，]/).map(value => index(value.trim()));
    if (values.length > LIMITS.columns + 1) throw new ResourceLimit('增列序列项数过多。');
    let current = TOP_COLUMNS;
    for (const delta of values) {
      budget.tick(); const length = current.length + delta; budget.size(length);
      if (isTop(current)) current = root(Math.ceil(length / 2) - 1, budget).slice(0, length);
      else {
        if (!current.length || current.at(-1)[0] !== 'run')
          throw new SyntaxError('DQDN：后继式之后不能继续接非负增列项。');
        const expanded = expandColumns(current, Math.ceil((delta + 1) / 2), budget,
          columns => columns.length >= length);
        if (expanded.length < length) throw new Error('DQDN internal: insufficient growth prefix');
        current = expanded.slice(0, length);
      }
    }
    return remember(current, budget);
  }
  const escapeHTML = text => text.replace(/[&<>"']/g, c => ({'&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;'}[c]));
  const html = fn => s => escapeHTML(fn(s));
  const OMEGA_OMEGA_PATH = [1,54,8,1,1,1,8,1,1,1,26,1,1,1,30,1,1,30,1,1,40,8,1,42,1,4,1,1,1];
  const notation = {
    // NER retains trees and saved analysis by ID when a script is reimported.
    // Keep the old ID's data intact, but do not reuse its oversized seed tree.
    id: 'dqdn-20261005-init-v2', name: 'DQDN', simple_name: 'DQDN',
    description: [
      '按需查询图列记号；只接受同一个 TOP 的有限展开后代。全段良序是当前纸面结论，尚未机器认证；没有把不良序的无类型裸图混入标准域。',
      '计数视图：数据列为 1，活动列为 2；在标准域内单射且按普通字典序比较。单个 2 是 TOP，1,2 是第 0 层边界 ε₀，不是 ω。',
      '所有 [0] 删末列。数据末列表示后继；活动末列展开为前 n 个孩子块，基本列满足前缀关系。三种基本列选项完全相同。',
      '输入支持计数串 112…、逗号序列、[1][2]、列列表，以及 TOP[1][2] 这样的实际展开路径。输入路径只是定位工具，不是原始表达式。',
      '最简操作序列视图从 TOP 重新推导路径：每一步都取仍能到达本式的最小下标；这不是操作步数最少，也不保留多余的输入历史。',
      '增列序列先合并最简路径中每个 [n] 及紧随的 [0]，再记录净增加的列数，用逗号分隔；TOP 算 1 列，TOP[1] 的首项为 1。零式显示 ∅，增列值 0 表示等长替换。',
      '列列表中 ! 是活动列；g 是层生成器；v/n 是变量/数字；l/a/s/r/q 是 λ/应用/后继/递归/查询。其余是类型、环境及生成器的小记录节点。',
      '冒号后的指针从 0 编号，指向左侧数据列；v、n、tx、g 后的数字是自然数原子而非指针。每一对 [] 恰是一列，完整显示，不折叠隐藏数据。',
      '原子整数用 BigInt，不舍入。约 750ms 单次保护；超限明确报错，不返回截断结果，也不把超限当作非良序或非法。',
      '界面修订 2：默认不载入 880 列示例，使用新的树缓存标识；数学规则不变。'
    ],
    display: {name: '计数序列', plain: sequenceText, html: html(sequenceText), from_display: parse},
    display_equiv: {
      '列列表': {plain: listText, html: html(listText), from_display: parse},
      '最简操作序列': {plain: minimalOperationText, html: html(minimalOperationText), from_display: parse},
      '增列序列': {plain: growthText, html: html(growthText), from_display: parseGrowth}
    },
    // The omega^omega example remains available by its manual path above.
    // Preloading it below TOP[1] forces NER to search to [54] (default cap: 10).
    init: () => ['TOP', 'TOP[2]', 'TOP[1]', 'TOP[1][1]', '1', '0'].map(parse),
    is_limit: s => { const a = standard(s); return isTop(a) || a.length > 0 && a.at(-1)[0] === 'run'; },
    compare, FS, FS_alter: FS, FS_short: FS,
    debug: {LIMITS, Budget, ResourceLimit, BadConstruction, Terms, RULES, ATOM, PTR,
      natural, fairChoice, root, decode, emit, expandColumns, countWord, serialize,
      fromCounts, parseColumns, standard, parse, minimalOperationText, growthText, parseGrowth, OMEGA_OMEGA_PATH,
      clearCache: () => { known.clear(); cacheBytes = 0; }, cacheSize: () => cacheBytes}
  };
  if (typeof register_notation === 'function') register_notation(notation);
  if (typeof module !== 'undefined' && module.exports) module.exports = notation;
})();
