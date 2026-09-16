/** Finite, acyclic self-indexed profile graphs. Candidate rules, not a WO theorem. */
export function createKernel(options = {}) {
  const limits = {ms: 700, work: 1200000, columns: 12000, size: 300000, depth: 48, text: 2000000, ...options};
  const started = Date.now(); let work = 0;
  function tick(force = false) {
    if (++work > limits.work || ((force || (work & 255) === 0) && Date.now() - started > limits.ms))
      throw Error('计算达到时间或操作预算；未返回截断项');
  }
  function natural(value) {
    if (typeof value === 'bigint' && value >= 0n && value <= BigInt(Number.MAX_SAFE_INTEGER)) value = Number(value);
    if (!Number.isSafeInteger(value) || value < 0) throw Error('地址和指标须为非负安全整数');
    return value;
  }
  const integers = new Map(), comparisons = new WeakMap(), expansions = new WeakMap();
  const zero = {columns: [], integer: 0, depth: 0, size: 0}; integers.set(0, zero);
  function integer(n) {
    natural(n); if (n > limits.columns) throw Error('有限数的列数超过预算');
    if (!integers.has(n)) integers.set(n, {columns: Array.from({length: n}, () => []), integer: n, depth: 0, size: n});
    return integers.get(n);
  }
  function compare(a, b) {
    tick(); if (a === b) return 0;
    if (a.integer !== null && b.integer !== null) return Math.sign(a.integer - b.integer);
    const found = comparisons.get(a)?.get(b); if (found !== undefined) return found;
    let result = 0;
    for (let j = 0; j < Math.min(a.columns.length, b.columns.length) && !result; j++) {
      const left = a.columns[j], right = b.columns[j];
      for (let r = 0; r < Math.min(left.length, right.length) && !result; r++)
        result = Math.sign(left[r].parent - right[r].parent) || compareProfiles(left[r].profile, right[r].profile);
      result ||= Math.sign(left.length - right.length);
    }
    result ||= Math.sign(a.columns.length - b.columns.length);
    if (!comparisons.has(a)) comparisons.set(a, new WeakMap());
    comparisons.get(a).set(b, result); return result;
  }
  function compareProfiles(a, b) {
    tick(); if (a.base !== b.base) return Math.sign(a.base - b.base);
    for (let i = 0; i < Math.min(a.cuts.length, b.cuts.length); i++) {
      const order = compare(a.cuts[i].at, b.cuts[i].at) || Math.sign(a.cuts[i].value - b.cuts[i].value);
      if (order) return order;
    }
    return Math.sign(a.cuts.length - b.cuts.length);
  }
  function profile(base, cuts = []) {
    natural(base); let previousValue = base, previousAt = null;
    const normalized = [];
    for (const {at, value} of cuts) {
      tick(); natural(value);
      if (!at || !Array.isArray(at.columns)) throw Error('列标须为同类有限表达式，不能是外顶端');
      if (!at.columns.length || (previousAt && compare(previousAt, at) <= 0)) throw Error('轮廓变点须严格递减且非零');
      if (value <= previousValue) throw Error('变点对应的地址须严格递增');
      normalized.push({at, value}); previousValue = value; previousAt = at;
    }
    return {base, cuts: normalized};
  }
  function fromWord(letters) {
    if (!letters.length) throw Error('有限轮廓词不能为空');
    for (let i = 0; i < letters.length; i++) {
      natural(letters[i]); if (i && letters[i] < letters[i - 1]) throw Error('轮廓词必须非降');
    }
    let first = 0;
    while (first + 1 < letters.length && letters[first] === letters[first + 1]) first++;
    const word = letters.slice(first), cuts = [];
    for (let i = 1; i < word.length; i++) if (word[i] !== word[i - 1])
      cuts.push({at: integer(word.length - i), value: word[i]});
    return profile(word[0], cuts);
  }
  const origin = p => p.cuts.at(-1)?.value ?? p.base;
  function renameProfile(p, move) {
    // Dimension expressions are closed terms: NEVER rename addresses inside them.
    return profile(move(p.base), p.cuts.map(c => ({at: c.at, value: move(c.value)})));
  }
  const lift = (p, old, child) => renameProfile(p, address => address === old ? child : address);
  function skyline(rows) {
    const largest = new Map();
    for (const row of rows) {
      tick(); const old = largest.get(row.parent);
      if (!old || compareProfiles(old.profile, row.profile) < 0) largest.set(row.parent, row);
    }
    const result = [];
    for (const row of [...largest.values()].sort((a, b) => b.parent - a.parent))
      if (!result.length || compareProfiles(result.at(-1).profile, row.profile) < 0) result.push(row);
    return result;
  }
  function term(columns) {
    if (columns.length > limits.columns) throw Error('完整输出列数超过预算');
    let depth = 0, size = columns.length, isInteger = true;
    for (let child = 0; child < columns.length; child++) {
      tick(); let previousParent = child, previousProfile = null;
      for (const row of columns[child]) {
        isInteger = false; natural(row.parent); const p = row.profile;
        if (row.parent >= previousParent || p.base > row.parent) throw Error('父地址/根地址无效');
        if (previousProfile && compareProfiles(previousProfile, p) >= 0) throw Error('列内不满足 skyline 正规性');
        for (const cut of p.cuts) {
          tick();
          if (cut.value > row.parent && cut.value !== child) throw Error('轮廓只能引用 ROOT 或当前列地址');
          depth = Math.max(depth, cut.at.depth + 1); size += cut.at.size + 2;
        }
        size += 2; previousParent = row.parent; previousProfile = p;
        if (depth > limits.depth || size > limits.size) throw Error('完整嵌套结构超过深度或大小预算');
      }
    }
    return isInteger ? integer(columns.length) : {columns, integer: null, depth, size};
  }
  const isLimit = g => !!g.columns.at(-1)?.length;
  function lowered(p, parent, block) {
    const q = origin(p), d = p.cuts.at(-1)?.at;
    if (!d || !(p.base <= parent && parent < q)) throw Error('降低轮廓的起源约束不成立');
    // Skip the deletion-only zeroth item of a limit label.  Using block here
    // traps every positive expansion of T3 below T2.
    const delta = fs(d, isLimit(d) ? block + 1 : 0);
    if (compare(delta, d) >= 0) throw Error('子列标降低失败；不返回伪展开');
    const base = Math.min(p.base, parent), cuts = []; let last = base;
    for (const cut of p.cuts) {
      const value = Math.min(cut.value, parent);
      if (value > last) { cuts.push({at: cut.at, value}); last = value; }
    }
    if (delta.columns.length) cuts.push({at: delta, value: q});
    return profile(base, cuts);
  }
  function belowOrigin(g, p, block) {
    let previous = null;
    for (const row of g.columns[origin(p)]) {
      if (compareProfiles(row.profile, p) < 0) previous = row.profile;
      else {
        const lower = lowered(p, row.parent, block);
        return previous && compareProfiles(previous, lower) > 0 ? previous : lower;
      }
    }
    return previous;
  }
  function minusColumn(g, block) {
    const child = g.columns.length - 1, column = g.columns[child], control = column.at(-1);
    const lower = belowOrigin(g, control.profile, block), rows = column.slice(0, -1);
    if (lower) rows.push({parent: control.parent, profile: lift(lower, origin(control.profile), child)});
    for (const row of g.columns[control.parent])
      rows.push({parent: row.parent, profile: lift(row.profile, control.parent, child)});
    return skyline(rows);
  }
  function fs(g, index) {
    tick(); natural(index);
    if (!g.columns.length) return g;
    const old = expansions.get(g)?.get(index); if (old) return old;
    const child = g.columns.length - 1;
    if (!index || !isLimit(g)) return term(g.columns.slice(0, child));
    const cut = g.columns[child].at(-1).parent, width = child - cut;
    if (index > Math.floor((limits.columns - child) / width)) throw Error('完整输出列数超过预算');
    const result = g.columns.slice(0, child); let size = result.length;
    const moved = (column, block) => {
      const move = address => address < cut ? address : address + block * width;
      return column.map(row => ({parent: move(row.parent), profile: renameProfile(row.profile, move)}));
    };
    function append(column) {
      tick(); size++;
      for (const row of column) size += 2 + row.profile.cuts.reduce((sum, c) => sum + c.at.size + 2, 0);
      if (size > limits.size) throw Error('完整嵌套结构超过大小预算');
      result.push(column);
    }
    for (let block = 0; block < index; block++) {
      append(moved(minusColumn(g, block), block));
      for (let k = cut + 1; k < child; k++) append(moved(g.columns[k], block + 1));
    }
    const output = term(result);
    if (!expansions.has(g)) expansions.set(g, new Map());
    expansions.get(g).set(index, output); return output;
  }
  function seed(d) {
    if (!d.columns.length) throw Error('S(D) 的种子列标须非零');
    return term([[], [{parent: 0, profile: profile(0, [{at: d, value: 1}])}]]);
  }
  function tower(n) {
    natural(n); if (n > limits.depth) throw Error('种子嵌套深度超过预算');
    let g = integer(1); for (let i = 0; i < n; i++) { tick(); g = seed(g); } return g;
  }
  function polynomial(exponents) {
    const columns = []; let previous = Infinity;
    for (const exponent of exponents) {
      natural(exponent); if (exponent > previous) throw Error('多项式指数须非增');
      if (columns.length + exponent + 1 > limits.columns) throw Error('多项式列数超过预算');
      const base = columns.length; columns.push([]);
      for (let i = 0; i < exponent; i++) columns.push([{parent: base, profile: profile(base)}]);
      previous = exponent;
    }
    return term(columns);
  }
  function omegaOmega() { return term([[], [{parent: 0, profile: profile(0)}], [{parent: 1, profile: profile(0)}]]); }
  function decodePolynomial(g) {
    const powers = []; let previous = Infinity, i = 0;
    while (i < g.columns.length) {
      tick(); const start = i; if (g.columns[i].length) return null; i++;
      while (i < g.columns.length && g.columns[i].length) {
        const c = g.columns[i];
        if (c.length !== 1 || c[0].parent !== start || c[0].profile.base !== start || c[0].profile.cuts.length) return null;
        i++;
      }
      const exponent = i - start - 1; if (exponent > previous) return null;
      powers.push(exponent); previous = exponent;
    }
    return powers;
  }
  function write(g) {
    const out = []; let count = 0;
    const emit = s => { tick(); count += s.length; if (count > limits.text) throw Error('完整列表超过字符预算；未省略或缩写重复项'); out.push(s); };
    function label(d) { if (d.integer !== null) emit(String(d.integer)); else { emit('{'); graph(d); emit('}'); } }
    function graph(a) {
      if (!a.columns.length) { emit('0'); return; }
      for (const c of a.columns) {
        emit('[');
        c.forEach((row, r) => {
          if (r) emit(';'); emit(row.parent + ':(' + row.profile.base);
          const cuts = row.profile.cuts;
          if (cuts.every(cut => cut.at.integer !== null)) {
            for (let i = 0; i < cuts.length; i++) {
              const n = cuts[i].at.integer - (cuts[i + 1]?.at.integer ?? 0), text = ',' + cuts[i].value;
              if (text.length * n + count > limits.text) throw Error('完整逐项轮廓超过字符预算');
              emit(text.repeat(n));
            }
          } else if (cuts.length) {
            emit('|'); cuts.forEach((cut, i) => { if (i) emit(','); label(cut.at); emit(':' + cut.value); });
          }
          emit(')');
        });
        emit(']');
      }
    }
    graph(g); return out.join('');
  }
  function read(raw, allowTop = true) {
    if (String(raw).length > limits.text) throw Error('输入字符超过预算');
    const text = String(raw).replace(/\s+/g, ''); let pos = 0, level = 0, path = 0;
    const peek = () => text[pos];
    function expect(ch) { if (text[pos++] !== ch) throw Error('输入格式错误：此处需要 ' + ch); }
    function number() {
      const start = pos; while (/\d/.test(text[pos] ?? '') && pos < text.length) pos++;
      if (start === pos) throw Error('此处需要非负整数'); return natural(Number(text.slice(start, pos)));
    }
    function label() {
      if (peek() !== '{') return integer(number());
      expect('{'); const d = expression(false); expect('}'); return d;
    }
    function readProfile(child) {
      const base = number();
      if (peek() === '|') {
        pos++; const cuts = [];
        do { const at = label(); expect(':'); cuts.push({at, value: number()}); if (peek() !== ',') break; pos++; } while (true);
        return profile(base, cuts);
      }
      const letters = [base];
      while (peek() === ',') { pos++; if (peek() === '*') { pos++; letters.push(child); } else letters.push(number()); }
      return fromWord(letters);
    }
    function columns() {
      const result = [];
      while (peek() === '[' && !/^\[\d+\]/.test(text.slice(pos, pos + 22))) {
        tick(); if (result.length >= limits.columns) throw Error('输入列数超过预算');
        expect('['); const c = [];
        if (peek() !== ']') do {
          const parent = number(); expect(':'); expect('('); const p = readProfile(result.length); expect(')');
          c.push({parent, profile: p}); if (peek() !== ';') break; pos++;
        } while (true);
        expect(']'); result.push(c);
      }
      if (!result.length) throw Error('此处需要完整列列表'); return term(result);
    }
    function expression(topAllowed) {
      tick(); if (++level > limits.depth + 4) throw Error('输入嵌套过深'); let g;
      if (peek() === '[') g = columns();
      else if (/\d/.test(peek() ?? '')) g = integer(number());
      else {
        const alias = /^(?:Limit(?:ofΩ-CWY2?)?|Top|∞|T\d+|WW|W\d*)/i.exec(text.slice(pos));
        if (!alias) throw Error('请输入 T2、Top、W2 或完整列列表');
        pos += alias[0].length; const name = alias[0].toUpperCase();
        if (name.startsWith('T') && name !== 'TOP') g = tower(natural(Number(name.slice(1))));
        else if (name === 'WW') g = omegaOmega();
        else if (name.startsWith('W')) g = polynomial([name === 'W' ? 1 : natural(Number(name.slice(1)))]);
        else { if (!topAllowed) throw Error('外顶端不能用作有限列标'); g = 'Limit'; }
      }
      while (/^\[\d+\]/.test(text.slice(pos, pos + 22))) {
        if (++path > 256) throw Error('展开路径超过预算'); expect('['); const n = number(); expect(']');
        g = g === 'Limit' ? tower(n) : fs(g, n);
      }
      level--; return g;
    }
    const result = expression(allowTop);
    if (pos !== text.length) throw Error('存在未识别的输入；重复地址须逐项书写'); tick(true); return result;
  }
  return {limits, tick, natural, zero, integer, compare, compareProfiles, profile, fromWord, origin, skyline,
    term, fs, seed, tower, isLimit, polynomial, omegaOmega, decodePolynomial, write, read, minusColumn};
}
