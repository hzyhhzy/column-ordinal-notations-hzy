/* Ω-CWY — self-indexed candidate. No well-ordering theorem claimed.
 * Full finite lists; diagrams are profile layers, not reconstructed wY geometry. */
"use strict";
(() => {
const {createKernel} = (() => {
/** Finite, acyclic self-indexed profile graphs. Candidate rules, not a WO theorem. */
function createKernel(options = {}) {
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

return {createKernel};
})();
const {escape,mountain,unavailable,withCounts,svg} = (() => {
/** Full profile-layer diagrams, not a claimed reconstruction of wY mountains. */
const escape = text => String(text).replace(/[&<>"']/g, c => ({'&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;'}[c]));
function polynomialText(powers) {
  if (!powers.length) return '0';
  const parts = [], superscript = n => String(n).replace(/\d/g, d => '⁰¹²³⁴⁵⁶⁷⁸⁹'[Number(d)]);
  for (let i = 0; i < powers.length;) {
    const exponent = powers[i]; let next = i + 1;
    while (next < powers.length && powers[next] === exponent) next++;
    const coefficient = next - i;
    parts.push(exponent === 0 ? String(coefficient) : (exponent === 1 ? 'ω' : 'ω' + superscript(exponent)) +
      (coefficient === 1 ? '' : '·' + coefficient));
    i = next;
  }
  return parts.join('+');
}
/** CNF = list of (nonincreasing) CNFs for its exponents, without coefficients.
 * Thus [] = 0, [[]] = 1, [[[]]] = omega. All routines avoid JS recursion.
 */
function compareCantor(a, b, tick = () => {}) {
  const stack = [{a, b, i: 0}];
  while (stack.length) {
    tick(); const frame = stack.at(-1);
    if (frame.a === frame.b) { stack.pop(); continue; }
    if (frame.i === Math.min(frame.a.length, frame.b.length)) {
      if (frame.a.length !== frame.b.length) return Math.sign(frame.a.length - frame.b.length);
      stack.pop(); continue;
    }
    const i = frame.i++; stack.push({a: frame.a[i], b: frame.b[i], i: 0});
  }
  return 0;
}
function decodeCantor(g, K) {
  // A CNF monomial is a preorder rooted tree. Its root column is empty;
  // every descendant has one constant profile pointing to that outer root.
  // The parent pointer describes the hereditary exponent tree, not a height.
  const children = [], roots = [], ancestors = []; let root = -1;
  for (let j = 0; j < g.columns.length; j++) {
    K.tick(); const column = g.columns[j]; children.push([]);
    if (!column.length) {
      root = j; roots.push(j); ancestors.length = 0; ancestors.push(j); continue;
    }
    if (column.length !== 1) return null;
    const {parent, profile} = column[0];
    if (profile.cuts.length || profile.base !== root) return null;
    while (ancestors.length && ancestors.at(-1) !== parent) { K.tick(); ancestors.pop(); }
    if (!ancestors.length) return null; // Not a preorder tree; do not guess a CNF.
    children[parent].push(j); ancestors.push(j);
  }
  const exponents = Array(g.columns.length);
  const nonincreasing = terms => {
    for (let i = 1; i < terms.length; i++)
      if (compareCantor(terms[i - 1], terms[i], K.tick) < 0) return false;
    return true;
  };
  for (let j = children.length - 1; j >= 0; j--) {
    K.tick(); const exponent = children[j].map(child => exponents[child]);
    if (!nonincreasing(exponent)) return null;
    exponents[j] = exponent;
  }
  const cnf = roots.map(j => exponents[j]);
  return nonincreasing(cnf) ? cnf : null;
}
function cantorText(cnf, options = {}) {
  const tick = options.tick ?? (() => {}), limit = options.maxChars ?? 16384;
  const superscript = n => String(n).replace(/\d/g, d => '⁰¹²³⁴⁵⁶⁷⁸⁹'[Number(d)]);
  const result = [], stack = [cnf]; let length = 0;
  while (stack.length) {
    tick(); const item = stack.pop();
    if (typeof item === 'string') {
      length += item.length; if (length > limit) throw Error('完整层标文本超过绘图预算；未截断层标');
      result.push(item); continue;
    }
    if (!item.length) { stack.push('0'); continue; }
    const tokens = [];
    for (let i = 0; i < item.length;) {
      tick(); const exponent = item[i]; let end = i + 1;
      while (end < item.length && compareCantor(exponent, item[end], tick) === 0) end++;
      const coefficient = end - i;
      if (i) tokens.push('+');
      if (!exponent.length) tokens.push(String(coefficient));
      else {
        tokens.push('ω');
        if (exponent.length !== 1 || exponent[0].length) {
          if (exponent.every(term => !term.length)) tokens.push(superscript(exponent.length));
          else if (exponent.length === 1 && exponent[0].length === 1 && !exponent[0][0].length) tokens.push('^ω');
          else tokens.push('^(', exponent, ')');
        }
        if (coefficient > 1) tokens.push('·' + coefficient);
      }
      i = end;
    }
    for (let i = tokens.length - 1; i >= 0; i--) stack.push(tokens[i]);
  }
  return result.join('');
}
function unavailable(reason) {
  return {width: 620, height: 44, elements: [], extra_text: [
    {text: '完整图暂不可显示：' + reason, x: 8, y: 20, size: 12, color: {type: 'text'}, align: 'left'}],
    _omegaCWY2: {complete: false, reason}};
}
function mountain(g, K, settings = {}) {
  if (g === 'Limit') return unavailable('外顶端没有有限列图');
  if (!g.columns.length) return {width: 64, height: 40, elements: [],
    extra_text: [{text: '0', x: 25, y: 20, size: 14}], _omegaCWY2: {complete: true, columns: 0, profiles: 0, nodes: 0}};
  const cap = {columns: 160, layers: 96, nodes: 2400, label: 16384,
    totalLabel: 65536, dimension: 16000, area: 16000000};
  if (g.columns.length > cap.columns) return unavailable('列数超过绘图预算；未绘制局部图');
  // Canonical literals identify equal closed terms even after a cold reload.
  // Sorting uses the notation comparator, NEVER the displayed label text.
  const levels = new Map([['0', {at: K.zero, raw: '0', label: '0'}]]), keys = new Map();
  let profiles = 0, nodes = g.columns.length, labelCharacters = 1;
  for (const column of g.columns) for (const row of column) {
    K.tick(); profiles++; nodes += 1 + row.profile.cuts.length;
    if (nodes > cap.nodes) return unavailable('完整节点数超过绘图预算；未截取部分层');
    for (const cut of row.profile.cuts) {
      let raw = keys.get(cut.at);
      if (raw === undefined) {
        raw = K.write(cut.at); keys.set(cut.at, raw);
        if (!levels.has(raw)) {
          if (levels.size >= cap.layers) return unavailable('完整层数超过绘图预算；未截取部分层');
          const cnf = decodeCantor(cut.at, K);
          const label = cnf !== null ? cantorText(cnf, {tick: K.tick, maxChars: cap.label}) : raw;
          labelCharacters += label.length;
          if (label.length > cap.label || labelCharacters > cap.totalLabel)
            return unavailable('完整层标文本超过绘图预算；未省略或截断层标');
          levels.set(raw, {at: cut.at, raw, label});
        }
      }
    }
  }
  const sorted = [...levels.values()].sort((a, b) => K.compare(a.at, b.at));
  const labels = sorted.map(level => level.label);
  const lookup = new Map(sorted.map((level, i) => [level.raw, i]));
  // Wrap whole literals without ellipses. Taller label bands reserve their full
  // space before any nodes/edges are laid out, including in the inverted view.
  const lineHeight = 16, lines = labels.map(label => label.match(/.{1,40}/gu));
  const bands = lines.map(parts => Math.max(36, parts.length * lineHeight + 12));
  const offsets = [0];
  for (let i = 1; i < bands.length; i++) offsets.push(offsets[i - 1] + (bands[i - 1] + bands[i]) / 2);
  const lane = Math.max(28, 8 * String(g.columns.length - 1).length + 10);
  const left = Math.max(42, ...lines.flat().map(s => 18 + s.length * 8));
  const top = 20, anchorGap = 44, invert = !!settings.invert_vertical;
  const originY = invert ? top + anchorGap : top + bands.at(-1) / 2 + offsets.at(-1);
  const layerY = i => originY + (invert ? offsets[i] : -offsets[i]);
  const anchorY = originY + (invert ? -anchorGap : anchorGap);
  const height = invert ? layerY(sorted.length - 1) + bands.at(-1) / 2 + top : anchorY + top;
  const centers = []; let cursor = left;
  const requestedWidth = Number.isFinite(settings.column_width) ? Math.max(34, Math.min(100, settings.column_width)) : 42;
  for (const c of g.columns) {
    const width = Math.max(requestedWidth, c.length * lane + 14);
    centers.push(cursor + width / 2); cursor += width;
  }
  const width = cursor + 12;
  if (width > cap.dimension || height > cap.dimension || width * height > cap.area)
    return unavailable('完整图尺寸超过绘图预算；未裁切任何列或层');
  const elements = [], circles = [], extra_text = [];
  const text = {type: 'text'}, gray = {type: 'gray'}, red = {type: 'red'}, background = {type: 'background'};
  function line(x1, y1, x2, y2, color = text, thickness = 1) {
    elements.push({type: 'line', x1, y1, x2, y2, stroke: true, stroke_color: color, width: thickness});
  }
  function point(x, y, value, color = text) {
    const label = String(value), r = Math.max(9, 4 * label.length + 3);
    circles.push({type: 'circle', x, y, r, stroke: true, stroke_color: color, fill: true, fill_color: background, width: 1});
    extra_text.push({text: label, x, y: y + 0.5, size: 12, color, align: 'center'});
  }
  for (let i = 0; i < sorted.length; i++) {
    const y = layerY(i); line(left - 6, y, width - 8, y, gray, 0.7);
    lines[i].forEach((part, lineIndex) => extra_text.push({text: part, x: left - 14,
      y: y + (lineIndex - (lines[i].length - 1) / 2) * lineHeight, size: 13, color: text, align: 'right'}));
  }
  for (let child = 0; child < g.columns.length; child++) {
    K.tick(); const column = g.columns[child]; point(centers[child], anchorY, child, red);
    for (let r = 0; r < column.length; r++) {
      const row = column[r], x = centers[child] + (r - (column.length - 1) / 2) * lane;
      // This slanted edge records the actual parent COLUMN, not an invented parent cap.
      line(x, originY + (invert ? -10 : 10), centers[row.parent], anchorY, text, 1.1);
      point(x, originY, K.origin(row.profile));
      let previous = originY;
      for (let k = row.profile.cuts.length - 1; k >= 0; k--) {
        const cut = row.profile.cuts[k], y = layerY(lookup.get(keys.get(cut.at)));
        line(x, previous, x, y); previous = y;
        point(x, y, k ? row.profile.cuts[k - 1].value : row.profile.base);
      }
    }
  }
  elements.push(...circles);
  K.tick(true);
  return {width, height, elements, extra_text, _omegaCWY2: {
    complete: true, kind: 'profile-layers', columns: g.columns.length, profiles, nodes,
    layers: labels, layerExpressions: sorted.map(level => level.raw), labelLines: lines,
    layerCenters: sorted.map((_, i) => layerY(i)), allChangesShown: true, invert_vertical: invert,
  }};
}
function withCounts(diagram, counts) {
  if (!diagram._omegaCWY2.complete) return diagram;
  // Separate footer, not a relabelling of the natural-number parent addresses.
  const tokens = counts.text.match(/[^,]+,?/g) ?? ['?'];
  const width = Math.max(diagram.width, 24 + Math.max(...tokens.map(s => s.length)) * 8);
  const characters = Math.max(1, Math.floor((width - 24) / 8)), lines = []; let current = '';
  for (const token of tokens) {
    if (current && current.length + token.length > characters) { lines.push(current); current = ''; }
    current += token;
  }
  if (current) lines.push(current);
  const height = diagram.height + 12 + lines.length * 16;
  if (width > 16000 || height > 16000 || width * height > 16000000)
    return unavailable('包含完整计数行的图超过尺寸预算；未裁切图形');
  return {...diagram, width, height, extra_text: [...diagram.extra_text,
    ...lines.map((line, i) => ({text: line, x: 12, y: diagram.height + 12 + i * 16,
      size: 13, color: {type: 'text'}, align: 'left'}))],
    _omegaCWY2: {...diagram._omegaCWY2, countSequence: counts.text, countsComplete: counts.complete,
      countLines: lines, countFooterTop: diagram.height}};
}
function svg(diagram, staticColors = false) {
  const palette = staticColors ? {text: '#202734', gray: '#c8cdd4', red: '#c53e46', background: '#fff'} :
    {text: 'var(--color-text,currentColor)', gray: 'var(--color-border-light,#c8cdd4)',
      red: 'var(--color-danger,#c53e46)', background: 'var(--color-bg,#fff)'};
  const color = spec => palette[spec?.type ?? 'text'] ?? palette.text;
  const parts = [`<svg xmlns="http://www.w3.org/2000/svg" width="${diagram.width}" height="${diagram.height}" viewBox="0 0 ${diagram.width} ${diagram.height}" role="img" aria-label="完整轮廓山脉图" style="font-family:inherit;vertical-align:middle">`];
  for (const e of diagram.elements) {
    if (e.type === 'line') parts.push(`<line x1="${e.x1}" y1="${e.y1}" x2="${e.x2}" y2="${e.y2}" stroke="${color(e.stroke_color)}" stroke-width="${e.width ?? 1}"/>`);
    else if (e.type === 'circle') parts.push(`<circle cx="${e.x}" cy="${e.y}" r="${e.r}" fill="${color(e.fill_color)}" stroke="${color(e.stroke_color)}" stroke-width="${e.width ?? 1}"/>`);
  }
  for (const t of diagram.extra_text) parts.push(`<text x="${t.x}" y="${t.y}" font-size="${t.size ?? 12}" fill="${color(t.color)}" text-anchor="${t.align === 'left' ? 'start' : t.align === 'right' ? 'end' : 'middle'}" dominant-baseline="central">${escape(t.text)}</text>`);
  parts.push('</svg>'); return parts.join('');
}

return {escape,polynomialText,compareCantor,decodeCantor,cantorText,unavailable,mountain,withCounts,svg};
})();
const {countSequence} = (() => {
/** Exact local column counts; bounded evaluation, never a guessed approximation. */
function countSequence(g, K, options = {}) {
  if (g === 'Limit') return {text: 'Limit of Ω-CWY', complete: true, values: null};
  if (!g.columns.length) return {text: '0', complete: true, values: []};
  const now = options.now ?? Date.now, started = now();
  const maxSteps = options.steps ?? 30000, milliseconds = options.ms ?? 450;
  let steps = 0; const values = Array(g.columns.length).fill(null);
  const asText = () => values.map(value => value === null ? '?' : String(value)).join(',');
  const checkTime = () => {
    if (now() - started >= milliseconds) throw Error('计数计算达到时间预算，不是整数溢出');
  };
  for (let child = 0; child < g.columns.length; child++) {
    try {
      checkTime(); K.tick(true);
      let current = K.term(g.columns.slice(0, child + 1)), count = 1n;
      while (current.columns.at(-1).length) {
        checkTime();
        if (steps >= maxSteps) throw Error('计数计算达到步数预算，不是整数溢出');
        steps++; K.tick();
        // The first retained replacement is D_0 for every positive FS index.
        const lowered = K.minusColumn(current, 0);
        const next = K.term([...current.columns.slice(0, -1), lowered]);
        if (K.compare(next, current) >= 0) throw Error('计数下降检查失败');
        current = next; count++;
      }
      values[child] = count;
    } catch (error) {
      // Never display the unfinished column's running total as its value.
      // Also preserve the prefix if the nested kernel reaches its own budget.
      return {text: asText(), complete: false, values, steps, completedColumns: child,
        reason: error instanceof Error ? error.message : String(error)};
    }
  }
  return {text: asText(), complete: true, values, steps, completedColumns: values.length};
}

return {countSequence};
})();

const NAME = 'Ω-CWY', TOP = 'Limit', cache = new Map(); let cacheSize = 0;
let lastCount = null;
function operation(fn) { const K = createKernel(); const result = fn(K); K.tick(true); return result; }
function parse(raw, K) {
  const text = String(raw); if (text.length > K.limits.text) throw Error('输入过长');
  const found = cache.get(text); if (found) return found;
  const g = K.read(text);
  const cost = text.length + (g === TOP ? 0 : g.size * 8);
  if (cost < 100000) {
    while (cache.size && (cache.size >= 32 || cacheSize + cost > 1000000)) {
      const oldest = cache.keys().next().value, previous = cache.get(oldest);
      cacheSize -= oldest.length + (previous === TOP ? 0 : previous.size * 8); cache.delete(oldest);
    }
    cache.set(text, g); cacheSize += cost;
  }
  return g;
}
const canonical = raw => operation(K => { const g = parse(raw, K); return g === TOP ? TOP : K.write(g); });
const plain = raw => operation(K => { const g = parse(raw, K); return g === TOP ? 'Limit of ' + NAME : K.write(g); });
const latex = raw => {
  const value = plain(raw);
  return value.startsWith('Limit') ? '\\mathrm{Limit\\ of\\ }\\Omega\\mathrm{-CWY}' :
    '\\mathtt{' + value.replace(/[{}]/g, c => '\\' + c) + '}';
};
function draw(raw, settings = {}) {
  try {
    const diagram = operation(K => mountain(parse(raw, K), K, settings));
    return diagram._omegaCWY2.complete ? withCounts(diagram, counts(raw)) : diagram;
  }
  catch (error) { return unavailable(error instanceof Error ? error.message : String(error)); }
}
function counts(raw) {
  // A trailing operation() time check would discard a correctly preserved
  // partial prefix after the nested kernel reported its time budget.
  try {
    const key = String(raw); if (lastCount?.key === key) return lastCount.result;
    const K = createKernel(), result = countSequence(parse(raw, K), K);
    if (key.length + result.text.length < 100000) lastCount = {key, result};
    return result;
  }
  catch (error) { return {text: '?', complete: false, values: null,
    reason: error instanceof Error ? error.message : String(error)}; }
}
register_notation({
  id: 'omega-cwy2-self-v1', name: NAME, simple_name: NAME,
  description: [
    'Ω-CWY：列标使用同类有限表达式的自索引轮廓候选。良序性、共尾性及与 wY 的强度比较尚未证明。',
    '列的位置地址仍为自然数；序数列标是有限、无环的严格子表达式，有自己的局部列编号。',
    'T0=1，T(n+1)=S(Tn)，Top[n]=Tn；S(D) 是以 D 为唯一变点列标的固定两列种子。因此 Tn 恰有 n 层标签嵌套。',
    '默认列表：[父:(普通有限词)]，或 [父:(根|{列标表达式}:地址,…)]; 多条父关系用分号隔开。有限列标可写自然数。',
    '有限词中的重复地址全部逐项列出，不使用重复幂、乘数或省略号。复杂列标以花括号包含完整表达式。',
    '展开的第 b 个块（b 从 0 起），对后继列标删末列、对极限列标取 D[b+1]；自然数地址搬运不进入嵌套列标内部。',
    '所有非零有限式的第零项删末列，后续项满足逐列前缀关系。外顶端按嵌套深度展开，不要求顶端项相互为前缀。',
    '输入 T0、T1、T2、T2[4]、Top[3]、自然数或完整列表。Wk 是规范 ω 的 k 次幂片段的输入别名，W=W1；WW 是其 ω^ω 界。',
    '三个视图为“原式”“计数序列”“山脉图”。计数使用 BigInt，计算每列作为末列反复降低再删除的步数；计数不是唯一编码或比较键。',
    '山脉图也可打开“显示图表”并悬停查看；有限层标不受 ω^ω 限制，统一按记号自身的比较规则排序。',
    '精确识别为 ε0 以下康托正规式的层标用 ω 幂、系数与和表示；其余层标写完整原式，长层标换行但不省略。',
    '这是完整的轮廓分层图，不是已证明的 wY 几何重建。红色底点为列地址，斜线给出父列，黑点数为轮廓地址；变点间恒定。',
    '山脉图最底部另列完整计数序列，未知项为 ?；红色底点仍为父列寻址用的自然数，不是计数。',
    '不合适或超限时整图提示原因，不截取部分列/层。超过绘图范围仍可在列表中展开。',
    '单次接口约 700ms 预算；有列数、嵌套、文本与缓存上限。超限不是数学上的终止或非终止。',
    '计数遇到预算时保留已算出的前缀，当前及后续每列用 ? 占位；未知计数不参与比较或展开。',
    '手写式只检查结构，不等于标准域成员。文件使用独立 ID，不修改旧 CWY2 或 ω+1 版。',
  ],
  display: {name: '原式', plain, html: raw => '<span style="font-family:inherit;white-space:nowrap">' + escape(plain(raw)) + '</span>', from_display: canonical, latex},
  display_equiv: {
    '计数序列': {plain: raw => counts(raw).text,
      html: raw => { const c = counts(raw); return '<span style="font-family:inherit;white-space:nowrap"' +
        (c.reason ? ' title="' + escape(c.reason) + '"' : '') + '>' + escape(c.text) + '</span>'; },
      latex: raw => { const c = counts(raw); return c.complete && c.values === null ? latex('Top') : c.text; }},
    '山脉图': {plain, html: raw => svg(draw(raw)), from_display: canonical, latex}},
  FS: (raw, n) => operation(K => { const g = parse(raw, K); K.natural(n); return K.write(g === TOP ? K.tower(Number(n)) : K.fs(g, n)); }),
  compare: (a, b) => operation(K => { const x = parse(a, K), y = parse(b, K); return x === TOP ? y === TOP ? 0 : 1 : y === TOP ? -1 : K.compare(x, y); }),
  is_limit: raw => operation(K => { const g = parse(raw, K); return g === TOP || K.isLimit(g); }),
  init: () => [TOP, '[]', '0'],
  draw_diagram: {default_data: {invert_vertical: false, column_width: 42}, draw_diagram: draw,
    settings: [{type: 'number', name: '列间距', min: 34, max: 100, field_name: 'column_width'},
      {type: 'boolean', name: '上下翻转', field_name: 'invert_vertical'}],
    handle_action: (data, action) => action.type === 'scroll' && ['up', 'down'].includes(action.direction)
      ? {...data, invert_vertical: action.direction === 'down'} : null},
  debug: {canonical, diagram: draw, counts, svg: raw => svg(draw(raw), true),
    inspect: raw => operation(K => { const g = parse(raw, K); return g === TOP ? {top: true} :
      {columns: g.columns.length, depth: g.depth, size: g.size, polynomial: K.decodePolynomial(g)}; }),
    clear_cache: () => { cache.clear(); cacheSize = 0; lastCount = null; }, cache_stats: () => ({entries: cache.size, estimatedSize: cacheSize})},
});

})();
