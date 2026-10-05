// Standalone NER: ordinary M13 with a monotone Y LOWER bound.
// This is not a reverse order embedding. Only one notation is registered.
(function(register){
'use strict';let bridge;
(function(register_notation){
// Standalone NER: canonical strict Y -> ordinary M13 order embedding.
// 2026-09-20. Paper proof: ORDER-EMBEDDING.zh-CN.md. No network or Node runtime.
// Original Y rules and ordinary e0MN rules are bundled unchanged mathematically.
(function(register){
'use strict';
let M;
(function(register_notation){
/* e0MN custom notation for NER -- fast-counting edition, 2026-09-17
 * https://smilelee-lyx.github.io/ne-rewritten/
 * Initial entries: Limit, (), 0; Limit[n] = ()(1:ω^^n).
 * Original expansion, comparison and drawing are unchanged. Counts freeze the
 * earlier columns and iterate down; the final deletion of an empty column is 1.
 */
(() => {
  'use strict';

  // ---------- e0 expressions ----------
  // Ord = [{ exp: Ord, coeff: positive integer }]; zero = [].
  const LIMIT = 'Limit';
  const cloneOrd = a => a.map(t => ({ exp: cloneOrd(t.exp), coeff: t.coeff }));
  const cloneCol = c => c.map(e => ({ a: e.a, x: cloneOrd(e.x) }));
  const cloneExpr = e => e.map(cloneCol);
  const ordNat = n => {
    if (!Number.isSafeInteger(n) || n < 0) throw Error(`Natural number expected: ${n}`);
    return n ? [{ exp: [], coeff: n }] : [];
  };
  const ordOne = () => ordNat(1);
  const isZero = a => a.length === 0;
  const isOne = a => a.length === 1 && isZero(a[0].exp) && a[0].coeff === 1;
  const isPositive = a => a.length > 0;

  function ordCompare(a, b) {
    for (let i = 0, n = Math.min(a.length, b.length); i < n; i++) {
      const c = ordCompare(a[i].exp, b[i].exp);
      if (c) return c;
      if (a[i].coeff !== b[i].coeff) return a[i].coeff > b[i].coeff ? 1 : -1;
    }
    return Math.sign(a.length - b.length);
  }
  const ordEq = (a, b) => ordCompare(a, b) === 0;
  const ordIsSuccessor = a => isPositive(a) && isZero(a[a.length - 1].exp);

  function ordIsStandard(a) {
    return Array.isArray(a) && a.every((t, i) =>
      Number.isSafeInteger(t.coeff) && t.coeff > 0 && ordIsStandard(t.exp) &&
      (!i || ordCompare(a[i - 1].exp, t.exp) > 0));
  }

  // Ordinal addition and the right difference beta-alpha defined by alpha+gamma=beta.
  // These operate on standard Cantor-normal-form e0 ordinals.
  function ordAdd(a, b) {
    if (!b.length) return cloneOrd(a);
    const lead = b[0].exp;
    let i = 0;
    while (i < a.length && ordCompare(a[i].exp, lead) > 0) i++;
    const out = cloneOrd(a.slice(0, i));
    if (i < a.length && ordEq(a[i].exp, lead)) {
      out.push({ exp: cloneOrd(lead), coeff: a[i].coeff + b[0].coeff });
      for (let j = 1; j < b.length; j++) out.push({ exp: cloneOrd(b[j].exp), coeff: b[j].coeff });
    } else {
      for (const t of b) out.push({ exp: cloneOrd(t.exp), coeff: t.coeff });
    }
    return out;
  }

  function ordRightDiff(a, b) {
    const cmp = ordCompare(a, b);
    if (cmp > 0) throw Error('Ordinal right difference requires the second ordinal to be at least the first');
    if (!cmp) return [];
    let i = 0;
    while (i < a.length && i < b.length && ordEq(a[i].exp, b[i].exp) && a[i].coeff === b[i].coeff) i++;
    if (i === a.length) return cloneOrd(b.slice(i));
    if (i >= b.length) throw Error('Ordinal right difference does not exist');
    const ec = ordCompare(a[i].exp, b[i].exp);
    if (ec < 0) return cloneOrd(b.slice(i));
    if (ec === 0 && a[i].coeff < b[i].coeff) {
      return [{ exp: cloneOrd(b[i].exp), coeff: b[i].coeff - a[i].coeff }, ...cloneOrd(b.slice(i + 1))];
    }
    throw Error('Ordinal right difference does not exist');
  }

  // e0 fundamental sequence, following cases 1--6 recursively.
  function ordFS(src, m) {
    if (!Number.isSafeInteger(m) || m < 0) throw Error('FS index must be a non-negative integer');
    if (!src.length) return [];

    const a = cloneOrd(src), last = a[a.length - 1];
    if (isZero(last.exp)) { // cases 1, 2
      if (last.coeff === 1) a.pop(); else last.coeff--;
      return a;
    }

    const exp = cloneOrd(last.exp), coeff = last.coeff;
    a.pop();
    if (coeff > 1) a.push({ exp, coeff: coeff - 1 });
    const nextExp = ordFS(exp, m);
    if (ordIsSuccessor(exp)) { // cases 3, 4
      if (m) a.push({ exp: nextExp, coeff: m });
    } else { // cases 5, 6
      a.push({ exp: nextExp, coeff: 1 });
    }
    return a;
  }

  const omegaPower = exp => [{ exp: cloneOrd(exp), coeff: 1 }];
  function omegaTower(n) {
    if (!Number.isSafeInteger(n) || n < 0) throw Error('Tower height must be a non-negative integer');
    let r = ordOne();
    while (n--) r = omegaPower(r);
    return r;
  }

  // In rfl: visible positive integers inside e0 shift iff q > cutoff.
  function shiftOrdNumbers(a, cutoff, d) {
    return a.map(t => {
      if (isZero(t.exp)) return { exp: [], coeff: t.coeff > cutoff ? t.coeff + d : t.coeff };
      return {
        exp: isOne(t.exp) ? cloneOrd(t.exp) : shiftOrdNumbers(t.exp, cutoff, d),
        coeff: t.coeff !== 1 && t.coeff > cutoff ? t.coeff + d : t.coeff,
      };
    });
  }

  // ---------- e0 parser / display ----------
  const normalizeOmega = s => s.replace(/omega/gi, 'ω').replace(/w/g, 'ω');

  function parseOrd(text, allowZero = false) {
    const s = normalizeOmega(String(text)).replace(/\s+/g, '');
    const tower = s.match(/^ω\^\^(\d+)$/);
    if (tower) return omegaTower(Number(tower[1]));
    let i = 0;

    const fail = msg => { throw Error(`Illegal e0 expression "${text}": ${msg} at position ${i}`); };
    const number = () => {
      const start = i;
      while (/\d/.test(s[i] || '')) i++;
      if (start === i) fail('number expected');
      const n = Number(s.slice(start, i));
      if (!Number.isSafeInteger(n)) fail('number is too large');
      return n;
    };

    function expr(end) {
      if (s[i] === '0' && (i + 1 === s.length || (end && s[i + 1] === end))) { i++; return []; }
      const out = [];
      while (i < s.length && (!end || s[i] !== end)) {
        out.push(term());
        if (s[i] !== '+') break;
        i++;
        if (i >= s.length || (end && s[i] === end)) fail('term expected after "+"');
      }
      return out;
    }

    function exponent() {
      if (i >= s.length) fail('exponent expected');
      const open = s[i];
      if (open === '{' || open === '(') {
        const close = open === '{' ? '}' : ')';
        i++;
        if (s[i] === close) { i++; return []; }
        const e = expr(close);
        if (s[i] !== close) fail(`missing "${close}"`);
        i++;
        return e;
      }
      if (/\d/.test(s[i])) return ordNat(number());
      if (s[i] === 'ω') return [term()];
      fail('bad exponent');
    }

    function term() {
      if (i >= s.length) fail('term expected');
      if (/\d/.test(s[i])) {
        const n = number();
        if (n <= 0) fail('positive integer expected');
        return { exp: [], coeff: n };
      }
      if (s[i] !== 'ω') fail('term must start with a positive integer or ω');
      i++;
      let exp = ordOne();
      if (s[i] === '^') { i++; exp = exponent(); }
      let coeff = 1;
      if (/\d/.test(s[i] || '')) {
        coeff = number();
        if (coeff <= 0) fail('positive coefficient expected');
      }
      return { exp, coeff };
    }

    if (!s) fail('empty expression');
    if (s === '0') { if (allowZero) return []; fail('row label must be positive'); }
    const out = expr();
    if (i !== s.length) fail(`unexpected character "${s[i]}"`);
    if (!allowZero && !out.length) fail('row label must be positive');
    return out;
  }

  function ordTo(a, mode) {
    if (!a.length) return '0';
    return a.map(t => {
      if (isZero(t.exp)) return String(t.coeff);
      let q = mode === 'latex' ? '\\omega' : 'ω';
      if (!isOne(t.exp)) {
        const e = ordTo(t.exp, mode);
        q += mode === 'html' ? `<sup>${e}</sup>` : `^{${e}}`;
      }
      return q + (t.coeff === 1 ? '' : t.coeff);
    }).join('+');
  }
  const ordToPlain = a => ordTo(a, 'plain');
  const ordToHTML = a => ordTo(a, 'html');
  const ordToLatex = a => ordTo(a, 'latex');

  function towerIndex(a) {
    if (isOne(a)) return 0;
    if (a.length !== 1 || a[0].coeff !== 1 || isZero(a[0].exp)) return -1;
    const k = towerIndex(a[0].exp);
    return k < 0 ? -1 : k + 1;
  }

  // ---------- e0MN parse / display ----------
  const entryCompare = (p, q) => p.a === q.a ? ordCompare(p.x, q.x) : (p.a > q.a ? 1 : -1);
  function arrayLexCompare(a, b, cmp) {
    for (let i = 0, n = Math.min(a.length, b.length); i < n; i++) {
      const c = cmp(a[i], b[i]);
      if (c) return c;
    }
    return Math.sign(a.length - b.length);
  }
  const colCompare = (a, b) => arrayLexCompare(a, b, entryCompare);
  const exprCompare = (a, b) => a === LIMIT ? (b === LIMIT ? 0 : 1)
    : b === LIMIT ? -1 : arrayLexCompare(a, b, colCompare);

  function isLegalColumn(c, colNo) {
    return c.every((e, i) =>
      Number.isSafeInteger(e.a) && e.a > 0 && e.a < colNo && isPositive(e.x) &&
      (!i || (c[i - 1].a > e.a && ordCompare(c[i - 1].x, e.x) < 0)));
  }
  const isLegalExpr = e => Array.isArray(e) && e.every((c, i) => Array.isArray(c) && isLegalColumn(c, i + 1));
  const isLimitExpr = e => e === LIMIT || (isLegalExpr(e) && !!e.length && !!e[e.length - 1].length);
  const predecessor = e => e.length ? cloneExpr(e.slice(0, -1)) : [];
  const makeLimit = n => [[], [{ a: 1, x: omegaTower(n) }]];

  function exprLimitIndex(e) {
    return e.length === 2 && !e[0].length && e[1].length === 1 && e[1][0].a === 1
      ? towerIndex(e[1][0].x) : -1;
  }

  function splitTop(s, sep) {
    const out = [];
    let start = 0, p = 0, b = 0;
    for (let i = 0; i < s.length; i++) {
      const ch = s[i];
      if (ch === '(') p++; else if (ch === ')') p--;
      else if (ch === '{') b++; else if (ch === '}') b--;
      else if (ch === sep && !p && !b) { out.push(s.slice(start, i)); start = i + 1; }
    }
    out.push(s.slice(start));
    return out;
  }

  function topColon(s) {
    let p = 0, b = 0;
    for (let i = 0; i < s.length; i++) {
      const ch = s[i];
      if (ch === '(') p++; else if (ch === ')') p--;
      else if (ch === '{') b++; else if (ch === '}') b--;
      else if (ch === ':' && !p && !b) return i;
    }
    return -1;
  }

  function parseColumn(s) {
    if (!s.trim()) return [];
    return splitTop(s, ';').map(piece => {
      const colon = topColon(piece);
      if (colon < 0) throw Error(`Entry must have form a:x; got: ${piece}`);
      const aText = piece.slice(0, colon).trim(), xText = piece.slice(colon + 1).trim();
      if (!/^\d+$/.test(aText)) throw Error(`Left-leg column label must be a positive integer: ${aText}`);
      const a = Number(aText);
      if (!Number.isSafeInteger(a) || a <= 0) throw Error(`Left-leg column label must be a positive integer: ${aText}`);
      return { a, x: parseOrd(xText) };
    });
  }

  function parseExpr(text) {
    const raw = String(text).trim();
    if (!raw || raw === '0' || raw === '∅') return [];
    if (/^Limit$/i.test(raw)) return LIMIT;
    const lim = raw.match(/^Limit\s*\[\s*(\d+)\s*\]$/i);
    if (lim) return makeLimit(Number(lim[1]));

    const out = [];
    for (let i = 0; i < raw.length;) {
      while (/\s/.test(raw[i] || '')) i++;
      if (i >= raw.length) break;
      if (raw[i] !== '(') throw Error(`Expected "(" at position ${i} in e0MN expression`);
      let p = 0, b = 0, end = -1;
      for (let j = i; j < raw.length; j++) {
        const ch = raw[j];
        if (ch === '(') p++; else if (ch === ')') { p--; if (!p && !b) { end = j; break; } }
        else if (ch === '{') b++; else if (ch === '}') b--;
      }
      if (end < 0) throw Error('Unmatched "(" in e0MN expression');
      out.push(parseColumn(raw.slice(i + 1, end)));
      i = end + 1;
    }
    return out;
  }

  function colTo(c, mode) {
    if (!c.length) return mode === 'latex' ? '\\left(\\right)' : '()';
    const body = c.map(e => `${e.a}:${ordTo(e.x, mode)}`).join(';');
    return mode === 'latex' ? `\\left(${body}\\right)` : `(${body})`;
  }
  const exprToPlain = e => e === LIMIT ? LIMIT : e.map(c => colTo(c, 'plain')).join('');
  const exprToHTML = e => e === LIMIT ? LIMIT : e.map(c => colTo(c, 'html')).join('');
  const exprToLatex = e => e === LIMIT ? '\\operatorname{Limit}' : e.map(c => colTo(c, 'latex')).join('');
  function exprToLimit(e, mode) {
    if (e === LIMIT) return mode === 'latex' ? '\\operatorname{Limit}' : LIMIT;
    const n = exprLimitIndex(e);
    if (n < 0) return mode === 'plain' ? exprToPlain(e) : mode === 'html' ? exprToHTML(e) : exprToLatex(e);
    return mode === 'latex' ? `\\operatorname{Limit}[${n}]` : `Limit[${n}]`;
  }

  // Equivalent display "行高差": keep the first row ordinal, then display the
  // unique gamma with x_prev + gamma = x_cur.  In HTML/LaTeX gamma is a superscript.
  function rowHeightEntry(a, delta, mode) {
    if (isOne(delta)) return String(a);
    const d = ordTo(delta, mode);
    if (mode === 'html') return `${a}<sup>${d}</sup>`;
    if (mode === 'latex') return `${a}^{${d}}`;
    return `${a}:${d}`;
  }

  function rowHeightColTo(c, mode) {
    if (!c.length) return mode === 'latex' ? '\\left(\\right)' : '()';
    let prev = [];
    const body = c.map((e, i) => {
      const delta = i ? ordRightDiff(prev, e.x) : cloneOrd(e.x);
      if (i && !ordEq(ordAdd(prev, delta), e.x)) throw Error('Internal error: row-height difference is incorrect');
      prev = e.x;
      return rowHeightEntry(e.a, delta, mode);
    }).join(',');
    return mode === 'latex' ? `\\left(${body}\\right)` : `(${body})`;
  }
  const exprToRowHeightPlain = e => e === LIMIT ? LIMIT : e.map(c => rowHeightColTo(c, 'plain')).join('');
  const exprToRowHeightHTML = e => e === LIMIT ? LIMIT : e.map(c => rowHeightColTo(c, 'html')).join('');
  const exprToRowHeightLatex = e => e === LIMIT ? '\\operatorname{Limit}' : e.map(c => rowHeightColTo(c, 'latex')).join('');

  function parseRowHeightColumn(s) {
    if (!s.trim()) return [];
    let prev = [];
    return splitTop(s, ',').map((piece, i) => {
      piece = piece.trim();
      if (!piece) throw Error('Empty entry in 行高差 column');
      const colon = topColon(piece);
      const aText = (colon < 0 ? piece : piece.slice(0, colon)).trim();
      if (!/^\d+$/.test(aText)) throw Error(`Left-leg column label must be a positive integer: ${aText}`);
      const a = Number(aText);
      if (!Number.isSafeInteger(a) || a <= 0) throw Error(`Left-leg column label must be a positive integer: ${aText}`);
      const delta = colon < 0 ? ordOne() : parseOrd(piece.slice(colon + 1).trim());
      const x = i ? ordAdd(prev, delta) : cloneOrd(delta);
      prev = x;
      return { a, x };
    });
  }

  function parseRowHeightExpr(text) {
    const raw = String(text).trim();
    if (!raw || raw === '0' || raw === '∅') return [];
    if (/^Limit$/i.test(raw)) return LIMIT;
    const lim = raw.match(/^Limit\s*\[\s*(\d+)\s*\]$/i);
    if (lim) return makeLimit(Number(lim[1]));

    const out = [];
    for (let i = 0; i < raw.length;) {
      while (/\s/.test(raw[i] || '')) i++;
      if (i >= raw.length) break;
      if (raw[i] !== '(') throw Error(`Expected "(" at position ${i} in 行高差 expression`);
      let p = 0, b = 0, end = -1;
      for (let j = i; j < raw.length; j++) {
        const ch = raw[j];
        if (ch === '(') p++;
        else if (ch === ')') { p--; if (!p && !b) { end = j; break; } }
        else if (ch === '{') b++;
        else if (ch === '}') b--;
      }
      if (end < 0) throw Error('Unmatched "(" in 行高差 expression');
      out.push(parseRowHeightColumn(raw.slice(i + 1, end)));
      i = end + 1;
    }
    return out;
  }

  // ---------- down / rfl / e0MN fundamental sequence ----------
  function down(src) {
    if (!isLimitExpr(src)) return predecessor(src);
    const e = cloneExpr(src), l = e.length, last = e[l - 1], n = last.length;
    const { a: an, x: xn } = last[n - 1], d = l - an;
    if (d <= 0) throw Error('Illegal e0MN expression: d <= 0');

    const source = e[an - 1];
    let s = 0;
    while (s < source.length && ordCompare(source[s].x, xn) < 0) s++;

    const newLast = last.slice(0, -1).map(z => ({ a: z.a, x: cloneOrd(z.x) }));
    const xnL = ordFS(xn, l - 1); // exactly x_n[l-1]
    const omit = isOne(xn) || (n > 1 && ordEq(xnL, last[n - 2].x));
    if (!omit && isPositive(xnL)) newLast.push({ a: an, x: xnL });
    for (let j = s; j < source.length; j++) newLast.push({ a: source[j].a, x: cloneOrd(source[j].x) });
    e[l - 1] = newLast;
    return e;
  }

  const processRflCol = (c, cutoff, d) => c.map(z => ({
    a: z.a >= cutoff ? z.a + d : z.a,
    x: shiftOrdNumbers(z.x, cutoff, d),
  }));

  function rfl(src) {
    if (!isLimitExpr(src)) return predecessor(src);
    const l = src.length, an = src[l - 1][src[l - 1].length - 1].a, d = l - an;
    if (d <= 0) throw Error('Illegal e0MN expression: d <= 0');
    const out = down(src);
    for (let col = an + 1; col <= l; col++) out.push(processRflCol(src[col - 1], an, d));
    return out;
  }

  function FS(src, m) {
    if (!Number.isSafeInteger(m) || m < 0) throw Error('FS index must be a non-negative integer');
    if (src === LIMIT) return makeLimit(m);
    if (!src.length) return [];
    if (!m || !isLimitExpr(src)) return predecessor(src);
    let r = cloneExpr(src);
    while (m--) r = rfl(r);
    return predecessor(r);
  }

  function FSShort(src, m) {
    if (!Number.isSafeInteger(m) || m < 0) throw Error('FS index must be a non-negative integer');
    if (src === LIMIT) return makeLimit(m);
    if (!src.length) return [];
    if (!m || !isLimitExpr(src)) return predecessor(src);
    if (m === 1) return down(src);
    const last = src[src.length - 1], d = src.length - last[last.length - 1].a;
    return FS(src, d === 1 ? m : m - 1);
  }

  // ---------- exact local counting display ----------
  // A task (a, upper) above an unchanged lower row finishes before that lower
  // row is touched. Each down step lowers upper and temporarily attaches a
  // suffix of column a. Its tasks have strictly smaller parent addresses.
  // Memoizing those tasks avoids enumerating a potentially enormous countdown.
  // Only the resulting counts are BigInts; the original CNF/FS semantics stay
  // unchanged (the original file uses safe Number coefficients).
  const countCache = new Map();
  let countCacheChars = 0;
  const COUNT_MAX = (1n << 32768n) - 1n;

  function countError(detail) {
    const error = Error('计数超限：' + detail + '（不是不终止的结论）');
    error.name = 'E0MNCountLimit';
    throw error;
  }


  // Exact fixed-host acceleration for normal polynomial rows.
  // At host m, W_0=1 and W_(d+1)=m W_d+1. On m-normal polynomials
  // H(sum omega^d c_d)=sum c_d W_d is strictly increasing and
  // H(alpha[m])=H(alpha)-1. All ancestors use this SAME host m.
  //
  // F_p(r) is the work until column p falls below row rank r. If a is
  // the parent of the first original row >=r, then
  // F_p(r)=F_p(r+1)+1+F_a(r). Parent choices are constant between
  // original row ranks. Binomial-basis polynomials sum whole intervals.
  // null means "outside this fast path", never an approximate count.
  function polynomialCount(expr, host, tick, add, info) {
    if (!expr[host].length) return 1n;
    if (!host) return null;
    const used = new Set([host]), pending = [host], terms = new Map();
    let maxDegree = 0;
    while (pending.length) {
      const p = pending.pop(), rows = [];
      for (const edge of expr[p]) {
        tick();
        const row = [];
        for (let k = 0; k < edge.x.length; k++) {
          tick();
          const t = edge.x[k];
          let d = 0;
          if (t.exp.length) {
            if (t.exp.length !== 1 || t.exp[0].exp.length) return null;
            d = t.exp[0].coeff;
          }
          if (d > host || t.coeff > host ||
              (t.coeff === host && k !== edge.x.length - 1)) return null;
          maxDegree = Math.max(maxDegree, d);
          row.push([d, t.coeff]);
        }
        const a = edge.a - 1;
        rows.push({ parent: a, terms: row });
        if (!used.has(a)) { used.add(a); pending.push(a); }
      }
      terms.set(p, rows);
    }
    const indices = [...used].sort((a, b) => a - b);
    // At most one degree is added per ancestor. Limit the live coefficient
    // table BEFORE allocating it; an ineligible-size input uses the fallback.
    if (indices.length * (indices.length + 1) / 2 > 350000) return null;
    const bounded = n => {
      if (n > COUNT_MAX) countError('快计数中间整数超过 32768 位');
      return n;
    };
    const weights = [1n], base = BigInt(host);
    for (let d = 1; d <= maxDegree; d++) {
      tick(); weights.push(bounded(base * weights[d - 1] + 1n));
    }
    const lookup = new Map(indices.map((p, i) => [p, i])), cuts = new Set([0n]);
    const cols = indices.map(p => terms.get(p).map(edge => {
      let rank = 0n;
      for (const [d, c] of edge.terms) {
        tick(); rank = add(rank, bounded(BigInt(c) * weights[d]));
      }
      cuts.add(rank);
      return { parent: lookup.get(edge.parent), rank };
    }));
    const knots = [...cuts].sort((a, b) => a < b ? -1 : a > b ? 1 : 0);
    const carry = cols.map(() => 0n), active = cols.map(c => c.length - 1);
    function evaluate(poly, q) {
      let value = 0n, choose = 1n;
      for (let k = 0; k < poly.length; k++) {
        tick();
        if (k) choose = bounded(choose * (q - BigInt(k) + 1n) / BigInt(k));
        if (!choose) break;
        value = add(value, bounded(poly[k] * choose));
      }
      return value;
    }
    for (let interval = knots.length - 1; interval > 0; interval--) {
      tick();
      const high = knots[interval], span = high - knots[interval - 1];
      const polynomials = [];
      for (let p = 0; p < cols.length; p++) {
        tick();
        const col = cols[p];
        if (!col.length || col[col.length - 1].rank < high) {
          polynomials.push([0n]);
          continue;
        }
        while (active[p] > 0 && col[active[p] - 1].rank >= high) {
          tick(); active[p]--;
        }
        const a = polynomials[col[active[p]].parent];
        const b = Array(a.length + 1).fill(0n);
        b[0] = carry[p]; b[1] = add(1n, a[0]);
        for (let k = 1; k < a.length; k++) {
          tick();
          b[k] = add(b[k], a[k]); b[k + 1] = add(b[k + 1], a[k]);
        }
        polynomials.push(b);
      }
      for (let p = 0; p < cols.length; p++)
        carry[p] = evaluate(polynomials[p], span);
    }
    if (info) {
      info.fastHosts = (info.fastHosts || 0) + 1;
      info.intervals = (info.intervals || 0) + knots.length - 1;
    }
    return add(carry[lookup.get(host)], 1n);
  }

  function exactCounts(expr, options) {
    const result = [];
    try {
    if (expr === LIMIT) throw Error('外顶端没有有限列计数');
    const settings = options || {}, started = Date.now();
    const maxMs = settings.maxMs ?? 1000, maxWork = settings.maxWork ?? 2000000;
    let work = 0, nodes = 0, depth = 0;
    const tick = () => {
      if (++work > maxWork) countError('工作量预算');
      if (Date.now() - started > maxMs) countError('约一秒时间预算');
    };
    const checkOrd = (a, level = 0) => {
      tick();
      if (level > 96) countError('行标嵌套深度');
      if (!Array.isArray(a)) throw Error('计数需要标准 Cantor 正规形');
      for (let i = 0; i < a.length; i++) {
        if (++nodes > 60000) countError('行标总大小');
        const t = a[i];
        if (!Number.isSafeInteger(t.coeff) || t.coeff <= 0)
          throw Error('计数需要安全整数系数');
        checkOrd(t.exp, level + 1);
        if (i && ordCompare(a[i - 1].exp, t.exp) <= 0)
          throw Error('计数需要标准 Cantor 正规形');
      }
    };
    if (!Array.isArray(expr)) throw Error('计数需要列序列');
    if (expr.length > 8192) countError('列数');
    for (const col of expr) {
      tick();
      if (!Array.isArray(col)) throw Error('计数需要列序列');
      for (const e of col) checkOrd(e.x);
    }
    if (!isLegalExpr(expr)) throw Error('计数需要合法的 e0MN 列');
    const cacheKey = exprToPlain(expr);
    if (cacheKey.length > 500000) countError('输入文字大小');
    if (!options && countCache.has(cacheKey)) {
      const hit = countCache.get(cacheKey);
      countCache.delete(cacheKey); countCache.set(cacheKey, hit);
      return hit.values.slice();
    }
    const add = (a, b) => {
      const result = a + b;
      if (result > COUNT_MAX) countError('结果超过 32768 位');
      return result;
    };

    // Skip a finite successor tail until either an inherited row becomes
    // active or the unchanged lower row is reached. This is an exact jump.
    function tailJump(current, barrier) {
      const last = current.at(-1);
      if (!last || !isZero(last.exp) || ordCompare(current, barrier) <= 0) return null;
      const base = current.slice(0, -1);
      let remaining = 0;
      if (ordCompare(base, barrier) < 0) {
        const end = barrier.at(-1);
        if (!end || !isZero(end.exp) || !ordEq(base, barrier.slice(0, -1))) return null;
        remaining = end.coeff;
      }
      if (remaining >= last.coeff) return null;
      return { next: remaining ? [...base, { exp: [], coeff: remaining }] : base,
        steps: BigInt(last.coeff) - BigInt(remaining) };
    }

    const finiteMemo = new Map(), finitePrefix = [true];
    const isFiniteOrd = a => !a.length || (a.length === 1 && isZero(a[0].exp));
    for (const col of expr) finitePrefix.push(finitePrefix.at(-1) && col.every(e => isFiniteOrd(e.x)));
    let finiteMemoChars = 0;
    for (let child = 0; child < expr.length; child++) {
      tick();
      const fast = settings.disableFast ? null
        : polynomialCount(expr, child, tick, add, settings.stats);
      if (fast !== null) { result.push(fast); continue; }
      if (settings.stats)
        settings.stats.fallbackHosts = (settings.stats.fallbackHosts || 0) + 1;
      const memo = new Map();
      let memoChars = 0;
      const keyOf = (a, x, lower) => a + '|' + ordToPlain(x) + '|' + ordToPlain(lower);
      function remember(target, key, value) {
        if (target.has(key)) return;
        if (memo.size + finiteMemo.size >= 200000 || memoChars + finiteMemoChars + key.length > 8000000)
          countError('局部缓存大小');
        if (target === finiteMemo) finiteMemoChars += key.length; else memoChars += key.length;
        target.set(key, value);
      }
      function task(a, upper, lower) {
        tick();
        if (++depth > 256) { depth--; countError('任务嵌套深度'); }
        try {
          const originalKey = keyOf(a, upper, lower);
          // Purely finite-row tasks never use the FS index, so earlier columns
          // can share their exact memo entries with later columns.
          const taskMemo = finitePrefix[a] && isFiniteOrd(upper) && isFiniteOrd(lower) ? finiteMemo : memo;
          if (taskMemo.has(originalKey)) return taskMemo.get(originalKey);
          const source = expr[a - 1];
          const sourceMax = source.length ? source.at(-1).x : [];
          const barrier = ordCompare(lower, sourceMax) >= 0 ? lower : sourceMax;
          const trail = [];
          let current = upper, total = 0n;
          while (ordCompare(current, lower) > 0) {
            tick();
            const key = keyOf(a, current, lower);
            if (taskMemo.has(key)) { total = add(total, taskMemo.get(key)); break; }
            if (trail.length >= 20000) countError('单任务路径长度');
            trail.push([key, total]);
            const jump = tailJump(current, barrier);
            if (jump) { total = add(total, jump.steps); current = jump.next; continue; }

            const next = ordFS(current, child);
            if (ordCompare(next, current) >= 0) throw Error('行标基本列没有严格下降');
            if (ordCompare(next, lower) < 0)
              throw Error('down 产生了非法列：降低后的行标越过前一项');
            total = add(total, 1n);
            let previous = next;
            for (const inherited of source) {
              tick();
              if (ordCompare(inherited.x, current) < 0) continue;
              total = add(total, task(inherited.a, inherited.x, previous));
              previous = inherited.x;
            }
            current = next;
          }
          for (const [key, before] of trail) remember(taskMemo, key, total - before);
          remember(taskMemo, originalKey, total);
          return total;
        } finally { depth--; }
      }
      let count = 1n, previous = [];
      for (const e of expr[child]) {
        count = add(count, task(e.a, e.x, previous));
        previous = e.x;
      }
      result.push(count);
    }
    if (!options) {
      const size = cacheKey.length + result.reduce((n, c) => n + c.toString().length, 0);
      if (size <= 2000000) {
        while (countCache.size >= 32 || countCacheChars + size > 2000000) {
          const oldest = countCache.keys().next().value;
          countCacheChars -= countCache.get(oldest).size; countCache.delete(oldest);
        }
        countCache.set(cacheKey, { values: result.slice(), size }); countCacheChars += size;
      }
    }
    return result;
    } catch (error) {
      if (error.name === 'E0MNCountLimit') error.partial = result.slice();
      throw error;
    }
  }

  function countResult(expr, options) {
    try { return {values: exactCounts(expr, options), complete: true}; }
    catch (error) {
      if (error.name !== 'E0MNCountLimit') throw error;
      const prefix = error.partial || [];
      const values = expr.map((col, i) => i < prefix.length ? prefix[i]
        : Array.isArray(col) && !col.length ? 1n : null);
      return {values, complete: values.every(n => n !== null), reason: error.message};
    }
  }

  function countText(expr, options) {
    if (expr === LIMIT) return LIMIT;
    try { return countResult(expr, options).values.map(n => n === null ? '?' : String(n)).join(',') || '0'; }
    catch (error) {
      return '计数不可用：' + error.message;
    }
  }
  const countDisplay = {
    name: '计数序列',
    plain: countText,
    html: expr => `<span style="font-family:inherit">${countText(expr).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;')}</span>`,
    latex: expr => {
      const text = countText(expr);
      if (/^(?:\d+|\?)(,(?:\d+|\?))*$/.test(text)) return text;
      if (text === LIMIT) return '\\operatorname{Limit}';
      return '\\text{' + text.replace(/[\\{}]/g, '') + '}';
    },
    // No inverse parser: a counting sequence alone need not determine a raw expression.
  };

  // ---------- diagram ----------
  // Rows are all e0 row labels x. One separator per adjacent pair; each entry
  // shows a, left leg goes diagonally left/down one row then downward, and right
  // leg continues downward to the next entry or star.
  const escAttr = s => String(s).replace(/&/g, '&amp;').replace(/"/g, '&quot;').replace(/</g, '&lt;').replace(/>/g, '&gt;');

  function drawDiagram(e) {
    if (e === LIMIT || !e.length) return undefined;
    const rows = [];
    const addRow = x => { if (!rows.some(r => ordEq(r, x))) rows.push(cloneOrd(x)); };
    e.forEach(c => c.forEach(z => addRow(z.x)));
    rows.sort(ordCompare);

    const labelW = Math.max(70, Math.min(240, 24 + Math.max(1, ...rows.map(r => ordToLatex(r).length)) * 7));
    const colW = 44, rowH = 42, pad = 12, font = 14, off = 10;
    const totalRows = rows.length + 1, maxRow = totalRows - 1;
    const width = labelW + e.length * colW, height = pad * 2 + maxRow * rowH;
    const black = { type: 'text' }, gray = { type: 'gray' }, elements = [], extra = [];
    const cy = r => pad + (maxRow - r) * rowH;
    const cx = c => labelW + c * colW + colW / 2;
    const rowOf = x => rows.findIndex(r => ordEq(r, x)) + 1;
    const line = (x1, y1, x2, y2, color = black) => elements.push({
      type: 'line', x1, y1, x2, y2, stroke: true, stroke_color: color, width: 1,
    });

    for (let r = 1; r < totalRows; r++) line(0, (cy(r) + cy(r - 1)) / 2, width, (cy(r) + cy(r - 1)) / 2, gray);
    rows.forEach((row, i) => {
      const latex = ordToLatex(row);
      extra.push({
        text: `<span data-latex="${escAttr(latex)}">${ordToHTML(row)}</span>`,
        x: labelW / 2, y: cy(i + 1), size: font, color: black, align: 'center', display_html: true,
      });
    });

    const occupied = e.map(c => {
      const map = Object.create(null); map[0] = '*';
      c.forEach(z => { const r = rowOf(z.x); if (r > 0) map[r] = String(z.a); });
      return map;
    });
    const below = (col, row) => {
      for (let r = row - 1; r >= 0; r--) if (occupied[col][r] !== undefined) return r;
      return 0;
    };

    // right legs
    occupied.forEach((map, c) => {
      const keys = Object.keys(map).map(Number).sort((a, b) => a - b);
      for (let i = 1; i < keys.length; i++) line(cx(c), cy(keys[i]) + off, cx(c), cy(keys[i - 1]) - off);
    });

    // left legs
    e.forEach((c, col) => c.forEach(z => {
      const srcRow = rowOf(z.x), targetCol = z.a - 1;
      if (srcRow <= 0 || targetCol < 0 || targetCol >= col) return;
      const oneDown = srcRow - 1, targetRow = below(targetCol, srcRow), y = cy(oneDown) - off;
      line(cx(col), cy(srcRow) + off, cx(targetCol), y);
      if (targetRow < oneDown) line(cx(targetCol), y, cx(targetCol), cy(targetRow) - off);
    }));

    occupied.forEach((map, c) => Object.keys(map).map(Number).forEach(r => extra.push({
      text: map[r], x: cx(c), y: cy(r), size: font, color: black, align: 'center',
    })));
    return { width, height, elements, extra_text: extra };
  }

  // ---------- NER registration ----------
  const originalDisplay = {
    plain: exprToPlain,
    html: exprToHTML,
    latex: exprToLatex,
    from_display: parseExpr,
    name: '原记号',
  };
  const rowHeightDisplay = {
    plain: exprToRowHeightPlain,
    html: exprToRowHeightHTML,
    latex: exprToRowHeightLatex,
    from_display: parseRowHeightExpr,
    name: '行高差',
  };

  const notation = {
    id: 'e0mn-fast-counting-v02',
    name: 'e0 Mountain Notation（快计数版）',
    simple_name: 'e0MN（快计数版）',
    category_id: 'category-mn',
    description: [
      'Made by test_alpha0',
      '快计数版：原 FS、FS_short、比较、输入和图形不变。正规多项式行标使用精确分段求和，其余回退原计数器。保留已算出的计数，未算出的列用 ?；问号不表示不终止。',
    ],
    display: originalDisplay,
    display_equiv: {
      '行高差': rowHeightDisplay,
      '计数序列': countDisplay,
    },
    is_limit: isLimitExpr,
    compare: exprCompare,
    FS,
    FS_short: FSShort,
    draw_diagram: { default_data: {}, draw_diagram: drawDiagram },
    init: () => [LIMIT, [[]], []],
    debug: { parseOrd, ordFS, ordAdd, ordRightDiff, parseExpr, parseRowHeightExpr, exprToPlain, exprToRowHeightPlain, down, rfl, isLegalExpr, drawDiagram, exactCounts, countResult, countText },
  };

  register_notation(notation);
})();

})(v=>{M=v;});
const originalFS=M.FS;
M={...M,FS:(a,n)=>{
  const c=Array.isArray(a)&&a.at(-1)?.at(-1);
  const width=c&&n?a.length-1+n*(a.length-c.a):Math.max(0,a.length-1);
  if(!Number.isSafeInteger(width)||width>=1200)throw Error('M target width budget (1200 columns)');
  return originalFS(a,n);
}};

function createBrowserYEngine(options) {
  'use strict';
  options = options ?? {};
  const defaults = {timeoutMs: 100, maxWork: 500000, maxWidth: 64, maxLayers: 32, maxDigits: 2000, maxAtoms: 40000};
  const __limits = {};
  for (const key of Object.keys(defaults)) {
    const value = options[key] ?? (key === 'timeoutMs' ? options.ms : undefined) ?? defaults[key];
    if (!Number.isSafeInteger(value) || value < 1) throw new RangeError(key + ' must be a positive safe integer');
    __limits[key] = value;
  }
  if (__limits.maxDigits > 100000) throw new RangeError('Browser Y maximum digit budget is 100000');
  const __valueLimit = 10n ** BigInt(__limits.maxDigits);
  let __work = 0, __deadline = 0, __badDepth = 0, __expandDepth = 0;
  function __budget(message) {
    const error = new RangeError(message);
    error.name = 'BudgetError'; error.code = 'Y_BUDGET'; throw error;
  }
  function __tick(amount = 1) {
    __work += amount;
    if (__work > __limits.maxWork) __budget('Y browser work limit');
    if (Date.now() > __deadline) __budget('Y browser time limit');
  }
  function __begin() {
    __work = 0; __deadline = Date.now() + __limits.timeoutMs;
    __badDepth = 0; __expandDepth = 0; __tick();
  }
  function __checkValue(value) {
    __tick();
    if (typeof value !== 'bigint' || value < 1n) throw new RangeError('Y values must be positive BigInts');
    if (value >= __valueLimit) __budget('Y browser integer digit limit');
  }
  function __validate(sequence) {
    if (!Array.isArray(sequence)) throw new TypeError('Y sequence must be a BigInt array');
    if (sequence.length > __limits.maxWidth) __budget('Y browser input width limit');
    for (const value of sequence) { __tick(); __checkValue(value); }
  }
  function __checkMountain(mountain) {
    __tick();
    if (mountain.length > __limits.maxLayers) __budget('Y browser mountain row limit');
    for (const row of mountain) {
      __tick();
      if (row.length > __limits.maxWidth) __budget('Y browser mountain width limit');
      for (const entry of row) { __tick(); __checkValue(entry.value); }
    }
    return mountain;
  }
  function calcMountain(sequence) {
    __tick(); return __checkMountain(__original_calcMountain(sequence));
  }
  function getBadRoot(sequence) {
    __tick();
    if (++__badDepth > __limits.maxLayers) { --__badDepth; __budget('Y browser diagonal depth limit'); }
    try { return __original_getBadRoot(sequence); } finally { --__badDepth; }
  }
  function expand(sequence, n, stringify) {
    __tick();
    if (++__expandDepth > __limits.maxLayers) { --__expandDepth; __budget('Y browser expansion depth limit'); }
    try { return __original_expand(sequence, n, stringify); } finally { --__expandDepth; }
  }
var itemSeparatorRegex=/[\t ,]/g
    function parseSequenceElement(s,i){
      if (s.indexOf("v")==-1||!isFinite(Number(s.substring(s.indexOf("v")+1)))){
        var numval=BigInt(s);
        return {
          value:numval,
          position:i,
          parentIndex:-1
        };
      }else{
        return {
          value:BigInt(s.substring(0,s.indexOf("v"))),
          position:i,
          parentIndex:Math.max(Math.min(i-1,Number(s.substring(s.indexOf("v")+1))),-1),
          forcedParent:true
        };
      }
    }
    function __original_calcMountain(s){
      //if (!/^(\d+,)*\d+$/.test(s)) throw Error("BAD");
      var lastLayer;
      if (typeof s=="string"){
        lastLayer=s.split(itemSeparatorRegex).map(parseSequenceElement);
      }
      else lastLayer=s;
      var calculatedMountain=[lastLayer]; //rows
      while (true){__tick();
        //assign parents
        var hasNextLayer=false;
        for (var i=0;i<lastLayer.length;i++){__tick();
          if (lastLayer[i].forcedParent){
            if (lastLayer[i].parentIndex!=-1) hasNextLayer=true;
            continue;
          }
          var p;
          if (calculatedMountain.length==1){
            p=lastLayer[i].position+1;
          }else{
            p=0;
            while (calculatedMountain[calculatedMountain.length-2][p].position<lastLayer[i].position+1) {__tick();p++;}
          }
          while (true){__tick();
            if (p<0) break;
            var j;
            if (calculatedMountain.length==1){
              p--;
              j=p-1;
            }else{ //ignoring
              p=calculatedMountain[calculatedMountain.length-2][p].parentIndex;
              if (p<0) break;
              j=0;
              while (lastLayer[j].position<calculatedMountain[calculatedMountain.length-2][p].position-1) {__tick();j++;}
            }
            if (j<0||j<lastLayer.length-1&&lastLayer[j].position+1!=lastLayer[j+1].position) break;
            if (lastLayer[j].value<lastLayer[i].value){
              lastLayer[i].parentIndex=j;
              hasNextLayer=true;
              break;
            }
          }
        }
        if (!hasNextLayer) break;
        var currentLayer=[];
        if (calculatedMountain.length >= __limits.maxLayers) __budget("Y mountain row limit"); calculatedMountain.push(currentLayer);
        for (var i=0;i<lastLayer.length;i++){__tick();
          if (lastLayer[i].parentIndex!=-1){
            currentLayer.push({value:lastLayer[i].value-lastLayer[lastLayer[i].parentIndex].value,position:lastLayer[i].position-1,parentIndex:-1});
          }
        }
        lastLayer=currentLayer;
      }
      return calculatedMountain;
    }
    function calcDiagonal(mountain){
      var diagonal=[];
      var diagonalTree=[];
      for (var i=0;i<mountain[0].length;i++){__tick(); //only one diagonal exists for each left-side-up diagonal line
        for (var j=mountain.length-1;j>=0;j--){__tick(); //prioritize the top
          var k=0;
          while (mountain[j][k]&&mountain[j][k].position+j<i) {__tick();k++;}
          if (!mountain[j][k]||mountain[j][k].position+j!=i) continue;
          var height=j;
          var lastIndex=k;
          while (true){__tick();
            if (height==0){
              lastIndex=mountain[height][lastIndex].parentIndex;
            }else{
              var l=0; //find right-down
              while (mountain[height-1][l].position!=mountain[height][lastIndex].position+1) {__tick();l++;}
              l=mountain[height-1][l].parentIndex; //go to its parent=left-down
              var m=0; //find up-left of that=left
              while (mountain[height][m].position<mountain[height-1][l].position-1) {__tick();m++;}
              if (mountain[height][m].position==mountain[height-1][l].position-1){ //left exists
                lastIndex=m;
              }else{
                height--;
                lastIndex=l;
              }
            }
            if (!mountain[height][lastIndex]||mountain[height][lastIndex].parentIndex==-1){
              diagonal.push(mountain[j][k].value);
              diagonalTree.push((mountain[height][lastIndex]?mountain[height][lastIndex].position:-1)+height);
              break;
            }
          }
          break;
        }
      }
      var pw=[];
      for (var i=0;i<diagonal.length;i++){__tick();
        var p=-1;
        for (var j=i-1;j>=0;j--){__tick();
          if (diagonal[j]<diagonal[i]){
            p=j;
            break;
          }
        }
        pw.push(p);
      }
      var r=[];
      for (var i=0;i<diagonal.length;i++){__tick();
        var p=i;
        while (true){__tick();
          p=diagonalTree[p];
          if (p<0||diagonal[p]<diagonal[i]) break;
        }
        if (p==pw[i]) r.push(diagonal[i]);
        else r.push(diagonal[i]+"v"+p);
      }
      //console.log(diagonalTree);
      return r.join(",");
    }
    function cloneMountain(mountain){
      var newMountain=[];
      for (var i=0;i<mountain.length;i++){__tick();
        var layer=[];
        for (var j=0;j<mountain[i].length;j++){__tick();
          layer.push({
            value:mountain[i][j].value,
            position:mountain[i][j].position,
            parentIndex:mountain[i][j].parentIndex,
            forcedParent:mountain[i][j].forcedParent
          });
        }
        newMountain.push(layer);
      }
      return newMountain;
    }
    function __original_getBadRoot(s){
      var mountain;
      if (typeof s=="string") mountain=calcMountain(s);
      else mountain=cloneMountain(s);
      var diagonal=calcMountain(calcDiagonal(mountain));
      if (diagonal[0][diagonal[0].length-1].value!=1){
        return getBadRoot(diagonal);
      }else{
        for (var i=mountain.length-1;i>=0;i--){__tick();
          if (mountain[i][mountain[i].length-1].position+i==mountain[0].length-1) return mountain[i-1][mountain[i-1][mountain[i-1].length-1].parentIndex].position+i-1;
        }
      }
    }
    function __original_expand(s,n,stringify){
      var mountain;
      if (typeof s=="string") mountain=calcMountain(s);
      else mountain=cloneMountain(s);
      var result=cloneMountain(mountain);
      if (mountain[0][mountain[0].length-1].parentIndex==-1){
        result[0].pop();
      }else{
        var result=cloneMountain(mountain);
        var cutHeight=mountain.length-1;
        while (mountain[cutHeight][mountain[cutHeight].length-1].position+cutHeight!=mountain[0].length-1) {__tick();cutHeight--;}
        var actualCutHeight=cutHeight;
        var badRootSeam=getBadRoot(mountain);
        var badRootHeight;
        var diagonal=calcMountain(calcDiagonal(mountain));
        var newDiagonal;
        var yamakazi=diagonal[0][diagonal[0].length-1].value==1; //Yamakazi-Funka dualilty
        if (yamakazi){
          newDiagonal=cloneMountain(diagonal);
          newDiagonal[0].pop();
          for (var i=0;i<n;i++){__tick();
            for (var j=badRootSeam;j<mountain[0].length-1;j++){__tick();
              newDiagonal[0].push(newDiagonal[0][j]); //who cares about mountains in diagonal?
            }
          }
          cutHeight--;
          badRootHeight=cutHeight;
        }else{
          newDiagonal=expand(diagonal,n,false);
          badRootHeight=mountain.length-1;
          while (true){__tick();
            var i=0;
            while (mountain[badRootHeight][i]&&mountain[badRootHeight][i].position+badRootHeight<badRootSeam) {__tick();i++;}
            if (mountain[badRootHeight][i]&&mountain[badRootHeight][i].position+badRootHeight==badRootSeam) break;
            badRootHeight--;
          }
        }
        for (var i=0;i<=actualCutHeight;i++) {__tick();result[i].pop();} //cut child
        if (!result[result.length-1].length) result.pop();
        var afterCutHeight=result.length;
        var afterCutMountain=cloneMountain(result);
        var afterCutLength=result[0].length;
        var badRootSeamHeight=afterCutHeight-1;
        while (true){__tick();
          var l=0;
          while (mountain[badRootSeamHeight][l]&&mountain[badRootSeamHeight][l].position+badRootSeamHeight<badRootSeam) {__tick();l++;}
          if (mountain[badRootSeamHeight][l]&&mountain[badRootSeamHeight][l].position+badRootSeamHeight==badRootSeam) break;
          badRootSeamHeight--;
        }
        badRootSeamHeight++;
        //Create Mt.Fuji shell
        for (var i=1;i<=n;i++){__tick(); //iteration
          for (var j=badRootSeam;j<afterCutLength;j++){__tick(); //seam
            var isAscending;
            var p=0; //simplified; may not work
            while (mountain[badRootHeight][p].position+badRootHeight<j) {__tick();p++;}
            if (mountain[badRootHeight][p].position+badRootHeight==j){
              while (true){__tick();
                if (!mountain[badRootHeight][p]||mountain[badRootHeight][p].position+badRootHeight<badRootSeam){
                  isAscending=false;
                  break;
                }
                if (mountain[badRootHeight][p].position+badRootHeight==badRootSeam){
                  isAscending=true;
                  break;
                }
                p=mountain[badRootHeight][p].parentIndex;
              }
            }else{
              isAscending=false;
            }
            var seamHeight=afterCutHeight-1;
            while (true){__tick();
              var l=0;
              while (mountain[seamHeight][l]&&mountain[seamHeight][l].position+seamHeight<j) {__tick();l++;}
              if (mountain[seamHeight][l]&&mountain[seamHeight][l].position+seamHeight==j) break;
              seamHeight--;
            }
            seamHeight++;
            var isReplacingCut=j==badRootSeam;
            //console.log([j,seamHeight]);
            if (isAscending){
              for (var k=0;k<seamHeight+(cutHeight-badRootHeight)*i;k++){__tick();
                if (!result[k]) { if (result.length >= __limits.maxLayers) __budget("Y output row limit"); result.push([]); }
                if (k<badRootHeight){ //Bb
                  var sy=k;
                  var sx;
                  if (isReplacingCut){
                    sx=mountain[sy].length-1;
                  }else{
                    sx=0;
                    while (mountain[sy][sx].position+sy<j) {__tick();sx++;}
                  }
                  var sourceParentIndex=mountain[sy][sx].parentIndex;
                  var parentShifts=i-isReplacingCut;
                  var parentPosition=mountain[sy][sourceParentIndex]?mountain[sy][sourceParentIndex].position+parentShifts*(afterCutLength-badRootSeam)*(mountain[sy][sourceParentIndex].position+sy>=badRootSeam)-(k-sy):-1;
                  var parentIndex=0;
                  while (result[k][parentIndex]&&result[k][parentIndex].position<parentPosition) {__tick();parentIndex++;}
                  if (!result[k][parentIndex]||result[k][parentIndex].position!=parentPosition) parentIndex=-1;
                  result[k].push({
                    value:parentIndex==-1?newDiagonal[0][j+(afterCutLength-badRootSeam)*i].value:NaN,
                    position:j+(afterCutLength-badRootSeam)*i-k,
                    parentIndex:parentIndex,
                    forcedParent:mountain[sy][sx].forcedParent
                  });
                }else if (k<=badRootHeight+(cutHeight-badRootHeight)*(i-isReplacingCut)){ //Br replace
                  var sy=badRootHeight;
                  var sx;
                  if (!yamakazi&&isReplacingCut){
                    sx=mountain[sy].length-1;
                  }else{
                    sx=0;
                    while (mountain[sy][sx].position+sy<j) {__tick();sx++;}
                  }
                  var sourceParentIndex=mountain[sy][sx].parentIndex;
                  var parentShifts=i-isReplacingCut;
                  var parentPosition=mountain[sy][sourceParentIndex]?mountain[sy][sourceParentIndex].position+parentShifts*(afterCutLength-badRootSeam)*(mountain[sy][sourceParentIndex].position+sy>=badRootSeam)-(k-sy):-1;
                  var parentIndex=0;
                  while (result[k][parentIndex]&&result[k][parentIndex].position<parentPosition) {__tick();parentIndex++;}
                  if (!result[k][parentIndex]||result[k][parentIndex].position!=parentPosition) parentIndex=-1;
                  result[k].push({
                    value:parentIndex==-1?newDiagonal[0][j+(afterCutLength-badRootSeam)*i].value:NaN,
                    position:j+(afterCutLength-badRootSeam)*i-k,
                    parentIndex:parentIndex,
                    forcedParent:mountain[sy][sx].forcedParent
                  });
                }else if (isReplacingCut&&k<=badRootHeight+(cutHeight-badRootHeight)*i){ //Br extend
                  var sy=k-(cutHeight-badRootHeight)*(i-1);
                  var sx;
                  if (!yamakazi&&isReplacingCut){
                    sx=mountain[sy].length-1;
                  }else{
                    sx=0;
                    while (mountain[sy][sx].position+sy<j) {__tick();sx++;}
                  }
                  var sourceParentIndex=mountain[sy][sx].parentIndex;
                  var parentShifts=i-isReplacingCut;
                  var parentPosition=mountain[sy][sourceParentIndex]?mountain[sy][sourceParentIndex].position+parentShifts*(afterCutLength-badRootSeam)*(mountain[sy][sourceParentIndex].position+sy>=badRootSeam)-(k-sy):-1;
                  var parentIndex=0;
                  while (result[k][parentIndex]&&result[k][parentIndex].position<parentPosition) {__tick();parentIndex++;}
                  if (!result[k][parentIndex]||result[k][parentIndex].position!=parentPosition) parentIndex=-1;
                  result[k].push({
                    value:parentIndex==-1?newDiagonal[0][j+(afterCutLength-badRootSeam)*i].value:NaN,
                    position:j+(afterCutLength-badRootSeam)*i-k,
                    parentIndex:parentIndex,
                    forcedParent:mountain[sy][sx].forcedParent
                  });
                }else{ //Be
                  //if (isReplacingCut) console.warn("Climbing doesn't all the way. Makes sense.");
                  var sy=k-(cutHeight-badRootHeight)*i;
                  var sx;
                  if (!yamakazi&&isReplacingCut){
                    sx=mountain[sy].length-1;
                  }else{
                    sx=0;
                    while (mountain[sy][sx].position+sy<j) {__tick();sx++;}
                  }
                  var sourceParentIndex=mountain[sy][sx].parentIndex;
                  var parentShifts=i-isReplacingCut;
                  var parentPosition=mountain[sy][sourceParentIndex]?mountain[sy][sourceParentIndex].position+parentShifts*(afterCutLength-badRootSeam)*(mountain[sy][sourceParentIndex].position+sy>=badRootSeam)-(k-sy):-1;
                  var parentIndex=0;
                  while (result[k][parentIndex]&&result[k][parentIndex].position<parentPosition) {__tick();parentIndex++;}
                  if (!result[k][parentIndex]||result[k][parentIndex].position!=parentPosition) parentIndex=-1;
                  result[k].push({
                    value:parentIndex==-1?newDiagonal[0][j+(afterCutLength-badRootSeam)*i].value:NaN,
                    position:j+(afterCutLength-badRootSeam)*i-k,
                    parentIndex:parentIndex,
                    forcedParent:mountain[sy][sx].forcedParent
                  });
                }
              }
            }else{
              if (isReplacingCut) console.warn("Cut child and not connected to bad root. Makes sense.");
              for (var k=0;k<seamHeight;k++){__tick();
                if (!result[k]) { if (result.length >= __limits.maxLayers) __budget("Y output row limit"); result.push([]); }
                //if statement is here to line up indents
                if (true){ //Bb
                  var sy=k;
                  var sx;
                  if (isReplacingCut){
                    sx=mountain[sy].length-1;
                  }else{
                    sx=0;
                    while (mountain[sy][sx].position+sy<j) {__tick();sx++;}
                  }
                  var sourceParentIndex=mountain[sy][sx].parentIndex;
                  var parentShifts=i-isReplacingCut;
                  var parentPosition=mountain[sy][sourceParentIndex]?mountain[sy][sourceParentIndex].position+parentShifts*(afterCutLength-badRootSeam)*(mountain[sy][sourceParentIndex].position+sy>=badRootSeam)-(k-sy):-1;
                  var parentIndex=0;
                  while (result[k][parentIndex]&&result[k][parentIndex].position<parentPosition) {__tick();parentIndex++;}
                  if (!result[k][parentIndex]||result[k][parentIndex].position!=parentPosition) parentIndex=-1;
                  result[k].push({
                    value:parentIndex==-1?newDiagonal[0][j+(afterCutLength-badRootSeam)*i].value:NaN,
                    position:j+(afterCutLength-badRootSeam)*i-k,
                    parentIndex:parentIndex,
                    forcedParent:mountain[sy][sx].forcedParent
                  });
                }
              }
            }
          }
        }
      }
      //Build number from ltr, ttb
      for (var i=result.length-1;i>=0;i--){__tick();
        if (!result[i].length){
          result.pop();
          continue;
        }
        for (var j=0;j<result[i].length;j++){__tick();
          if (typeof result[i][j].value === "bigint") continue;
          var k=0; //find left-up
          while (result[i+1][k].position<result[i][j].position-1) {__tick();k++;}
          if (result[i+1][k].position!=result[i][j].position-1) throw Error("Mountain not complete");
          result[i][j].value=result[i][result[i][j].parentIndex].value+result[i+1][k].value; __checkValue(result[i][j].value);
        }
      }
      var rr;
      if (stringify){
        rr=[];
        for (var i=0;result[0]&&i<result[0].length;i++){__tick();
          rr.push(result[0][i].value+(result[0].forcedParent?"v"+result[0].parentIndex:""));
        }
        rr=rr.join(",");
      }else{
        rr=result;
      }
      return rr;
    }
    
  function __root(row, index) {
    for (let hops = 0; row[index].parentIndex >= 0; hops++) {
      __tick();
      if (hops >= __limits.maxWidth) __budget('Y browser ancestor traversal limit');
      const parent = row[index].parentIndex;
      if (!Number.isSafeInteger(parent) || parent < 0 || parent >= index) throw new RangeError('Invalid Y parent index');
      index = parent;
    }
    return index;
  }
  function fs(sequence, n) {
    __begin(); __validate(sequence);
    if (!Number.isSafeInteger(n) || n < 0) throw new RangeError('Y FS index must be a nonnegative safe integer');
    if (!sequence.length) return [];
    if (n === 0 || sequence.at(-1) === 1n) return sequence.slice(0, -1);
    const mountain = calcMountain(sequence.join(',')), x = mountain[0].length - 1;
    if (mountain[0][x].parentIndex >= 0) {
      const cut = getBadRoot(mountain);
      if (!Number.isSafeInteger(cut) || cut < 0 || cut >= x) throw new RangeError('Invalid Y bad root');
      if (BigInt(x) + BigInt(n) * BigInt(x - cut) > BigInt(__limits.maxWidth)) __budget('Y browser output width limit');
    }
    const result = __checkMountain(expand(mountain, n, false));
    const values = [];
    if (result[0]) for (const entry of result[0]) { __tick(); values.push(entry.value); }
    return values;
  }
  function diagram(sequence, genuineOnly = false) {
    __begin(); __validate(sequence);
    if (!sequence.length) return {size: 0, atoms: []};
    let mountain = calcMountain(sequence.join(','));
    const size = sequence.length, atoms = new Map();
    for (let k = 0; k < __limits.maxLayers; k++) {
      __tick();
      for (let r = 0; r < mountain.length; r++) {
        __tick(); const row = mountain[r];
        for (const entry of row) {
          __tick();
          if (entry.parentIndex < 0) continue;
          const root = __root(row, entry.parentIndex);
          const qMax = row[root].position + r, parent = row[entry.parentIndex].position + r, child = entry.position + r;
          if (!(0 <= qMax && qMax <= parent && parent < child && child < size)) throw new RangeError('Invalid Y canonical edge');
          for (let q = genuineOnly ? qMax : 0; q <= qMax; q++) {
            __tick(); const atom = [k, q, parent, child]; atoms.set(atom.join(','), atom);
            if (atoms.size > __limits.maxAtoms) __budget('Y browser atom limit');
          }
        }
      }
      mountain = calcMountain(calcDiagonal(mountain));
      let terminal = true;
      for (const entry of mountain[0]) { __tick(); if (entry.value !== 1n) { terminal = false; break; } }
      if (terminal) {
        const ordered = [...atoms.values()];
        ordered.sort((a, b) => { __tick(); for (let i = 0; i < 4; i++) { __tick(); if (a[i] !== b[i]) return a[i] - b[i]; } return 0; });
        return {size, atoms: ordered};
      }
    }
    __budget('Y browser canonical diagonal layer limit');
  }
  function control(sequence) {
    __begin(); __validate(sequence);
    if (!sequence.length || sequence.at(-1) === 1n) return null;
    let mountain = calcMountain(sequence.join(','));
    const x = sequence.length - 1;
    if (mountain[0][x].parentIndex < 0) return null;
    for (let k = 0; k < __limits.maxLayers; k++) {
      __tick(); const next = calcMountain(calcDiagonal(mountain));
      if (next[0].at(-1).value !== 1n) { mountain = next; continue; }
      let height = mountain.length - 1;
      while (height >= 0) {
        __tick(); let found = false;
        for (const entry of mountain[height]) { __tick(); if (entry.position + height === x) { found = true; break; } }
        if (found) break;
        height--;
      }
      if (height <= 0) throw new RangeError('Missing Y top edge');
      const r = height - 1, row = mountain[r]; let entry;
      for (const candidate of row) { __tick(); if (candidate.position + r === x) { entry = candidate; break; } }
      if (!entry || entry.parentIndex < 0) throw new RangeError('Missing Y control parent');
      const parent = entry.parentIndex, root = __root(row, parent);
      return [k, row[root].position + r, row[parent].position + r, x];
    }
    __budget('Y browser control diagonal layer limit');
  }
  return {fs, diagram, genuine: sequence => diagram(sequence, true), control};
}

const browserY=createBrowserYEngine({maxWidth:96,maxLayers:100,maxAtoms:120000,maxWork:1500000,timeoutMs:120});
function equal(a,b){
  if(a===b)return true;
  if(!a||!b||typeof a!=='object'||typeof b!=='object'||Array.isArray(a)!==Array.isArray(b))return false;
  const keys=Object.keys(a);return keys.length===Object.keys(b).length&&keys.every(k=>Object.prototype.hasOwnProperty.call(b,k)&&equal(a[k],b[k]));
}
function assert(ok,message){if(!ok)throw Error('Embedding assertion: '+(message||'invariant'));}
assert.equal=(a,b,message)=>assert(a===b,message||'equal');
assert.deepEqual=(a,b,message)=>assert(equal(a,b),message||'deep equality');
const nat=n => n ? [{exp: [], coeff: n}] : [];
function ocmp(a, b) {
  for (let i = 0; i < Math.min(a.length, b.length); i++) {
    const c = ocmp(a[i].exp, b[i].exp);
    if (c) return c;
    if (a[i].coeff !== b[i].coeff) return Math.sign(a[i].coeff - b[i].coeff);
  }
  return Math.sign(a.length - b.length);
}
function ancestry(h, threshold) {
  const sets = [];
  for (const col of h) {
    const own = new Set();
    for (const {a, x} of col) if (ocmp(x, threshold) >= 0) {
      own.add(a - 1);
      for (const p of sets[a - 1]) own.add(p);
    }
    sets.push(own);
  }
  return sets;
}
function normalizeAt(h, tau, emit = () => {}) {
  const col = h.at(-1), i = col.findIndex(e => ocmp(e.x, tau) >= 0);
  assert(i >= 0, 'requested threshold exists');
  const out = [...h.slice(0, -1), [...col.slice(0, i), {a: col[i].a, x: tau}]];
  if (JSON.stringify(out) !== JSON.stringify(h)) emit({kind: 'macro', before: h, after: out});
  return out;
}
function expose(h, parent, tau, emit = () => {}) {
  assert(ancestry(h, tau).at(-1).has(parent), 'requested ancestor exists');
  let out = h;
  for (let rounds = 0; rounds < h.length; rounds++) {
    out = normalizeAt(out, tau, emit);
    const control = out.at(-1).at(-1);
    assert(control.a >= parent + 1);
    if (control.a === parent + 1) return out;
    const next = M.debug.down(out);
    emit({kind: 'down', before: out, after: next});
    out = next;
  }
  throw new Error('exposure did not strictly reduce the parent');
}
const cover={M,nat,ocmp,ancestry,normalizeAt,expose};
const definitions={"direct":function(require,module){
'use strict';

// Source-only acceleration: retain true row roots rather than their entire
// downward closure. Every expansion still runs Naruyoko's original Y rules.
const assert = require('assert');
const createYEngine = () => browserY;
const Y = createYEngine({maxWidth: 96, maxLayers: 100, maxAtoms: 120000, timeoutMs: 500});

function encode(values) {
  const g = Y.genuine(values);
  return {...g, values: values.slice()};
}
const G = {
  realEdges(g) { return g.atoms; },
  control(g) {
    let ctrl = null;
    for (const edge of g.atoms) if (edge[3] === g.size - 1) ctrl = edge;
    return ctrl;
  },
  fs(g, n) { return encode(Y.fs(g.values, n)); },
};

function parents(g) {
  const heights = Array(g.size).fill(0);
  for (const [k,,,j] of g.atoms) if (!k) heights[j]++;
  const p = heights.map(h => ({parents: Array(h).fill(null), high: null}));
  for (const [k,q,f,j] of g.atoms) {
    if (!k) {
      const row = heights[q];
      assert(row < heights[j] && p[j].parents[row] === null);
      p[j].parents[row] = f;
    } else {
      assert(k === 1 && q === f && p[j].high === null, 'flat high stars');
      p[j].high = f;
    }
  }
  assert(p.every(v => v.parents.every(x => x !== null)));
  return p;
}

module.exports = {Y, G, encode, parents};

},
"banded":function(require,module){
'use strict';

// A marked source class, checked against the original numerical Y.
// Marks are inherited under copy; they are not recomputed after a step.
const assert=require('assert'),D=require('direct');
function rowAncestor(ps,p,j,row){
  let a=j;while(a>p&&ps[a].parents.length>row)a=ps[a].parents[row];return a===p;
}
function mark(g){const b=Array(g.size).fill(false);for(const [,q] of g.atoms)b[q]=true;return b;}
function inspect(g,base){
  const ps=D.parents(g);assert.equal(base.length,g.size);
  for(const [,q] of g.atoms)assert(base[q],'genuine root is marked');
  for(let j=0;j<g.size;j++){
    const p=ps[j];
    for(let r=1;r<p.parents.length;r++)assert.equal(ps[p.parents[r]].high,null,'upper parent is not a tip');
    if(p.high===null)continue;
    const c=p.high,h=ps[c].parents.length;
    assert(!base[j]&&base[c],'tips unmarked, their roots marked');
    assert(p.parents.every(v=>v===c)&&p.parents.length===h+1,'uniform high tip');
    for(let v=c+1;v<j;v++){
      if(!h)assert.equal(ps[v].high,c,'height-zero star has only pure tips inside');
      let a=v;while(a>c&&ps[a].high!==c&&ps[a].parents.length)a=ps[a].parents[0];
      assert(a>c&&ps[a].high===c,'star interval is a band of same-root tip subtrees');
    }
    const zeroDesc=[];
    for(let v=j+1;v<g.size;v++)if(rowAncestor(ps,j,v,0)){
      if(!h)zeroDesc.push(v);
      if(rowAncestor(ps,c,v,h)){
        assert(!base[v],'no marked root in tip potential');
        // Consequence of root marking and the no-upper-tip condition. Keep it
        // explicit as an independently checked finite version of the lemma.
        assert.equal(ps[v].parents.length,h+1,'potential has exactly one live upper row');
      }
    }
    if(!h&&zeroDesc.length){
      assert.deepEqual(zeroDesc,[j+1],'zero tip has at most one immediate leaf');
      assert(!base[j+1]);assert.deepEqual(ps[j+1],{parents:[j],high:null});
    }
  }
  return ps;
}
function nextMarks(g,base,n){
  const x=g.size-1,ctrl=D.G.control(g),out=base.slice(0,x);
  if(n&&ctrl)for(let b=1;b<=n;b++)out.push(...base.slice(ctrl[2],x));
  return out;
}
function expected(g,base,n){
  const ps=inspect(g,base),x=g.size-1,out=ps.slice(0,x).map(p=>({parents:p.parents.slice(),high:p.high}));
  const ctrl=D.G.control(g);if(!n||!ctrl)return out;
  const high=!!ctrl[0],cut=ctrl[2],span=x-cut,row=ps[x].parents.length-1,h=ps[cut].parents.length;
  for(let b=1;b<=n;b++)for(let j=cut;j<x;j++){
    const move=p=>p<cut?p:p+b*span,previous=p=>p<cut?p:p+(b-1)*span;
    let p={parents:ps[j].parents.map(move),high:ps[j].high===null?null:move(ps[j].high)};
    if(high){
      if(j===cut)p={parents:Array(h+b).fill(cut+(b-1)*span),high:null};
      else if(rowAncestor(ps,cut,j,h)){
        assert(!base[j]&&ps[j].parents.length===h+1,'only one-row unmarked columns ascend');
        p.parents=ps[j].parents.slice(0,h).map(move).concat(Array(b+1).fill(move(ps[j].parents[h])));
      }
    }else if(j===cut)for(let u=0;u<row;u++)p.parents[u]=previous(ps[x].parents[u]);
    out.push(p);
  }
  return out;
}
module.exports={D,rowAncestor,mark,inspect,nextMarks,expected};

},
"graded":function(require,module){
'use strict';

// Finite-depth graded-band protocol; paper proof in
// Y13425712-GRADED-BAND-BOUND.zh-CN.md. Bounded tests remain diagnostics,
// not a replacement for its owner-transport and closure arguments.
const assert=require('assert'),S=require('banded');
const {D,rowAncestor,mark,nextMarks}=S;
const A=require('unused');
const top=[1n,3n,4n,2n,5n,7n,12n];
function inspect(g,base,d){
  const ps=D.parents(g),roots=new Set(ps.filter(p=>p.high!==null).map(p=>p.high));
  const owner=Array(g.size).fill(null);assert.equal(base.length,g.size);
  for(const [,q] of g.atoms)assert(base[q],'genuine root marked');
  for(let t=0;t<g.size;t++){
    const p=ps[t];for(let r=1;r<p.parents.length;r++)assert.equal(ps[p.parents[r]].high,null,'upper parent not tip');
    if(p.high===null)continue;const c=p.high,h=ps[c].parents.length;
    assert(!base[t]&&base[c]);assert(p.parents.every(a=>a===c)&&p.parents.length===h+1,'uniform tip');
    for(let v=c+1;v<t;v++){
      if(!h)assert.equal(ps[v].high,c,'pure zero-star band');
      let a=v;while(a>c&&ps[a].high!==c&&ps[a].parents.length)a=ps[a].parents[0];
      assert(a>c&&ps[a].high===c,'band condition');
    }
    const zero=[];
    for(let j=t+1;j<g.size;j++)if(rowAncestor(ps,t,j,0)){
      if(!h)zero.push(j);
      if(rowAncestor(ps,c,j,h)){
        assert(!roots.has(j),'no live high root in another potential');
        if(base[j])assert(ps[j].parents.length<=h+d,'finite marked depth');
        assert(ps[j].parents.length<=h+d+1,'derived body height bound');
        assert(owner[j]===null||owner[j]===c,'unique potential owner');owner[j]=c;
      }
    }
    if(!h&&zero.length){assert.deepEqual(zero,[t+1]);assert(!base[t+1]);
      assert.deepEqual(ps[t+1],{parents:[t],high:null});}
  }
  for(let j=0;j<g.size;j++)if(ps[j].high!==null)assert.equal(owner[j],null,'a uniform tip has no other owner');
  return {ps,owner,roots};
}
function expected(g,base,d,n){
  const {ps}=inspect(g,base,d),x=g.size-1,ctrl=D.G.control(g);
  const out=ps.slice(0,x).map(p=>({parents:p.parents.slice(),high:p.high}));if(!n||!ctrl)return out;
  const high=!!ctrl[0],c=ctrl[2],span=x-c,h=ps[c].parents.length,row=ps[x].parents.length-1;
  for(let b=1;b<=n;b++)for(let j=c;j<x;j++){
    const move=p=>p<c?p:p+b*span,prev=p=>p<c?p:p+(b-1)*span;
    let p={parents:ps[j].parents.map(move),high:ps[j].high===null?null:move(ps[j].high)};
    if(high){
      if(j===c)p={parents:Array(h+b).fill(c+(b-1)*span),high:null};
      else if(rowAncestor(ps,c,j,h))p.parents=ps[j].parents.slice(0,h).map(move)
        .concat(Array(b+1).fill(move(ps[j].parents[h])),ps[j].parents.slice(h+1).map(move));
    }else if(j===c)for(let u=0;u<row;u++)p.parents[u]=prev(ps[x].parents[u]);
    out.push(p);
  }
  return out;
}
function pump(s,required,extraCloser=false){
  const span=s.pos.at(-1)+(extraCloser?1n:0n)-s.anchor,need=BigInt(required)-s.anchor;
  const n=need>0n?(need+span-1n)/span:0n,delta=n*span;if(!n)return {...s,lastPump:0n};
  return {...s,pos:s.pos.map(p=>p+delta),caps:s.caps.map(a=>a.map(q=>q>s.anchor?q+delta:q)),
    anchor:s.anchor+delta,reserve:s.reserve+delta,lastPump:n};
}
function check(s){
  const {ps,owner,roots}=inspect(s.source,s.base,s.d),H=s.anchor+BigInt(s.d+2);
  assert(s.anchor>=BigInt(Math.max(0,...ps.map(p=>p.parents.length))),'anchor above ordinary heights');
  if(!s.source.size){assert.equal(s.pos.length,0);return {ps,owner,roots};}
  assert.equal(s.pos.length,1+2*s.source.size);assert.equal(s.pos[0],s.anchor);
  for(let j=0;j<ps.length;j++){
    const a=1+2*j;assert(s.pos[a]>H);assert(s.caps[a][0]>=1n&&s.caps[a+1][0]>=1n);
    for(let r=0;r<ps[j].parents.length;r++){
      const cap=s.caps[a][1+2*ps[j].parents[r]];assert(cap>=BigInt(r+1),'literal ordinary coverage');
      if(owner[j]!==null){const h=ps[owner[j]].parents.length;
        if(r>=h)assert(cap>=s.anchor+1n+BigInt(r-h),`graded coverage ${j},${r}`);}
    }
    if(!s.base[j]&&ps[j].parents.length)assert(s.caps[a][1+2*ps[j].parents.at(-1)]>=H,'body top H');
    if(ps[j].high!==null)assert(s.caps[a][1+2*ps[j].high]>=H,'high H');
  }
  return {ps,owner,roots};
}
function initialize(n){
  const values=D.Y.fs(top,n),d=n;let s={...A.initialize(values,d+4),d};
  // Initialization pumps at ONE EXTRA closing column. The representation's
  // own final auxiliary column must lie inside, not be the deleted controller.
  s=pump(s,Math.max(0,...D.parents(s.source).map(p=>p.parents.length)),true);check(s);return s;
}
function initializeFixed(n){
  const source=D.encode(D.Y.fs(top,n)),d=n,w=source.size;
  // D4[2w+1]: two extra columns after the representation's final auxiliary.
  // Pump at column 2, retain the last copy. One extra column survives.
  const z=BigInt(2*w+5),L=z-2n;
  const growth=(BigInt(d)+L-1n)/L,delta=growth*L;
  const z1=z-1n+delta,required=BigInt(Math.max(0,...D.parents(source).map(p=>p.parents.length)));
  const common=(required-1n+z1-2n)/(z1-1n),delta2=common*(z1-1n);
  const anchor=1n+delta2,Q=3n+delta+delta2;
  const pos=[anchor];for(let j=0;j<w;j++){const p=4n+2n*BigInt(j)+delta+delta2;pos.push(p,p+1n);}
  const caps=pos.map((_,j)=>Array.from({length:j},(_,p)=>p===0?1n:Q));
  const s={source,d,base:mark(source),anchor,reserve:anchor+1n,pos,caps,
    initialization:{growth,common,Q}};check(s);return s;
}
function step(s,n){
  const {ps,owner}=check(s),w=s.source.size;if(!w)return s;
  const ctrl=D.G.control(s.source),source=D.G.fs(s.source,n),base=nextMarks(s.source,s.base,n);
  assert.deepEqual(D.parents(source),expected(s.source,s.base,s.d,n),'independent general high/ordinary formula');
  if(!n||!ctrl){const width=w>1?s.pos.length-2:0;
    const t={...s,source,base,pos:s.pos.slice(0,width),caps:s.caps.slice(0,width),lastPump:0n};check(t);return t;}
  let t=s;if(ctrl[0])t=pump(t,Math.max(0,...D.parents(source).map(p=>p.parents.length)));
  t={...t,pos:t.pos.slice(0,-1),caps:t.caps.slice(0,-1).map(a=>a.slice())};
  const row=ps[w-1].parents.length-1,own=owner[w-1];let threshold;
  if(ctrl[0]||!s.base[w-1])threshold=t.anchor+BigInt(s.d+2);
  else if(own!==null&&row>=ps[own].parents.length)threshold=t.anchor+1n+BigInt(row-ps[own].parents.length);
  else threshold=BigInt(row+1);
  const cut=1+2*ctrl[2];assert(t.caps.at(-1)[cut]>=threshold,'required controller');
  t=A.copy(t,cut,n,threshold);t.source=source;t.base=base;check(t);return t;
}
module.exports={D,A,top,inspect,expected,initialize,initializeFixed,check,step,pump};

},
"real":function(require,module){
'use strict';
// REAL M version of the graded protocol. No rule substitutions.
const assert=require('assert'),G=require('graded');
const F=require('greedy');
const S=require('banded');
const {M,D,nat,expose,capacity}=F;
function check(s){
  const r=G.inspect(s.source,s.base,s.d),H=s.anchor+s.d+2;
  assert(s.anchor>=Math.max(0,...r.ps.map(p=>p.parents.length)));
  assert(M.debug.isLegalExpr(s.target));
  if(!s.source.size){assert.equal(s.target.length,s.floor||0);return r;}
  assert.equal(s.target.length,s.points.at(-1)+1);
  for(let j=0;j<r.ps.length;j++){
    const a=s.points[j],p=r.ps[j];assert(a>H);
    assert(capacity(s.target,s.anchor-1,a-1)>=1&&capacity(s.target,s.anchor-1,a)>=1);
    for(let u=0;u<p.parents.length;u++){
      const cap=capacity(s.target,s.points[p.parents[u]]-1,a-1);assert(cap>=u+1);
      if(r.owner[j]!==null){const h=r.ps[r.owner[j]].parents.length;
        if(u>=h)assert(cap>=s.anchor+1+u-h,`graded ${j},${u}`);}
    }
    if(!s.base[j]&&p.parents.length)assert(capacity(s.target,s.points[p.parents.at(-1)]-1,a-1)>=H,'body H');
    if(p.high!==null)assert(capacity(s.target,s.points[p.high]-1,a-1)>=H,'high H');
  }
  return r;
}
function initialize(n,emit=()=>{}){
  const source=D.encode(D.Y.fs(G.top,n)),d=n,height=d+4,w=source.size;
  const seed=M.FS(M.debug.parseExpr('()(1:ω)'),height);let target=M.FS(seed,2*w);
  emit({kind:'FS',before:seed,after:target,n:2*w});
  let anchor=1,points=Array.from({length:w},(_,j)=>height+2*j);
  const required=Math.max(0,...D.parents(source).map(p=>p.parents.length)),span=target.length-anchor;
  const pump=Math.max(0,Math.ceil((required-anchor)/span));
  // The extra final column controls this pump; all per-column auxiliaries are
  // retained inside the bad block. FS(0) also gives the unpumped representation.
  if(pump)target=expose(target,anchor-1,nat(1),emit);
  const before=target;target=M.FS(target,pump);emit({kind:'FS',before,after:target,n:pump});
  anchor+=pump*span;points=points.map(p=>p+pump*span);
  const s={source,d,base:S.mark(source),anchor,points,target,seed};
  check(s);return s;
}
function initializeFixed(n,emit=()=>{}){
  const source=D.encode(D.Y.fs(G.top,n)),d=n,w=source.size;
  const seed=M.FS(M.debug.parseExpr('()(1:ω)'),4);let target=M.FS(seed,2*w+1);
  emit({kind:'FS',before:seed,after:target,n:2*w+1});
  const fs=k=>{const before=target;target=M.FS(target,k);emit({kind:'FS',before,after:target,n:k});};
  const span=target.length-2,growth=Math.ceil(d/span),delta=growth*span;
  if(growth)target=expose(target,1,nat(1),emit);fs(growth);
  let anchor=1,points=Array.from({length:w},(_,j)=>4+2*j+delta);
  // One extra column remains beyond the last selected auxiliary.
  assert.equal(target.length,points.at(-1)+2);
  const span2=target.length-1,required=Math.max(0,...D.parents(source).map(p=>p.parents.length));
  const common=Math.max(0,Math.ceil((required-anchor)/span2)),delta2=common*span2;
  if(common)target=expose(target,0,nat(1),emit);fs(common);
  anchor+=delta2;points=points.map(p=>p+delta2);
  const s={source,d,base:S.mark(source),anchor,points,target,seed,
    initialization:{growth,common,Q:3+delta+delta2}};check(s);return s;
}
function step(s,n,emit=()=>{}){
  const {ps,owner}=check(s),w=s.source.size;if(!w)return s;
  const c=D.G.control(s.source),source=D.G.fs(s.source,n);
  assert.deepEqual(D.parents(source),G.expected(s.source,s.base,s.d,n));
  const base=S.nextMarks(s.source,s.base,n);
  let {target,anchor}=s,points=s.points.slice(),next=points.slice(0,-1),lastPump=0;
  const fs=k=>{const before=target;target=M.FS(target,k);emit({kind:'FS',before,after:target,n:k});};
  if(n&&c){
    if(c[0]){
      const required=Math.max(0,...D.parents(source).map(p=>p.parents.length)),span=target.length-anchor;
      const k=Math.max(0,Math.ceil((required-anchor)/span)),delta=k*span;lastPump=k;
      if(k)target=expose(target,anchor-1,nat(1),emit);fs(k);
      if(k){anchor+=delta;points=points.map(p=>p+delta);}next=points.slice(0,-1);
    }else fs(0);
    const row=ps.at(-1).parents.length-1,own=owner.at(-1);let threshold;
    if(c[0]||!s.base[w-1])threshold=anchor+s.d+2;
    else if(own!==null&&row>=ps[own].parents.length)threshold=anchor+1+row-ps[own].parents.length;
    else threshold=row+1;
    const cut=c[2];target=expose(target,points[cut]-1,nat(threshold),emit);
    const span=target.length-points[cut];fs(n);
    for(let b=1;b<=n;b++)for(let j=cut;j<w-1;j++)next.push(points[j]+b*span);
  }
  const width=next.length?next.at(-1)+1:(s.floor||0);while(target.length>width)fs(0);
  const out={...s,source,base,target,points:next,anchor,lastPump};check(out);assert(M.compare(target,s.target)<0);return out;
}
module.exports={...F,G,initialize,initializeFixed,check,step};

},
"atomic":function(require,module){
'use strict';
// Opaque closed atoms inside the graded-band outer protocol. The internal
// ordinal bound is a PAPER relative-rank premise, not proved by this checker.
const assert=require('assert'),F=require('real');
const S=require('banded');
const {M,D,nat,capacity,expose}=F;
const word=m=>[1n,3n,4n,...Array.from({length:m},()=>[2n,5n,7n,12n]).flat()];
const diagonal=k=>M.FS(M.debug.parseExpr('()(1:ω)'),k);
function make(m){
  assert(Number.isSafeInteger(m)&&m>=1);
  const atom=word(m),aw=atom.length,H=diagonal(2*m+2),hw=H.length,L=hw+1,seed=diagonal(L);
  const ap=D.parents(D.encode(atom));
  const end=u=>u.a+(u.atom?hw-1:0),aux=u=>end(u)+1;
  function collapse(source){
    const ps=D.parents(source),units=[],index=Array(source.size).fill(null),interior=new Set();
    for(let j=0;j<source.size;){
      const isAtom=ps[j].parents.length===0,at=units.length;units.push({j,atom:isAtom});index[j]=at;
      if(isAtom){
        assert.deepEqual(source.values.slice(j,j+aw),atom,'closed atom unchanged');
        for(let k=0;k<aw;k++){
          assert.deepEqual(ps[j+k],{parents:ap[k].parents.map(p=>p+j),high:ap[k].high===null?null:ap[k].high+j});
          if(k)interior.add(j+k);
        }
      }
      j+=isAtom?aw:1;
    }
    const atoms=[];
    for(const [k,q,p,j] of source.atoms)if(!interior.has(j)){
      assert(!interior.has(q)&&!interior.has(p),'outer edges do not touch atom interiors');
      atoms.push([k,index[q],index[p],index[j]]);
    }
    const g={size:units.length,atoms};
    return {g,units,index,ps:D.parents(g)};
  }
  function check(s){
    const z=collapse(s.source),r=F.G.inspect(z.g,s.base,s.d),top=s.anchor+s.d+2;
    assert.deepEqual(s.units.map(({j,atom})=>({j,atom})),z.units);
    assert(s.anchor>=Math.max(0,...r.ps.map(p=>p.parents.length)));assert(M.debug.isLegalExpr(s.target));
    if(!s.units.length){assert.deepEqual(s.target,[[]]);return {...z,...r};}
    assert.equal(s.target.length,aux(s.units.at(-1)));
    const cap=(p,j)=>capacity(s.target,p-1,j-1);let previous=s.anchor;
    for(let j=0;j<s.units.length;j++){
      const u=s.units[j],p=r.ps[j];assert(u.a>previous);previous=aux(u);
      assert(cap(s.anchor,u.a)>=1&&cap(s.anchor,aux(u))>=1);
      if(u.atom){
        assert(!p.parents.length&&p.high===null&&s.base[j]);const offset=u.a-1;
        for(let col=0;col<H.length;col++)for(const e of H[col]){
          const row=e.x[0].coeff;assert(cap(offset+e.a,offset+col+1)>=(row===1?1:offset+row),'relative atom coverage');
        }
      }else{
        assert(u.a>top);assert(p.parents.length>0);
        for(let row=0;row<p.parents.length;row++){
          const q=cap(s.units[p.parents[row]].a,u.a);assert(q>=row+1);
          if(r.owner[j]!==null&&row>=r.ps[r.owner[j]].parents.length)
            assert(q>=s.anchor+1+row-r.ps[r.owner[j]].parents.length,'outer graded coverage');
        }
        if(!s.base[j])assert(cap(s.units[p.parents.at(-1)].a,u.a)>=top,'outer body H');
        if(p.high!==null)assert(cap(s.units[p.high].a,u.a)>=top,'outer high H');
      }
    }
    return {...z,...r};
  }
  function initialize(n,emit=()=>{}){
    const source=D.encode(D.Y.fs(word(m+1),n)),z=collapse(source),d=n,v=z.units.length-1;
    const base=S.mark(z.g);for(let j=0;j<z.units.length;j++)if(z.units[j].atom)base[j]=true;
    let target=M.FS(seed,2*v+3);emit({kind:'FS',before:seed,after:target,n:2*v+3});
    const fs=k=>{const before=target;target=M.FS(target,k);emit({kind:'FS',before,after:target,n:k});};
    let units=z.units.map((u,j)=>({...u,a:j?L+2*j:2}));
    // The template ends at L, its auxiliary is L+1, and the first outer
    // point is L+2. Two final extra columns are used by the two pumps.
    const span=target.length-2,growth=Math.max(0,Math.ceil((d+3-(L-1))/span)),delta=growth*span;
    if(growth)target=expose(target,1,nat(1),emit);fs(growth);units=units.map(u=>({...u,a:u.a+delta}));
    assert.equal(target.length,aux(units.at(-1))+1,'one extra column before common pump');
    const required=Math.max(0,...z.ps.map(p=>p.parents.length)),span2=target.length-1;
    const common=Math.max(0,Math.ceil((required-1)/span2)),delta2=common*span2;
    if(common)target=expose(target,0,nat(1),emit);fs(common);units=units.map(u=>({...u,a:u.a+delta2}));
    const s={source,units,base,d,anchor:1+delta2,target};check(s);return s;
  }
  function step(s,n,emit=()=>{}){
    const r=check(s),w=s.units.length,last=s.units.at(-1);assert(!last.atom,'rank handoff, not an outer step');
    const source=D.G.fs(s.source,n),child=collapse(source),c=D.G.control(r.g);
    assert.deepEqual(child.ps,F.G.expected(r.g,s.base,s.d,n),'outer parent formula after atom collapse');
    const base=S.nextMarks(r.g,s.base,n);let {target,anchor}=s,units=s.units.map(u=>({...u})),next=units.slice(0,-1);
    const fs=k=>{const before=target;target=M.FS(target,k);emit({kind:'FS',before,after:target,n:k});};
    const trim=k=>{assert(k>=1&&target.length>=k);while(target.length>k)fs(0);};let pump=0;
    if(n&&c){
      if(c[0]){
        const span=target.length-anchor,required=Math.max(0,...child.ps.map(p=>p.parents.length));
        pump=Math.max(0,Math.ceil((required-anchor)/span));const delta=pump*span;
        if(pump)target=expose(target,anchor-1,nat(1),emit);fs(pump);
        if(pump){anchor+=delta;units=units.map(u=>({...u,a:u.a+delta}));}next=units.slice(0,-1);
      }else fs(0);
      const row=r.ps.at(-1).parents.length-1,own=r.owner.at(-1);
      const q=c[0]||!s.base[w-1]?anchor+s.d+2:
        own!==null&&row>=r.ps[own].parents.length?anchor+1+row-r.ps[own].parents.length:row+1;
      const cut=c[2];target=expose(target,units[cut].a-1,nat(q),emit);
      const span=target.length-units[cut].a,sourceSpan=s.source.size-1-units[cut].j;fs(n);
      for(let b=1;b<=n;b++)for(const u of units.slice(cut,-1))next.push({...u,j:u.j+b*sourceSpan,a:u.a+b*span});
    }
    trim(next.length?aux(next.at(-1)):1);
    const out={...s,source,units:next,base,target,anchor,lastPump:pump};check(out);assert(M.compare(target,s.target)<0);return out;
  }
  function innerSnapshot(s){
    check(s);const u=s.units.at(-1);assert(u.atom);const d=u.a-1;
    return {source:H,target:s.target.slice(0,d+hw),d,prefix:s.target.slice(0,d),floor:s.target.slice(0,d+1)};
  }
  function finishAtomForOuterTest(s,emit=()=>{}){
    // Boundary test only. Full source-atom rank comes from the induction.
    const u=s.units.at(-1);assert(u.atom);let target=s.target;
    const source=D.encode(s.source.values.slice(0,-aw)),units=s.units.slice(0,-1),base=s.base.slice(0,-1);
    const width=units.length?aux(units.at(-1)):1;
    while(target.length>width){const before=target;target=M.FS(target,0);emit({kind:'FS',before,after:target,n:0});}
    const out={...s,source,units,base,target};check(out);return out;
  }
  return {...F,m,atom,H,hw,L,seed,word,collapse,check,initialize,step,innerSnapshot,finishAtomForOuterTest};
}
module.exports={make,word};

},
"relative":function(require,module){
'use strict';

// Unlike the earlier closed-component lemma, outside-prefix references are
// allowed. The prefix stays fixed; coverage concerns only active endpoints.
const assert=require('assert');
const C=require('cover');
const {M,nat,ancestry,expose}=C;
const value=x=>{
  assert(x.length===1&&!x[0].exp.length&&x[0].coeff>0);return x[0].coeff;
};
const shift=(r,d)=>r===1?1:r+d;
function check(s) {
  const {source,target,d,prefix}=s;
  assert.equal(target.length,d+source.length);
  assert.deepEqual(target.slice(0,d),prefix);
  assert(M.debug.isLegalExpr(source)&&M.debug.isLegalExpr(target));
  for(const col of [...source,...target])for(const e of col)assert(value(e.x)<=e.a);
  const cache=new Map();
  for(let j=0;j<source.length;j++)for(const e of source[j]) {
    const tau=shift(value(e.x),d);
    if(!cache.has(tau))cache.set(tau,ancestry(target,nat(tau)));
    assert(cache.get(tau)[d+j].has(d+e.a-1));
  }
}
function step(s,n,emit=()=>{}) {
  check(s);assert(s.source.length);
  const ctrl=s.source.at(-1).at(-1);let target=s.target;
  if(n&&ctrl)target=expose(target,s.d+ctrl.a-1,nat(shift(value(ctrl.x),s.d)),emit);
  const k=n&&ctrl?n:0,next=M.FS(target,k);
  emit({kind:'FS',before:target,after:next,n:k});
  const out={...s,source:M.FS(s.source,n),target:next};check(out);
  assert(M.compare(next,s.target)<0);return out;
}
module.exports={...C,check,step,shift};

},
"greedy":function(require,module){
'use strict';

// Experimental only: use the largest available threshold at ordinary controls.
// Unlike the rejected literal-row protocol, this does not deliberately discard
// stronger seams merely because the source control has a low ordinary height.
const assert = require('assert');
const C = require('cover');
const D = require('direct');
const {M, nat, ancestry, expose} = C;

function capacity(target, p, j) {
  // Zero-based endpoints; all tested rows are finite positive integers.
  const caps = Array(j + 1).fill(0); caps[p] = Infinity;
  for (let v = p + 1; v <= j; v++) for (const e of target[v]) {
    assert(e.x.length === 1 && !e.x[0].exp.length);
    caps[v] = Math.max(caps[v], Math.min(e.x[0].coeff, caps[e.a - 1] || 0));
  }
  return caps[j];
}
function check(s) {
  assert.equal(s.points.length, s.source.size);
  if (!s.source.size) { assert.equal(s.target.length, 0); return; }
  assert.equal(s.reserve, s.anchor + 1);
  assert.equal(s.target.length, s.points.at(-1) + 1);
  assert(M.debug.isLegalExpr(s.target));
  for (const col of s.target) for (const e of col)
    assert(e.x.length === 1 && !e.x[0].exp.length && e.x[0].coeff <= e.a, 'finite strict cone');
  const ps = D.parents(s.source);
  for (let j = 0; j < s.source.size; j++) {
    const a = s.points[j];
    assert(a > s.reserve);
    assert(capacity(s.target, s.anchor - 1, a - 1) >= 1);
    assert(capacity(s.target, s.anchor - 1, a) >= 1);
    ps[j].parents.forEach((p, r) =>
      assert(capacity(s.target, s.points[p] - 1, a - 1) >= r + 1, `ordinary ${j},${r}`));
    if (ps[j].high !== null)
      assert(capacity(s.target, s.points[ps[j].high] - 1, a - 1) >= s.reserve + 1, `high ${j}`);
  }
}
function initialize(values, seedHeight = 4) {
  const source = D.encode(values);
  const seed = M.FS(M.debug.parseExpr('()(1:ω)'), seedHeight);
  const target = M.FS(seed, 2 * source.size - 1);
  const s = {source, target, points: values.map((_, j) => seedHeight + 2 * j), anchor: 1, reserve: 2};
  check(s); return s;
}
function step(s, n, emit = () => {}, verify = true) {
  const x = s.source.size - 1;
  if (x < 0) return s;
  const ctrl = D.G.control(s.source), source = D.G.fs(s.source, n);
  let {target, anchor, reserve} = s, points = s.points.slice(), next = points.slice(0, -1);
  const fs = k => {
    const old = target; target = M.FS(target, k); emit({kind: 'FS', before: old, after: target, n: k});
  };
  if (n && ctrl) {
    if (ctrl[0]) {
      const required = Math.max(0, ...D.parents(source).map(p => p.parents.length)) + 1;
      const L = target.length - anchor;
      const pump = Math.max(0, Math.ceil((required - reserve) / L)), delta = pump * L;
      if (pump) target = expose(target, anchor - 1, nat(1), emit);
      fs(pump);
      if (pump) { anchor += delta; reserve += delta; points = points.map(p => p + delta); }
      next = points.slice(0, -1);
    } else fs(0);
    const cut = ctrl[2], parent = points[cut] - 1;
    const threshold = capacity(target, parent, target.length - 1);
    assert(threshold >= 1);
    target = expose(target, parent, nat(threshold), emit);
    const L = target.length - points[cut]; fs(n);
    for (let b = 1; b <= n; b++) for (let j = cut; j < x; j++) next.push(points[j] + b * L);
  }
  const width = next.length ? next.at(-1) + 1 : 0;
  assert(target.length >= width);
  while (target.length > width) fs(0);
  const t = {source, target, points: next, anchor, reserve};
  if (verify) check(t);
  assert(M.compare(target, s.target) < 0); return t;
}
module.exports = {...C, D, capacity, initialize, step, check};

},
"prototype":function(require,module){
'use strict';
// Canonical strict order embedding. The proof is ORDER-EMBEDDING.zh-CN.md.
// Mathematical coverage still relies on the preceding graded-band lemmas.
const assert = require('assert');
const F = require('real');
const A = require('atomic');
const R = require('relative');
const {M, D, nat, expose} = F;
const U = M.debug.parseExpr('()(1:ω)');
const E = [1n,3n,4n,2n,5n,7n,12n,3n];
const lex = (a,b) => {
  for (let j=0;j<Math.min(a.length,b.length);j++) if(a[j]!==b[j]) return a[j]<b[j]?-1:1;
  return Math.sign(a.length-b.length);
};
const diagonal = m => M.FS(U,2*m+2);

function converter(options={}) {
  let deadline, steps, lifted, maxWidth, nested;
  const tick = () => {
    assert(++steps < (options.maxSteps??20000),'canonical route step budget');
    assert(Date.now()<deadline,'canonical route time budget');
  };
  function leastIndex(a,x) {
    for(let n=0;n<=x.length+1;n++) {
      tick(); const b=D.Y.fs(a,n);
      if(lex(b,x)>=0) return n;
    }
    throw Error('No finite canonical branch found');
  }
  // Lift exact M moves through the relative-cover relation. A normalization
  // macro only reduces the final row; a down event is FS(1) then truncation.
  function lift(cover,e) {
    tick(); assert.deepEqual(cover.source,e.before);
    if(!cover.d && cover.source===cover.target) {
      if(options.audit)options.audit(e);
      maxWidth=Math.max(maxWidth,e.after.length);
      assert(e.after.length<1200,'target width budget');
      return {...cover,source:e.after,target:e.after};
    }
    let target=cover.target;
    const audit=options.audit??(()=>{});
    if(e.kind==='macro') {
      const control=e.after.at(-1).at(-1);
      target=expose(target,cover.d+control.a-1,nat(R.shift(control.x[0].coeff,cover.d)),audit);
    } else if(e.kind==='down') {
      target=R.step(cover,1,audit).target;
      while(target.length>cover.d+e.after.length){
        const before=target;target=M.FS(target,0);audit({kind:'FS',before,after:target,n:0});
      }
    } else {
      assert.equal(e.kind,'FS'); target=R.step(cover,e.n,audit).target;
    }
    const out={...cover,source:e.after,target};
    R.check(out); lifted++; maxWidth=Math.max(maxWidth,target.length);
    assert(target.length<1200,'target width budget');
    return out;
  }
  function within(m,x,initial,depth=0) {
    tick(); assert(depth<20,'atom recursion budget');
    const top=A.word(m); assert(lex(x,top)<=0);
    if(!x.length) return initial.target.slice(0,initial.d+1);
    if(!lex(x,top)) return initial.target;
    let cover=initial;
    const emit=e=>{cover=lift(cover,e);};
    const P=m===1?F:A.make(m-1);
    const n=leastIndex(top,x);
    let s=m===1?{...P.initializeFixed(n,emit),floor:1}:P.initialize(n,emit);
    for(;;) {
      tick(); assert(lex(s.source.values,x)>=0);
      if(!lex(s.source.values,x)) return cover.target;
      if(m>1 && s.units.at(-1)?.atom) {
        const u=s.units.at(-1),prefix=s.source.values.slice(0,u.j);
        if(lex(x,prefix)<=0) {
          s=P.finishAtomForOuterTest(s,emit); continue;
        }
        assert.deepEqual(x.slice(0,prefix.length),prefix);
        const z=P.innerSnapshot(s),d=cover.d+z.d;
        const next={source:z.source,target:cover.target.slice(0,d+z.source.length),d,
          prefix:cover.target.slice(0,d)};
        R.check(next);
        nested++;
        return within(m-1,x.slice(prefix.length),next,depth+1);
      }
      s=P.step(s,leastIndex(s.source.values,x),emit);
    }
  }
  function convert(x) {
    deadline=Date.now()+(options.ms??1500); steps=0; lifted=0; maxWidth=0; nested=0;
    assert(lex(x,E)<=0,'outside source bound');
    if(!x.length)return {target:[],steps:0,lifted:0,maxWidth:0};
    if(!lex(x,E))return {target:U,steps:0,lifted:0,maxWidth:2};
    let m=1;while(lex(x,A.word(m))>0){
      tick();m++;assert(m<=Math.ceil(x.length/4)+1,'input is not under any canonical top branch');
    }
    const source=diagonal(m),initial={source,target:source,d:0,prefix:[]};
    const target=within(m,x,initial);
    assert(M.compare(target,U)<0); assert(M.debug.isLegalExpr(target));
    return {target,steps,lifted,maxWidth,m,nested};
  }
  return {convert,leastIndex};
}
module.exports={converter,M,D,E,U,lex,diagonal};

}},cache={assert:{exports:assert},cover:{exports:cover},unused:{exports:{}}};
function require(name){
  if(cache[name])return cache[name].exports;
  if(!definitions[name])throw Error('Missing bundled module '+name);
  const module={exports:{}};cache[name]=module;definitions[name](require,module);return module.exports;
}
function installOrderEmbedding(P,Y,M) {
  const endpoint=P.E.join(','),engine=P.converter({ms:650,maxSteps:12000});
  const parse=raw=>{
    let text=String(raw).split('↦')[0].trim().replace(/^Y\s*/, '').replace(/^[【(\[]|[】)\]]$/g,'').trim();
    if(text==='Limit'||text==='顶端')text=endpoint;
    if(['','0','∅'].includes(text))return [];
    if(text.length>12000)throw Error('Y 输入过长');
    const parts=text.split(/[,，\s]+/);
    if(parts.length>96||parts.some(s=>!/^\d+$/.test(s)||s.length>1000))throw Error('Y 输入应为以逗号分隔的正整数，至多 96 列');
    const v=parts.map(BigInt);
    if(v[0]!==1n||v.some(n=>n<1n)||P.lex(v,P.E)>0)throw Error('输入不在本转换器的 Y 顶端以下');
    return v;
  };
  const rawOf=v=>v.join(',')||'0';
  const escape=s=>String(s).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;');
  const cache=new Map();let cacheChars=0,hits=0;
  function image(raw) {
    const key=rawOf(parse(raw));
    if(cache.has(key)){hits++;return cache.get(key).value;}
    let value;
    try {
      const r=engine.convert(parse(key));
      // A second, direct check of actual M order, independent of NER.compare.
      for(const [other,entry] of cache)if(entry.value.status==='ok'){
        if(M.compare(r.target,entry.value.target)!==P.lex(parse(key),parse(other)))
          throw Error('保序断言失败：'+key+' / '+other);
      }
      value={status:'ok',target:r.target,columns:r.target.length,nested:r.nested||0,
        list:M.debug.exprToPlain(r.target)||'0',
        counts:M.debug.countText(r.target,{maxMs:40,maxWork:80000})};
    } catch(error) {
      value={status:'unavailable',message:String(error.message??error),
        label:/budget|limit|超限|预算/i.test(String(error.message??error))?'映射计算超限':'未能转换（非标准输入或待审计错误）'};
    }
    const size=JSON.stringify(value).length;
    if(size<=1500000){
      while(cache.size&&(cache.size>=96||cacheChars+size>3000000)){
        const first=cache.keys().next().value;cacheChars-=cache.get(first).size;cache.delete(first);
      }
      cache.set(key,{value,size});cacheChars+=size;
    }
    return value;
  }
  function show(raw,mode) {
    const y=rawOf(parse(raw));if(mode==='y')return y;
    const result=image(y),target=result.status==='ok'?(mode.includes('list')?result.list:result.counts):'【'+result.label+'】';
    return mode.startsWith('pair')?'Y('+y+') ↦ M('+target+')':target;
  }
  function display(name,mode,input=true) {
    const d={name,plain:raw=>show(raw,mode),
      html:raw=>'<span style="font-family:inherit;white-space:normal" title="严格保序映射；不是等值换写，也不是同指标基本列">'+escape(show(raw,mode))+'</span>'};
    if(input)d.from_display=text=>rawOf(parse(text));
    return d;
  }
  const notation={
    id:'y-to-m13-order-embedding-20260920',name:'Y → M13（保序嵌入）',simple_name:'Y ↪ M13',
    init:()=>[endpoint,'1','0'],
    display:display('Y → M 计数','pair-count'),
    display_equiv:{
      'Y → M 列表':display('Y → M 列表','pair-list'),
      'Y 数列':display('Y 数列','y'),
      'M 计数':display('M 计数','count',false),
      'M 列表':display('M 列表','list',false),
    },
    is_limit:raw=>{const v=parse(raw);return !!v.length&&v.at(-1)>1n;},
    // The paper proves this equals M.compare(F(a), F(b)); no display timeout
    // can therefore change NER's order. debug.compare_images checks M directly.
    compare:(a,b)=>P.lex(parse(a),parse(b)),
    FS:(raw,n)=>{
      if(!Number.isSafeInteger(n)||n<0||n>96)throw Error('基本列指标超限（0..96）');
      return rawOf(Y.fs(parse(raw),n));
    },
    description:[
      '源顶端为 Y(1,3,4,2,5,7,12,3)，12 是单个整数十二；它映到普通 e0MN 的 M13=()(1:ω)。',
      '只对该顶端的标准后代承诺映射。全部严格小于源顶端的式子，映像都严格小于 M13。',
      '点击仍按原 Y 基本列展开；箭头右边是固定、严格保序的 M 像，不是等值换写，不是同指标基本列。',
      '同一 Y 数列的映像不依赖点击路径。保序纸面证明与源码一起交付，尚未 Lean 形式化。',
      '一次映射约 650ms 预算，最大目标 1200 列；超限仅隐藏映像，Y 仍可展开。不会用猜测值或秩上界替代。',
      '计数若超限，保留已算出的数字，其余显示 ?；“M 列表”显示完整精确的目标式。',
    ],
    debug:{image,parse,source:Y,target:M,endpoint,
      compare_images:(a,b)=>{
        const x=image(a),y=image(b);if(x.status!=='ok'||y.status!=='ok')throw Error('映像未算出，不能核验目标比较');
        const c=M.compare(x.target,y.target);if(c!==P.lex(parse(a),parse(b)))throw Error('保序断言失败');return c;
      },
      clear_cache:()=>{cache.clear();cacheChars=0;},
      cache_stats:()=>({entries:cache.size,chars:cacheChars,hits}),
    },
  };
  return notation;
}
register(installOrderEmbedding(require('prototype'),browserY,M));
})(register_notation);

})(n=>{bridge=n;});
function installMLowerBound(bridge,rows) {
  const M=bridge.debug.target,Y=bridge.debug.source,U=M.debug.parseExpr('()(1:ω)');
  const endpoint=bridge.debug.parse(bridge.debug.endpoint);
  const lex=(a,b)=>{
    const x=a==='0'?[]:a.split(',').map(BigInt),y=b==='0'?[]:b.split(',').map(BigInt);
    for(let i=0;i<Math.min(x.length,y.length);i++)if(x[i]!==y[i])return x[i]<y[i]?-1:1;
    return Math.sign(x.length-y.length);
  };
  const table=rows.map(r=>({...r,expr:M.debug.parseExpr(r.m)}));
  const tripletTop='1,3,4,2,5,7,4',tripletSeed=M.FS(U,3);
  const small=M.debug.parseExpr('()(1:1)'),escape=s=>String(s).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;');
  const cache=new Map();
  function parse(text){
    text=String(text).split('≥')[0].trim().replace(/^M【|】$/g,'');
    if(['M13','Limit','1,3'].includes(text))return U;
    const e=M.debug.parseExpr(text);if(M.compare(e,U)>0)throw Error('本版本只探索普通 M13 以下');return e;
  }
  function bound(expr){
    const key=M.debug.exprToPlain(expr);
    if(cache.has(key))return cache.get(key);
    let result={y:'0',method:'finite',witness:null};
    if(M.compare(expr,small)<0){
      // Standard terms below M12 are precisely finite strings of empty columns.
      result={y:expr.map(()=>1).join(',')||'0',method:'finite',witness:key};
    }else{
      for(const row of table)if(M.compare(row.expr,expr)<=0&&lex(result.y,row.y)<0)
        result={y:row.y,method:row.method,witness:row.m};
      // The entire cofinal family T[n] <= D3[3*n+6], not a finite set of
      // examples.  For a standard input below D3, a longer prefix of D3's
      // infinite basic sequence cannot lie below the input: otherwise the
      // input would dominate every D3[k].  Thus the length bound is exact.
      if(lex(result.y,tripletTop)<0&&expr.length>=9){
        let lo=-1,hi=Math.floor((expr.length-9)/3)+1;
        while(lo+1<hi){
          const n=Math.floor((lo+hi)/2),w=M.FS(tripletSeed,3*n+6);
          if(M.compare(w,expr)<=0)lo=n;else hi=n;
        }
        if(lo>=0){
          const y=[1,3,4,...Array.from({length:lo+1},(_,b)=>[b+2,b+5,b+7]).flat()].join(',');
          if(lex(result.y,y)<0)result={y,method:'dormant-triplet-family',
            witness:M.debug.exprToPlain(M.FS(tripletSeed,3*lo+6))};
        }
      }
      // An unbounded mathematical family, not just the finitely stored sample.
      for(let m=1;2*m+3<=expr.length;m++){
        const seed=M.FS(U,2*m+2);if(M.compare(seed,expr)>0)break;
        const y=[1,3,4,...Array.from({length:m},()=>[2,5,7,12]).flat()].join(',');
        if(lex(result.y,y)<0)result={y,method:'closed-block-family',witness:M.debug.exprToPlain(seed)};
      }
    }
    if(cache.size>=128)cache.delete(cache.keys().next().value);cache.set(key,result);return result;
  }
  function show(expr,list,pair){
    const text=list?(M.debug.exprToPlain(expr)||'0'):M.debug.countText(expr,{maxMs:40,maxWork:80000});
    return pair?'M【'+text+'】 ≥ Y【'+bound(expr).y+'】':text;
  }
  const view=(name,list,pair)=>({name,plain:expr=>show(expr,list,pair),
    html:expr=>'<span style="font-family:inherit;white-space:normal" title="Y 序型下界；可重复，不是反向嵌入">'+escape(show(expr,list,pair))+'</span>',
    ...(list?{from_display:parse}:{})});
  return {
    id:'m13-with-monotone-y-lower-bound-20260920',name:'M13 ≥ Y（单调下界）',simple_name:'M13 ≥ Y',
    init:()=>[U,[[]],[]],is_limit:M.is_limit,compare:M.compare,
    FS:(expr,n)=>{
      if(!Number.isSafeInteger(n)||n<0||n>96)throw Error('基本列指标超限（0..96）');
      return M.FS(expr,n);
    },
    display:view('M 计数 ≥ Y',false,true),
    display_equiv:{'M 列表 ≥ Y':view('M 列表 ≥ Y',true,true),'M 计数':view('M 计数',false,false),'M 列表':view('M 列表',true,false)},
    description:[
      '顶端为普通 e0MN 的 M13=()(1:ω)，不是 strong e0MN。点击使用原 M 基本列。',
      '旁边显示 Y 序型下界；M 增大时下界不减，但不同 M 式可以得到同一个下界。不是 M 到 Y 的反向嵌入。',
      '下界取自已有比较定理、任意有限 C_m 家族、完整三列块基本列族，以及两套下降模拟的固定标定表。不是最优下界。',
      '已补入 Y(134257) 与 Y(1342574) 之间的标定；显示仍是下界，不保证逐个列出所有 Y 式子。',
      '顶端显示 Y(1,3,4,2,5,7,12,3)。关于更大的 Y(…,12,4)，本文件没有宣称已证明。',
      '只对 M13 的标准后代作承诺。未 Lean 形式化。下界表固定，不受点击顺序、缓存或计数超时影响。',
      '计数超限保留已算出的数字，余下以 ? 表示；列表视图给出完整 M 式。',
    ],
    debug:{bound,parse,source:M,y:Y,endpoint,table,forward:bridge,
      verify_bound:expr=>{
        const b=bound(expr);return {y:b.y,method:b.method,
          witnessBelow:b.witness===null||M.compare(M.debug.parseExpr(b.witness),expr)<=0};
      },
    },
  };
}
register(installMLowerBound(bridge,[{"y":"1,2","m":"()(1:1)","method":"paper-calibration"},{"y":"1,2,4","m":"()(1:1)(2:2)","method":"paper-calibration"},{"y":"1,3","m":"()(1:1)(2:2)(1:1)","method":"paper-calibration"},{"y":"1,3,3","m":"()(1:1)(2:2)(2:2)(1:1)","method":"paper-calibration"},{"y":"1,3,3,3","m":"()(1:1)(2:2)(2:2)(2:2)(1:1)","method":"paper-calibration"},{"y":"1,3,4","m":"()(1:1)(2:2)(3:1)","method":"paper-calibration"},{"y":"1,3,4,2,5,7","m":"()(1:1)(2:2)(3:1;2:2)","method":"paper-calibration"},{"y":"1,3,4,2,5,7,1","m":"()(1:1)(2:2)(3:1;2:2)()","method":"paper-calibration"},{"y":"1,3,4,2,5,7,2","m":"()(1:1)(2:2)(3:1;2:2)(1:1)","method":"paper-calibration"},{"y":"1,3,4,2,5,7,3","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,5","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)()(11:1)(12:12)(13:12)(14:12)(15:12)(16:12)(17:12)(18:12)(19:11;18:12)(20:11;18:12)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,5,9","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)()(11:1)(12:12)(13:12)(14:12)(15:12)(16:12)(17:12)(18:12)(19:11;18:12)(20:11;18:12)(21:11;18:12)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,5,9,17","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)()(11:1)(12:12)(13:12)(14:12)(15:12)(16:12)(17:12)(18:12)(19:11;18:12)(20:11;18:12)(21:11;18:12)(22:11;18:12)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:1;8:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,7","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:1;8:2)(11:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,7,9","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:1;8:2)(11:2)()(13:1)(14:14)(15:14)(16:14)(17:14)(18:14)(19:14)(20:14)(21:14)(22:1;20:14)(23:13;20:14)(24:13;20:14)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,7,9,13","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:1;8:2)(11:2)()(13:1)(14:14)(15:14)(16:14)(17:14)(18:14)(19:14)(20:14)(21:14)(22:1;20:14)(23:13;20:14)(24:13;20:14)(25:13;20:14)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,7,9,13,21","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:1;8:2)(11:2)()(13:1)(14:14)(15:14)(16:14)(17:14)(18:14)(19:14)(20:14)(21:14)(22:1;20:14)(23:13;20:14)(24:13;20:14)(25:13;20:14)(26:13;20:14)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,7,10","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:1;8:2)(11:2)(12:1;8:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,7,10,11","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:1;8:2)(11:2)(12:1;8:2)(13:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,7,10,11,13","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:1;8:2)(11:2)(12:1;8:2)(13:2)()(15:1)(16:16)(17:16)(18:16)(19:16)(20:16)(21:16)(22:16)(23:16)(24:1;22:16)(25:16)(26:1;22:16)(27:15;22:16)(28:15;22:16)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,7,10,11,13,17","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:1;8:2)(11:2)(12:1;8:2)(13:2)()(15:1)(16:16)(17:16)(18:16)(19:16)(20:16)(21:16)(22:16)(23:16)(24:1;22:16)(25:16)(26:1;22:16)(27:15;22:16)(28:15;22:16)(29:15;22:16)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,7,10,11,13,17,25","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:1;8:2)(11:2)(12:1;8:2)(13:2)()(15:1)(16:16)(17:16)(18:16)(19:16)(20:16)(21:16)(22:16)(23:16)(24:1;22:16)(25:16)(26:1;22:16)(27:15;22:16)(28:15;22:16)(29:15;22:16)(30:15;22:16)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,7,10,11,14","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:1;8:2)(11:2)(12:1;8:2)(13:2)(14:1;8:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,7,10,11,14,15","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:1;8:2)(11:2)(12:1;8:2)(13:2)(14:1;8:2)(15:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,7,10,11,14,15,17","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:1;8:2)(11:2)(12:1;8:2)(13:2)(14:1;8:2)(15:2)()(17:1)(18:18)(19:18)(20:18)(21:18)(22:18)(23:18)(24:18)(25:18)(26:1;24:18)(27:18)(28:1;24:18)(29:18)(30:1;24:18)(31:17;24:18)(32:17;24:18)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,7,10,11,14,15,17,21","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:1;8:2)(11:2)(12:1;8:2)(13:2)(14:1;8:2)(15:2)()(17:1)(18:18)(19:18)(20:18)(21:18)(22:18)(23:18)(24:18)(25:18)(26:1;24:18)(27:18)(28:1;24:18)(29:18)(30:1;24:18)(31:17;24:18)(32:17;24:18)(33:17;24:18)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,7,10,11,14,15,17,21,29","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:1;8:2)(11:2)(12:1;8:2)(13:2)(14:1;8:2)(15:2)()(17:1)(18:18)(19:18)(20:18)(21:18)(22:18)(23:18)(24:18)(25:18)(26:1;24:18)(27:18)(28:1;24:18)(29:18)(30:1;24:18)(31:17;24:18)(32:17;24:18)(33:17;24:18)(34:17;24:18)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,7,10,11,14,15,18","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:1;8:2)(11:2)(12:1;8:2)(13:2)(14:1;8:2)(15:2)(16:1;8:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,6","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)()(14:1)(15:15)(16:15)(17:15)(18:15)(19:15)(20:15)(21:15)(22:15)(23:15)(24:15)(25:14;24:15)(26:14;24:15)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,6,10","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)()(14:1)(15:15)(16:15)(17:15)(18:15)(19:15)(20:15)(21:15)(22:15)(23:15)(24:15)(25:14;24:15)(26:14;24:15)(27:14;24:15)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,6,10,18","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)()(14:1)(15:15)(16:15)(17:15)(18:15)(19:15)(20:15)(21:15)(22:15)(23:15)(24:15)(25:14;24:15)(26:14;24:15)(27:14;24:15)(28:14;24:15)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:1;11:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,8","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:1;11:2)(14:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,8,10","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:1;11:2)(14:2)()(16:1)(17:17)(18:17)(19:17)(20:17)(21:17)(22:17)(23:17)(24:17)(25:17)(26:17)(27:17)(28:1;26:17)(29:16;26:17)(30:16;26:17)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,8,10,14","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:1;11:2)(14:2)()(16:1)(17:17)(18:17)(19:17)(20:17)(21:17)(22:17)(23:17)(24:17)(25:17)(26:17)(27:17)(28:1;26:17)(29:16;26:17)(30:16;26:17)(31:16;26:17)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,8,10,14,22","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:1;11:2)(14:2)()(16:1)(17:17)(18:17)(19:17)(20:17)(21:17)(22:17)(23:17)(24:17)(25:17)(26:17)(27:17)(28:1;26:17)(29:16;26:17)(30:16;26:17)(31:16;26:17)(32:16;26:17)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,8,11","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:1;11:2)(14:2)(15:1;11:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,8,11,12","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:1;11:2)(14:2)(15:1;11:2)(16:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,8,11,12,14","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:1;11:2)(14:2)(15:1;11:2)(16:2)()(18:1)(19:19)(20:19)(21:19)(22:19)(23:19)(24:19)(25:19)(26:19)(27:19)(28:19)(29:19)(30:1;28:19)(31:19)(32:1;28:19)(33:18;28:19)(34:18;28:19)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,8,11,12,14,18","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:1;11:2)(14:2)(15:1;11:2)(16:2)()(18:1)(19:19)(20:19)(21:19)(22:19)(23:19)(24:19)(25:19)(26:19)(27:19)(28:19)(29:19)(30:1;28:19)(31:19)(32:1;28:19)(33:18;28:19)(34:18;28:19)(35:18;28:19)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,8,11,12,14,18,26","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:1;11:2)(14:2)(15:1;11:2)(16:2)()(18:1)(19:19)(20:19)(21:19)(22:19)(23:19)(24:19)(25:19)(26:19)(27:19)(28:19)(29:19)(30:1;28:19)(31:19)(32:1;28:19)(33:18;28:19)(34:18;28:19)(35:18;28:19)(36:18;28:19)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,8,11,12,15","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:1;11:2)(14:2)(15:1;11:2)(16:2)(17:1;11:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,8,11,12,15,16","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:1;11:2)(14:2)(15:1;11:2)(16:2)(17:1;11:2)(18:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,8,11,12,15,16,18","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:1;11:2)(14:2)(15:1;11:2)(16:2)(17:1;11:2)(18:2)()(20:1)(21:21)(22:21)(23:21)(24:21)(25:21)(26:21)(27:21)(28:21)(29:21)(30:21)(31:21)(32:1;30:21)(33:21)(34:1;30:21)(35:21)(36:1;30:21)(37:20;30:21)(38:20;30:21)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,8,11,12,15,16,18,22","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:1;11:2)(14:2)(15:1;11:2)(16:2)(17:1;11:2)(18:2)()(20:1)(21:21)(22:21)(23:21)(24:21)(25:21)(26:21)(27:21)(28:21)(29:21)(30:21)(31:21)(32:1;30:21)(33:21)(34:1;30:21)(35:21)(36:1;30:21)(37:20;30:21)(38:20;30:21)(39:20;30:21)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,8,11,12,15,16,18,22,30","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:1;11:2)(14:2)(15:1;11:2)(16:2)(17:1;11:2)(18:2)()(20:1)(21:21)(22:21)(23:21)(24:21)(25:21)(26:21)(27:21)(28:21)(29:21)(30:21)(31:21)(32:1;30:21)(33:21)(34:1;30:21)(35:21)(36:1;30:21)(37:20;30:21)(38:20;30:21)(39:20;30:21)(40:20;30:21)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,8,11,12,15,16,19","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:1;11:2)(14:2)(15:1;11:2)(16:2)(17:1;11:2)(18:2)(19:1;11:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,7","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)()(17:1)(18:18)(19:18)(20:18)(21:18)(22:18)(23:18)(24:18)(25:18)(26:18)(27:18)(28:18)(29:18)(30:18)(31:17;30:18)(32:17;30:18)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,7,11","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)()(17:1)(18:18)(19:18)(20:18)(21:18)(22:18)(23:18)(24:18)(25:18)(26:18)(27:18)(28:18)(29:18)(30:18)(31:17;30:18)(32:17;30:18)(33:17;30:18)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,7,11,19","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)()(17:1)(18:18)(19:18)(20:18)(21:18)(22:18)(23:18)(24:18)(25:18)(26:18)(27:18)(28:18)(29:18)(30:18)(31:17;30:18)(32:17;30:18)(33:17;30:18)(34:17;30:18)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:1;14:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,9","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:1;14:2)(17:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,9,11","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:1;14:2)(17:2)()(19:1)(20:20)(21:20)(22:20)(23:20)(24:20)(25:20)(26:20)(27:20)(28:20)(29:20)(30:20)(31:20)(32:20)(33:20)(34:1;32:20)(35:19;32:20)(36:19;32:20)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,9,11,15","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:1;14:2)(17:2)()(19:1)(20:20)(21:20)(22:20)(23:20)(24:20)(25:20)(26:20)(27:20)(28:20)(29:20)(30:20)(31:20)(32:20)(33:20)(34:1;32:20)(35:19;32:20)(36:19;32:20)(37:19;32:20)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,9,11,15,23","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:1;14:2)(17:2)()(19:1)(20:20)(21:20)(22:20)(23:20)(24:20)(25:20)(26:20)(27:20)(28:20)(29:20)(30:20)(31:20)(32:20)(33:20)(34:1;32:20)(35:19;32:20)(36:19;32:20)(37:19;32:20)(38:19;32:20)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,9,12","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:1;14:2)(17:2)(18:1;14:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,9,12,13","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:1;14:2)(17:2)(18:1;14:2)(19:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,9,12,13,15","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:1;14:2)(17:2)(18:1;14:2)(19:2)()(21:1)(22:22)(23:22)(24:22)(25:22)(26:22)(27:22)(28:22)(29:22)(30:22)(31:22)(32:22)(33:22)(34:22)(35:22)(36:1;34:22)(37:22)(38:1;34:22)(39:21;34:22)(40:21;34:22)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,9,12,13,15,19","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:1;14:2)(17:2)(18:1;14:2)(19:2)()(21:1)(22:22)(23:22)(24:22)(25:22)(26:22)(27:22)(28:22)(29:22)(30:22)(31:22)(32:22)(33:22)(34:22)(35:22)(36:1;34:22)(37:22)(38:1;34:22)(39:21;34:22)(40:21;34:22)(41:21;34:22)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,9,12,13,15,19,27","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:1;14:2)(17:2)(18:1;14:2)(19:2)()(21:1)(22:22)(23:22)(24:22)(25:22)(26:22)(27:22)(28:22)(29:22)(30:22)(31:22)(32:22)(33:22)(34:22)(35:22)(36:1;34:22)(37:22)(38:1;34:22)(39:21;34:22)(40:21;34:22)(41:21;34:22)(42:21;34:22)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,9,12,13,16","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:1;14:2)(17:2)(18:1;14:2)(19:2)(20:1;14:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,9,12,13,16,17","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:1;14:2)(17:2)(18:1;14:2)(19:2)(20:1;14:2)(21:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,9,12,13,16,17,19","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:1;14:2)(17:2)(18:1;14:2)(19:2)(20:1;14:2)(21:2)()(23:1)(24:24)(25:24)(26:24)(27:24)(28:24)(29:24)(30:24)(31:24)(32:24)(33:24)(34:24)(35:24)(36:24)(37:24)(38:1;36:24)(39:24)(40:1;36:24)(41:24)(42:1;36:24)(43:23;36:24)(44:23;36:24)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,9,12,13,16,17,19,23","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:1;14:2)(17:2)(18:1;14:2)(19:2)(20:1;14:2)(21:2)()(23:1)(24:24)(25:24)(26:24)(27:24)(28:24)(29:24)(30:24)(31:24)(32:24)(33:24)(34:24)(35:24)(36:24)(37:24)(38:1;36:24)(39:24)(40:1;36:24)(41:24)(42:1;36:24)(43:23;36:24)(44:23;36:24)(45:23;36:24)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,9,12,13,16,17,19,23,31","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:1;14:2)(17:2)(18:1;14:2)(19:2)(20:1;14:2)(21:2)()(23:1)(24:24)(25:24)(26:24)(27:24)(28:24)(29:24)(30:24)(31:24)(32:24)(33:24)(34:24)(35:24)(36:24)(37:24)(38:1;36:24)(39:24)(40:1;36:24)(41:24)(42:1;36:24)(43:23;36:24)(44:23;36:24)(45:23;36:24)(46:23;36:24)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,9,12,13,16,17,20","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:1;14:2)(17:2)(18:1;14:2)(19:2)(20:1;14:2)(21:2)(22:1;14:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,10","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:2)(17:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,10,6","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:2)(17:2)(18:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,10,6,8","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:2)(17:2)(18:2)()(20:1)(21:21)(22:21)(23:21)(24:21)(25:21)(26:21)(27:21)(28:21)(29:21)(30:21)(31:21)(32:21)(33:21)(34:21)(35:21)(36:21)(37:20;36:21)(38:20;36:21)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,10,6,8,12","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:2)(17:2)(18:2)()(20:1)(21:21)(22:21)(23:21)(24:21)(25:21)(26:21)(27:21)(28:21)(29:21)(30:21)(31:21)(32:21)(33:21)(34:21)(35:21)(36:21)(37:20;36:21)(38:20;36:21)(39:20;36:21)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,10,6,8,12,20","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:2)(17:2)(18:2)()(20:1)(21:21)(22:21)(23:21)(24:21)(25:21)(26:21)(27:21)(28:21)(29:21)(30:21)(31:21)(32:21)(33:21)(34:21)(35:21)(36:21)(37:20;36:21)(38:20;36:21)(39:20;36:21)(40:20;36:21)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,10,6,9","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:2)(17:2)(18:2)(19:1;17:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,10,6,9,10","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:2)(17:2)(18:2)(19:1;17:2)(20:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,10,6,9,10,12","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:2)(17:2)(18:2)(19:1;17:2)(20:2)()(22:1)(23:23)(24:23)(25:23)(26:23)(27:23)(28:23)(29:23)(30:23)(31:23)(32:23)(33:23)(34:23)(35:23)(36:23)(37:23)(38:23)(39:23)(40:1;38:23)(41:22;38:23)(42:22;38:23)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,10,6,9,10,12,16","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:2)(17:2)(18:2)(19:1;17:2)(20:2)()(22:1)(23:23)(24:23)(25:23)(26:23)(27:23)(28:23)(29:23)(30:23)(31:23)(32:23)(33:23)(34:23)(35:23)(36:23)(37:23)(38:23)(39:23)(40:1;38:23)(41:22;38:23)(42:22;38:23)(43:22;38:23)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,10,6,9,10,12,16,24","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:2)(17:2)(18:2)(19:1;17:2)(20:2)()(22:1)(23:23)(24:23)(25:23)(26:23)(27:23)(28:23)(29:23)(30:23)(31:23)(32:23)(33:23)(34:23)(35:23)(36:23)(37:23)(38:23)(39:23)(40:1;38:23)(41:22;38:23)(42:22;38:23)(43:22;38:23)(44:22;38:23)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,10,6,9,10,13","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:2)(17:2)(18:2)(19:1;17:2)(20:2)(21:1;17:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,10,6,9,10,13,14","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:2)(17:2)(18:2)(19:1;17:2)(20:2)(21:1;17:2)(22:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,10,6,9,10,13,14,16","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:2)(17:2)(18:2)(19:1;17:2)(20:2)(21:1;17:2)(22:2)()(24:1)(25:25)(26:25)(27:25)(28:25)(29:25)(30:25)(31:25)(32:25)(33:25)(34:25)(35:25)(36:25)(37:25)(38:25)(39:25)(40:25)(41:25)(42:1;40:25)(43:25)(44:1;40:25)(45:24;40:25)(46:24;40:25)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,10,6,9,10,13,14,16,20","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:2)(17:2)(18:2)(19:1;17:2)(20:2)(21:1;17:2)(22:2)()(24:1)(25:25)(26:25)(27:25)(28:25)(29:25)(30:25)(31:25)(32:25)(33:25)(34:25)(35:25)(36:25)(37:25)(38:25)(39:25)(40:25)(41:25)(42:1;40:25)(43:25)(44:1;40:25)(45:24;40:25)(46:24;40:25)(47:24;40:25)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,10,6,9,10,13,14,16,20,28","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:2)(17:2)(18:2)(19:1;17:2)(20:2)(21:1;17:2)(22:2)()(24:1)(25:25)(26:25)(27:25)(28:25)(29:25)(30:25)(31:25)(32:25)(33:25)(34:25)(35:25)(36:25)(37:25)(38:25)(39:25)(40:25)(41:25)(42:1;40:25)(43:25)(44:1;40:25)(45:24;40:25)(46:24;40:25)(47:24;40:25)(48:24;40:25)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,10,6,9,10,13,14,17","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:2)(17:2)(18:2)(19:1;17:2)(20:2)(21:1;17:2)(22:2)(23:1;17:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,10,6,9,10,13,14,17,18","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:2)(17:2)(18:2)(19:1;17:2)(20:2)(21:1;17:2)(22:2)(23:1;17:2)(24:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,10,6,9,10,13,14,17,18,20","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:2)(17:2)(18:2)(19:1;17:2)(20:2)(21:1;17:2)(22:2)(23:1;17:2)(24:2)()(26:1)(27:27)(28:27)(29:27)(30:27)(31:27)(32:27)(33:27)(34:27)(35:27)(36:27)(37:27)(38:27)(39:27)(40:27)(41:27)(42:27)(43:27)(44:1;42:27)(45:27)(46:1;42:27)(47:27)(48:1;42:27)(49:26;42:27)(50:26;42:27)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,10,6,9,10,13,14,17,18,20,24","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:2)(17:2)(18:2)(19:1;17:2)(20:2)(21:1;17:2)(22:2)(23:1;17:2)(24:2)()(26:1)(27:27)(28:27)(29:27)(30:27)(31:27)(32:27)(33:27)(34:27)(35:27)(36:27)(37:27)(38:27)(39:27)(40:27)(41:27)(42:27)(43:27)(44:1;42:27)(45:27)(46:1;42:27)(47:27)(48:1;42:27)(49:26;42:27)(50:26;42:27)(51:26;42:27)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,10,6,9,10,13,14,17,18,21","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:2)(17:2)(18:2)(19:1;17:2)(20:2)(21:1;17:2)(22:2)(23:1;17:2)(24:2)(25:1;17:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,10,6,9,11","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:2)(17:2)(18:2)(19:2)(20:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,10,6,9,11,7","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:2)(17:2)(18:2)(19:2)(20:2)(21:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,10,6,9,11,7,9","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:2)(17:2)(18:2)(19:2)(20:2)(21:2)()(23:1)(24:24)(25:24)(26:24)(27:24)(28:24)(29:24)(30:24)(31:24)(32:24)(33:24)(34:24)(35:24)(36:24)(37:24)(38:24)(39:24)(40:24)(41:24)(42:24)(43:23;42:24)(44:23;42:24)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,10,6,9,11,7,9,13","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:2)(17:2)(18:2)(19:2)(20:2)(21:2)()(23:1)(24:24)(25:24)(26:24)(27:24)(28:24)(29:24)(30:24)(31:24)(32:24)(33:24)(34:24)(35:24)(36:24)(37:24)(38:24)(39:24)(40:24)(41:24)(42:24)(43:23;42:24)(44:23;42:24)(45:23;42:24)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,10,6,9,11,7,9,13,21","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:2)(17:2)(18:2)(19:2)(20:2)(21:2)()(23:1)(24:24)(25:24)(26:24)(27:24)(28:24)(29:24)(30:24)(31:24)(32:24)(33:24)(34:24)(35:24)(36:24)(37:24)(38:24)(39:24)(40:24)(41:24)(42:24)(43:23;42:24)(44:23;42:24)(45:23;42:24)(46:23;42:24)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,10,6,9,11,7,10","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:2)(17:2)(18:2)(19:2)(20:2)(21:2)(22:1;20:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,10,6,9,11,7,10,11","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:2)(17:2)(18:2)(19:2)(20:2)(21:2)(22:1;20:2)(23:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,10,6,9,11,7,10,11,13","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:2)(17:2)(18:2)(19:2)(20:2)(21:2)(22:1;20:2)(23:2)()(25:1)(26:26)(27:26)(28:26)(29:26)(30:26)(31:26)(32:26)(33:26)(34:26)(35:26)(36:26)(37:26)(38:26)(39:26)(40:26)(41:26)(42:26)(43:26)(44:26)(45:26)(46:1;44:26)(47:25;44:26)(48:25;44:26)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,10,6,9,11,7,10,11,13,17","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:2)(17:2)(18:2)(19:2)(20:2)(21:2)(22:1;20:2)(23:2)()(25:1)(26:26)(27:26)(28:26)(29:26)(30:26)(31:26)(32:26)(33:26)(34:26)(35:26)(36:26)(37:26)(38:26)(39:26)(40:26)(41:26)(42:26)(43:26)(44:26)(45:26)(46:1;44:26)(47:25;44:26)(48:25;44:26)(49:25;44:26)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,10,6,9,11,7,10,11,13,17,25","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:2)(17:2)(18:2)(19:2)(20:2)(21:2)(22:1;20:2)(23:2)()(25:1)(26:26)(27:26)(28:26)(29:26)(30:26)(31:26)(32:26)(33:26)(34:26)(35:26)(36:26)(37:26)(38:26)(39:26)(40:26)(41:26)(42:26)(43:26)(44:26)(45:26)(46:1;44:26)(47:25;44:26)(48:25;44:26)(49:25;44:26)(50:25;44:26)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,10,6,9,11,7,10,11,14","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:2)(17:2)(18:2)(19:2)(20:2)(21:2)(22:1;20:2)(23:2)(24:1;20:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,10,6,9,11,7,10,11,14,15","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:2)(17:2)(18:2)(19:2)(20:2)(21:2)(22:1;20:2)(23:2)(24:1;20:2)(25:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,10,6,9,11,7,10,11,14,15,17","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:2)(17:2)(18:2)(19:2)(20:2)(21:2)(22:1;20:2)(23:2)(24:1;20:2)(25:2)()(27:1)(28:28)(29:28)(30:28)(31:28)(32:28)(33:28)(34:28)(35:28)(36:28)(37:28)(38:28)(39:28)(40:28)(41:28)(42:28)(43:28)(44:28)(45:28)(46:28)(47:28)(48:1;46:28)(49:28)(50:1;46:28)(51:27;46:28)(52:27;46:28)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,10,6,9,11,7,10,11,14,15,18","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:2)(17:2)(18:2)(19:2)(20:2)(21:2)(22:1;20:2)(23:2)(24:1;20:2)(25:2)(26:1;20:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,10,6,9,11,7,10,12","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:2)(17:2)(18:2)(19:2)(20:2)(21:2)(22:2)(23:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,10,6,9,11,7,10,12,8","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:2)(17:2)(18:2)(19:2)(20:2)(21:2)(22:2)(23:2)(24:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,10,6,9,11,7,10,12,8,10","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:2)(17:2)(18:2)(19:2)(20:2)(21:2)(22:2)(23:2)(24:2)()(26:1)(27:27)(28:27)(29:27)(30:27)(31:27)(32:27)(33:27)(34:27)(35:27)(36:27)(37:27)(38:27)(39:27)(40:27)(41:27)(42:27)(43:27)(44:27)(45:27)(46:27)(47:27)(48:27)(49:26;48:27)(50:26;48:27)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,10,6,9,11,7,10,12,8,10,14","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:2)(17:2)(18:2)(19:2)(20:2)(21:2)(22:2)(23:2)(24:2)()(26:1)(27:27)(28:27)(29:27)(30:27)(31:27)(32:27)(33:27)(34:27)(35:27)(36:27)(37:27)(38:27)(39:27)(40:27)(41:27)(42:27)(43:27)(44:27)(45:27)(46:27)(47:27)(48:27)(49:26;48:27)(50:26;48:27)(51:26;48:27)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,10,6,9,11,7,10,12,8,11","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:2)(17:2)(18:2)(19:2)(20:2)(21:2)(22:2)(23:2)(24:2)(25:1;23:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,3,6,8,4,7,9,5,8,10,6,9,11,7,10,12,8,11,13","m":"()(1:1)(2:2)(3:2)(4:2)(5:2)(6:2)(7:2)(8:2)(9:2)(10:2)(11:2)(12:2)(13:2)(14:2)(15:2)(16:2)(17:2)(18:2)(19:2)(20:2)(21:2)(22:2)(23:2)(24:2)(25:2)(26:2)","method":"local-triplet-simulation"},{"y":"1,3,4,2,5,7,4","m":"()(1:1)(2:2)(3:3)","method":"paper-calibration"},{"y":"1,3,4,2,5,7,10","m":"()(1:1)(2:2)(3:3)(4:3)(5:3)(6:3)(7:3)(8:3)(9:3)(10:3)(11:3)(12:3)(13:3)(14:3)(15:3)(16:3)(17:3)(1:1)(19:2)(20:20)(21:20)(22:20)(23:20)(24:20)(25:20)(26:20)(27:20)(28:20)(29:20)(30:20)(31:20)(32:20)(33:20)()(35:1)(36:36)(37:37)(38:37)(39:37)(40:37)(41:37)(42:37)(43:37)(44:37)(45:37)(46:37)(47:37)(48:37)(49:37)(50:37)(51:37)(35:1)(53:36)(54:54)(55:54)(56:54)(57:54)(58:54)(59:54)(60:54)(61:54)(62:54)(63:54)(64:54)(65:54)(66:37;64:54)(67:54)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,10,14","m":"()(1:1)(2:2)(3:3)(4:3)(5:3)(6:3)(7:3)(8:3)(9:3)(10:3)(11:3)(12:3)(13:3)(14:3)(15:3)(16:3)(17:3)(1:1)(19:2)(20:20)(21:20)(22:20)(23:20)(24:20)(25:20)(26:20)(27:20)(28:20)(29:20)(30:20)(31:20)(32:20)(33:20)()(35:1)(36:36)(37:37)(38:37)(39:37)(40:37)(41:37)(42:37)(43:37)(44:37)(45:37)(46:37)(47:37)(48:37)(49:37)(50:37)(51:37)(35:1)(53:36)(54:54)(55:54)(56:54)(57:54)(58:54)(59:54)(60:54)(61:54)(62:54)(63:54)(64:54)(65:54)(66:37;64:54)(67:54)(68:37;64:54)(69:54)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,11","m":"()(1:1)(2:2)(3:3)(4:3)(5:3)(6:3)(7:3)(8:3)(9:3)(10:3)(11:3)(12:3)(13:3)(14:3)(15:3)(16:3)(17:3)(1:1)(19:2)(20:20)(21:20)(22:20)(23:20)(24:20)(25:20)(26:20)(27:20)(28:20)(29:20)(30:20)(31:20)(32:20)(33:20)()(35:1)(36:36)(37:37)(38:37)(39:37)(40:37)(41:37)(42:37)(43:37)(44:37)(45:37)(46:37)(47:37)(48:37)(49:37)(50:37)(51:37)(35:1)(53:36)(54:54)(55:54)(56:54)(57:54)(58:54)(59:54)(60:54)(61:54)(62:54)(63:54)(64:54)(65:54)(66:54)(67:54)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,11,18","m":"()(1:1)(2:2)(3:3)(4:3)(5:3)(6:3)(7:3)(8:3)(9:3)(10:3)(11:3)(12:3)(13:3)(14:3)(15:3)(16:3)(17:3)(18:3)(19:3)(1:1)(21:2)(22:22)(23:22)(24:22)(25:22)(26:22)(27:22)(28:22)(29:22)(30:22)(31:22)(32:22)(33:22)(34:22)(35:22)(36:22)(37:22)()(39:1)(40:40)(41:41)(42:41)(43:41)(44:41)(45:41)(46:41)(47:41)(48:41)(49:41)(50:41)(51:41)(52:41)(53:41)(54:41)(55:41)(56:41)(57:41)(39:1)(59:40)(60:60)(61:60)(62:60)(63:60)(64:60)(65:60)(66:60)(67:60)(68:60)(69:60)(70:60)(71:60)(72:60)(73:60)(74:42;72:60)(75:60)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,11,18,29","m":"()(1:1)(2:2)(3:3)(4:3)(5:3)(6:3)(7:3)(8:3)(9:3)(10:3)(11:3)(12:3)(13:3)(14:3)(15:3)(16:3)(17:3)(18:3)(19:3)(1:1)(21:2)(22:22)(23:22)(24:22)(25:22)(26:22)(27:22)(28:22)(29:22)(30:22)(31:22)(32:22)(33:22)(34:22)(35:22)(36:22)(37:22)()(39:1)(40:40)(41:41)(42:41)(43:41)(44:41)(45:41)(46:41)(47:41)(48:41)(49:41)(50:41)(51:41)(52:41)(53:41)(54:41)(55:41)(56:41)(57:41)(39:1)(59:40)(60:60)(61:60)(62:60)(63:60)(64:60)(65:60)(66:60)(67:60)(68:60)(69:60)(70:60)(71:60)(72:60)(73:60)(74:42;72:60)(75:60)(76:42;72:60)(77:60)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,11,19","m":"()(1:1)(2:2)(3:3)(4:3)(5:3)(6:3)(7:3)(8:3)(9:3)(10:3)(11:3)(12:3)(13:3)(14:3)(15:3)(16:3)(17:3)(18:3)(19:3)(1:1)(21:2)(22:22)(23:22)(24:22)(25:22)(26:22)(27:22)(28:22)(29:22)(30:22)(31:22)(32:22)(33:22)(34:22)(35:22)(36:22)(37:22)()(39:1)(40:40)(41:41)(42:41)(43:41)(44:41)(45:41)(46:41)(47:41)(48:41)(49:41)(50:41)(51:41)(52:41)(53:41)(54:41)(55:41)(56:41)(57:41)(39:1)(59:40)(60:60)(61:60)(62:60)(63:60)(64:60)(65:60)(66:60)(67:60)(68:60)(69:60)(70:60)(71:60)(72:60)(73:60)(74:60)(75:60)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,11,19,34","m":"()(1:1)(2:2)(3:3)(4:3)(5:3)(6:3)(7:3)(8:3)(9:3)(10:3)(11:3)(12:3)(13:3)(14:3)(15:3)(16:3)(17:3)(18:3)(19:3)(20:3)(21:3)(1:1)(23:2)(24:24)(25:24)(26:24)(27:24)(28:24)(29:24)(30:24)(31:24)(32:24)(33:24)(34:24)(35:24)(36:24)(37:24)(38:24)(39:24)(40:24)(41:24)()(43:1)(44:44)(45:45)(46:45)(47:45)(48:45)(49:45)(50:45)(51:45)(52:45)(53:45)(54:45)(55:45)(56:45)(57:45)(58:45)(59:45)(60:45)(61:45)(62:45)(63:45)(43:1)(65:44)(66:66)(67:66)(68:66)(69:66)(70:66)(71:66)(72:66)(73:66)(74:66)(75:66)(76:66)(77:66)(78:66)(79:66)(80:66)(81:66)(82:47;80:66)(83:66)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,11,19,34,60","m":"()(1:1)(2:2)(3:3)(4:3)(5:3)(6:3)(7:3)(8:3)(9:3)(10:3)(11:3)(12:3)(13:3)(14:3)(15:3)(16:3)(17:3)(18:3)(19:3)(20:3)(21:3)(1:1)(23:2)(24:24)(25:24)(26:24)(27:24)(28:24)(29:24)(30:24)(31:24)(32:24)(33:24)(34:24)(35:24)(36:24)(37:24)(38:24)(39:24)(40:24)(41:24)()(43:1)(44:44)(45:45)(46:45)(47:45)(48:45)(49:45)(50:45)(51:45)(52:45)(53:45)(54:45)(55:45)(56:45)(57:45)(58:45)(59:45)(60:45)(61:45)(62:45)(63:45)(43:1)(65:44)(66:66)(67:66)(68:66)(69:66)(70:66)(71:66)(72:66)(73:66)(74:66)(75:66)(76:66)(77:66)(78:66)(79:66)(80:66)(81:66)(82:47;80:66)(83:66)(84:47;80:66)(85:66)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,11,19,35","m":"()(1:1)(2:2)(3:3)(4:3)(5:3)(6:3)(7:3)(8:3)(9:3)(10:3)(11:3)(12:3)(13:3)(14:3)(15:3)(16:3)(17:3)(18:3)(19:3)(20:3)(21:3)(1:1)(23:2)(24:24)(25:24)(26:24)(27:24)(28:24)(29:24)(30:24)(31:24)(32:24)(33:24)(34:24)(35:24)(36:24)(37:24)(38:24)(39:24)(40:24)(41:24)()(43:1)(44:44)(45:45)(46:45)(47:45)(48:45)(49:45)(50:45)(51:45)(52:45)(53:45)(54:45)(55:45)(56:45)(57:45)(58:45)(59:45)(60:45)(61:45)(62:45)(63:45)(43:1)(65:44)(66:66)(67:66)(68:66)(69:66)(70:66)(71:66)(72:66)(73:66)(74:66)(75:66)(76:66)(77:66)(78:66)(79:66)(80:66)(81:66)(82:66)(83:66)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,11,19,35,66","m":"()(1:1)(2:2)(3:3)(4:3)(5:3)(6:3)(7:3)(8:3)(9:3)(10:3)(11:3)(12:3)(13:3)(14:3)(15:3)(16:3)(17:3)(18:3)(19:3)(20:3)(21:3)(22:3)(23:3)(1:1)(25:2)(26:26)(27:26)(28:26)(29:26)(30:26)(31:26)(32:26)(33:26)(34:26)(35:26)(36:26)(37:26)(38:26)(39:26)(40:26)(41:26)(42:26)(43:26)(44:26)(45:26)()(47:1)(48:48)(49:49)(50:49)(51:49)(52:49)(53:49)(54:49)(55:49)(56:49)(57:49)(58:49)(59:49)(60:49)(61:49)(62:49)(63:49)(64:49)(65:49)(66:49)(67:49)(68:49)(69:49)(47:1)(71:48)(72:72)(73:72)(74:72)(75:72)(76:72)(77:72)(78:72)(79:72)(80:72)(81:72)(82:72)(83:72)(84:72)(85:72)(86:72)(87:72)(88:72)(89:72)(90:52;88:72)(91:72)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,11,19,35,66,123","m":"()(1:1)(2:2)(3:3)(4:3)(5:3)(6:3)(7:3)(8:3)(9:3)(10:3)(11:3)(12:3)(13:3)(14:3)(15:3)(16:3)(17:3)(18:3)(19:3)(20:3)(21:3)(22:3)(23:3)(1:1)(25:2)(26:26)(27:26)(28:26)(29:26)(30:26)(31:26)(32:26)(33:26)(34:26)(35:26)(36:26)(37:26)(38:26)(39:26)(40:26)(41:26)(42:26)(43:26)(44:26)(45:26)()(47:1)(48:48)(49:49)(50:49)(51:49)(52:49)(53:49)(54:49)(55:49)(56:49)(57:49)(58:49)(59:49)(60:49)(61:49)(62:49)(63:49)(64:49)(65:49)(66:49)(67:49)(68:49)(69:49)(47:1)(71:48)(72:72)(73:72)(74:72)(75:72)(76:72)(77:72)(78:72)(79:72)(80:72)(81:72)(82:72)(83:72)(84:72)(85:72)(86:72)(87:72)(88:72)(89:72)(90:52;88:72)(91:72)(92:52;88:72)(93:72)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,11,19,35,67","m":"()(1:1)(2:2)(3:3)(4:3)(5:3)(6:3)(7:3)(8:3)(9:3)(10:3)(11:3)(12:3)(13:3)(14:3)(15:3)(16:3)(17:3)(18:3)(19:3)(20:3)(21:3)(22:3)(23:3)(1:1)(25:2)(26:26)(27:26)(28:26)(29:26)(30:26)(31:26)(32:26)(33:26)(34:26)(35:26)(36:26)(37:26)(38:26)(39:26)(40:26)(41:26)(42:26)(43:26)(44:26)(45:26)()(47:1)(48:48)(49:49)(50:49)(51:49)(52:49)(53:49)(54:49)(55:49)(56:49)(57:49)(58:49)(59:49)(60:49)(61:49)(62:49)(63:49)(64:49)(65:49)(66:49)(67:49)(68:49)(69:49)(47:1)(71:48)(72:72)(73:72)(74:72)(75:72)(76:72)(77:72)(78:72)(79:72)(80:72)(81:72)(82:72)(83:72)(84:72)(85:72)(86:72)(87:72)(88:72)(89:72)(90:72)(91:72)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12","m":"()(1:1)(2:2)(3:3)(4:4)","method":"paper-calibration"},{"y":"1,3,4,2,5,7,12,2","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:5)(7:5)(8:5)(9:5)(10:5)(11:5)(12:5)()(14:1)(15:15)(16:16)(17:17)(18:18)(19:18)(20:18)(21:18)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:5)(7:5)(8:5)(9:5)(10:5)(11:5)(12:5)()(14:1)(15:15)(16:16)(17:17)(18:18)(19:18)(20:18)(21:18)(22:18)(23:18)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,6","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:5)(7:5)(8:5)(9:5)(10:5)(11:5)(12:5)()(14:1)(15:15)(16:16)(17:17)(18:18)(19:18)(20:18)(21:18)(22:18)(23:18)(24:15;20:18)(25:18)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,6,9","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:5)(7:5)(8:5)(9:5)(10:5)(11:5)(12:5)()(14:1)(15:15)(16:16)(17:17)(18:18)(19:18)(20:18)(21:18)(22:18)(23:18)(24:15;20:18)(25:18)(26:18)(27:18)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,6,9,10","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:5)(7:5)(8:5)(9:5)(10:5)(11:5)(12:5)()(14:1)(15:15)(16:16)(17:17)(18:18)(19:18)(20:18)(21:18)(22:18)(23:18)(24:15;20:18)(25:18)(26:18)(27:18)(28:15;20:18)(29:18)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,6,9,10,13","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:5)(7:5)(8:5)(9:5)(10:5)(11:5)(12:5)()(14:1)(15:15)(16:16)(17:17)(18:18)(19:18)(20:18)(21:18)(22:18)(23:18)(24:15;20:18)(25:18)(26:18)(27:18)(28:15;20:18)(29:18)(30:18)(31:18)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:5)(7:5)(8:5)(9:5)(10:5)(11:5)(12:5)()(14:1)(15:15)(16:16)(17:17)(18:18)(19:18)(20:18)(21:18)(22:18)(23:18)(24:18)(25:18)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,10","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:5)(7:5)(8:5)(9:5)(10:5)(11:5)(12:5)(13:5)(14:5)()(16:1)(17:17)(18:18)(19:19)(20:20)(21:20)(22:20)(23:20)(24:20)(25:20)(26:20)(27:20)(28:18;26:20)(29:20)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,10,14","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:5)(7:5)(8:5)(9:5)(10:5)(11:5)(12:5)(13:5)(14:5)()(16:1)(17:17)(18:18)(19:19)(20:20)(21:20)(22:20)(23:20)(24:20)(25:20)(26:20)(27:20)(28:18;26:20)(29:20)(30:18;26:20)(31:20)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,11","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:5)(7:5)(8:5)(9:5)(10:5)(11:5)(12:5)(13:5)(14:5)()(16:1)(17:17)(18:18)(19:19)(20:20)(21:20)(22:20)(23:20)(24:20)(25:20)(26:20)(27:20)(28:20)(29:20)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,11,18","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:5)(7:5)(8:5)(9:5)(10:5)(11:5)(12:5)(13:5)(14:5)(15:5)(16:5)()(18:1)(19:19)(20:20)(21:21)(22:22)(23:22)(24:22)(25:22)(26:22)(27:22)(28:22)(29:22)(30:22)(31:22)(32:21;30:22)(33:22)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,11,18,29","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:5)(7:5)(8:5)(9:5)(10:5)(11:5)(12:5)(13:5)(14:5)(15:5)(16:5)()(18:1)(19:19)(20:20)(21:21)(22:22)(23:22)(24:22)(25:22)(26:22)(27:22)(28:22)(29:22)(30:22)(31:22)(32:21;30:22)(33:22)(34:21;30:22)(35:22)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,11,19","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:5)(7:5)(8:5)(9:5)(10:5)(11:5)(12:5)(13:5)(14:5)(15:5)(16:5)()(18:1)(19:19)(20:20)(21:21)(22:22)(23:22)(24:22)(25:22)(26:22)(27:22)(28:22)(29:22)(30:22)(31:22)(32:22)(33:22)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,11,19,34","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:5)(7:5)(8:5)(9:5)(10:5)(11:5)(12:5)(13:5)(14:5)(15:5)(16:5)(17:5)(18:5)(19:5)(1:1)(21:2)(22:22)(23:23)(24:24)(25:24)(26:24)(27:24)(28:24)(29:24)(30:24)(31:24)(32:24)(33:24)(34:24)(35:24)(36:24)(37:24)()(39:1)(40:40)(41:41)(42:42)(43:43)(44:43)(45:43)(46:43)(47:43)(48:43)(49:43)(50:43)(51:43)(52:43)(53:43)(54:43)(55:43)(56:43)(57:43)(39:1)(59:40)(60:60)(61:61)(62:62)(63:62)(64:62)(65:62)(66:62)(67:62)(68:62)(69:62)(70:62)(71:62)(72:62)(73:62)(74:43;72:62)(75:62)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,11,19,34,60","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:5)(7:5)(8:5)(9:5)(10:5)(11:5)(12:5)(13:5)(14:5)(15:5)(16:5)(17:5)(18:5)(19:5)(1:1)(21:2)(22:22)(23:23)(24:24)(25:24)(26:24)(27:24)(28:24)(29:24)(30:24)(31:24)(32:24)(33:24)(34:24)(35:24)(36:24)(37:24)()(39:1)(40:40)(41:41)(42:42)(43:43)(44:43)(45:43)(46:43)(47:43)(48:43)(49:43)(50:43)(51:43)(52:43)(53:43)(54:43)(55:43)(56:43)(57:43)(39:1)(59:40)(60:60)(61:61)(62:62)(63:62)(64:62)(65:62)(66:62)(67:62)(68:62)(69:62)(70:62)(71:62)(72:62)(73:62)(74:43;72:62)(75:62)(76:43;72:62)(77:62)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,11,19,35","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:5)(7:5)(8:5)(9:5)(10:5)(11:5)(12:5)(13:5)(14:5)(15:5)(16:5)(17:5)(18:5)(19:5)(1:1)(21:2)(22:22)(23:23)(24:24)(25:24)(26:24)(27:24)(28:24)(29:24)(30:24)(31:24)(32:24)(33:24)(34:24)(35:24)(36:24)(37:24)()(39:1)(40:40)(41:41)(42:42)(43:43)(44:43)(45:43)(46:43)(47:43)(48:43)(49:43)(50:43)(51:43)(52:43)(53:43)(54:43)(55:43)(56:43)(57:43)(39:1)(59:40)(60:60)(61:61)(62:62)(63:62)(64:62)(65:62)(66:62)(67:62)(68:62)(69:62)(70:62)(71:62)(72:62)(73:62)(74:62)(75:62)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,11,19,35,66","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:5)(7:5)(8:5)(9:5)(10:5)(11:5)(12:5)(13:5)(14:5)(15:5)(16:5)(17:5)(18:5)(19:5)(20:5)(21:5)(1:1)(23:2)(24:24)(25:25)(26:26)(27:26)(28:26)(29:26)(30:26)(31:26)(32:26)(33:26)(34:26)(35:26)(36:26)(37:26)(38:26)(39:26)(40:26)(41:26)()(43:1)(44:44)(45:45)(46:46)(47:47)(48:47)(49:47)(50:47)(51:47)(52:47)(53:47)(54:47)(55:47)(56:47)(57:47)(58:47)(59:47)(60:47)(61:47)(62:47)(63:47)(43:1)(65:44)(66:66)(67:67)(68:68)(69:68)(70:68)(71:68)(72:68)(73:68)(74:68)(75:68)(76:68)(77:68)(78:68)(79:68)(80:68)(81:68)(82:48;80:68)(83:68)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,11,19,35,66,123","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:5)(7:5)(8:5)(9:5)(10:5)(11:5)(12:5)(13:5)(14:5)(15:5)(16:5)(17:5)(18:5)(19:5)(20:5)(21:5)(1:1)(23:2)(24:24)(25:25)(26:26)(27:26)(28:26)(29:26)(30:26)(31:26)(32:26)(33:26)(34:26)(35:26)(36:26)(37:26)(38:26)(39:26)(40:26)(41:26)()(43:1)(44:44)(45:45)(46:46)(47:47)(48:47)(49:47)(50:47)(51:47)(52:47)(53:47)(54:47)(55:47)(56:47)(57:47)(58:47)(59:47)(60:47)(61:47)(62:47)(63:47)(43:1)(65:44)(66:66)(67:67)(68:68)(69:68)(70:68)(71:68)(72:68)(73:68)(74:68)(75:68)(76:68)(77:68)(78:68)(79:68)(80:68)(81:68)(82:48;80:68)(83:68)(84:48;80:68)(85:68)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,11,19,35,67","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:5)(7:5)(8:5)(9:5)(10:5)(11:5)(12:5)(13:5)(14:5)(15:5)(16:5)(17:5)(18:5)(19:5)(20:5)(21:5)(1:1)(23:2)(24:24)(25:25)(26:26)(27:26)(28:26)(29:26)(30:26)(31:26)(32:26)(33:26)(34:26)(35:26)(36:26)(37:26)(38:26)(39:26)(40:26)(41:26)()(43:1)(44:44)(45:45)(46:46)(47:47)(48:47)(49:47)(50:47)(51:47)(52:47)(53:47)(54:47)(55:47)(56:47)(57:47)(58:47)(59:47)(60:47)(61:47)(62:47)(63:47)(43:1)(65:44)(66:66)(67:67)(68:68)(69:68)(70:68)(71:68)(72:68)(73:68)(74:68)(75:68)(76:68)(77:68)(78:68)(79:68)(80:68)(81:68)(82:68)(83:68)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,12","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:6)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,12,2","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:6)(7:7)(8:7)(9:7)(10:7)(11:7)(12:7)(13:7)(14:7)()(16:1)(17:17)(18:18)(19:19)(20:20)(21:21)(22:22)(23:22)(24:22)(25:22)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,12,2,5","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:6)(7:7)(8:7)(9:7)(10:7)(11:7)(12:7)(13:7)(14:7)()(16:1)(17:17)(18:18)(19:19)(20:20)(21:21)(22:22)(23:22)(24:22)(25:22)(26:22)(27:22)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,12,2,5,6","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:6)(7:7)(8:7)(9:7)(10:7)(11:7)(12:7)(13:7)(14:7)()(16:1)(17:17)(18:18)(19:19)(20:20)(21:21)(22:22)(23:22)(24:22)(25:22)(26:22)(27:22)(28:17;24:22)(29:22)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,12,2,5,6,9","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:6)(7:7)(8:7)(9:7)(10:7)(11:7)(12:7)(13:7)(14:7)()(16:1)(17:17)(18:18)(19:19)(20:20)(21:21)(22:22)(23:22)(24:22)(25:22)(26:22)(27:22)(28:17;24:22)(29:22)(30:22)(31:22)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,12,2,5,6,9,10","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:6)(7:7)(8:7)(9:7)(10:7)(11:7)(12:7)(13:7)(14:7)()(16:1)(17:17)(18:18)(19:19)(20:20)(21:21)(22:22)(23:22)(24:22)(25:22)(26:22)(27:22)(28:17;24:22)(29:22)(30:22)(31:22)(32:17;24:22)(33:22)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,12,2,5,6,9,10,13","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:6)(7:7)(8:7)(9:7)(10:7)(11:7)(12:7)(13:7)(14:7)()(16:1)(17:17)(18:18)(19:19)(20:20)(21:21)(22:22)(23:22)(24:22)(25:22)(26:22)(27:22)(28:17;24:22)(29:22)(30:22)(31:22)(32:17;24:22)(33:22)(34:22)(35:22)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,12,2,5,7","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:6)(7:7)(8:7)(9:7)(10:7)(11:7)(12:7)(13:7)(14:7)()(16:1)(17:17)(18:18)(19:19)(20:20)(21:21)(22:22)(23:22)(24:22)(25:22)(26:22)(27:22)(28:22)(29:22)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,12,2,5,7,10","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:6)(7:7)(8:7)(9:7)(10:7)(11:7)(12:7)(13:7)(14:7)(15:7)(16:7)()(18:1)(19:19)(20:20)(21:21)(22:22)(23:23)(24:24)(25:24)(26:24)(27:24)(28:24)(29:24)(30:24)(31:24)(32:20;30:24)(33:24)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,12,2,5,7,10,14","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:6)(7:7)(8:7)(9:7)(10:7)(11:7)(12:7)(13:7)(14:7)(15:7)(16:7)()(18:1)(19:19)(20:20)(21:21)(22:22)(23:23)(24:24)(25:24)(26:24)(27:24)(28:24)(29:24)(30:24)(31:24)(32:20;30:24)(33:24)(34:20;30:24)(35:24)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,12,2,5,7,11","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:6)(7:7)(8:7)(9:7)(10:7)(11:7)(12:7)(13:7)(14:7)(15:7)(16:7)()(18:1)(19:19)(20:20)(21:21)(22:22)(23:23)(24:24)(25:24)(26:24)(27:24)(28:24)(29:24)(30:24)(31:24)(32:24)(33:24)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,12,2,5,7,11,18","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:6)(7:7)(8:7)(9:7)(10:7)(11:7)(12:7)(13:7)(14:7)(15:7)(16:7)(17:7)(18:7)()(20:1)(21:21)(22:22)(23:23)(24:24)(25:25)(26:26)(27:26)(28:26)(29:26)(30:26)(31:26)(32:26)(33:26)(34:26)(35:26)(36:23;34:26)(37:26)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,12,2,5,7,11,18,29","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:6)(7:7)(8:7)(9:7)(10:7)(11:7)(12:7)(13:7)(14:7)(15:7)(16:7)(17:7)(18:7)()(20:1)(21:21)(22:22)(23:23)(24:24)(25:25)(26:26)(27:26)(28:26)(29:26)(30:26)(31:26)(32:26)(33:26)(34:26)(35:26)(36:23;34:26)(37:26)(38:23;34:26)(39:26)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,12,2,5,7,11,19","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:6)(7:7)(8:7)(9:7)(10:7)(11:7)(12:7)(13:7)(14:7)(15:7)(16:7)(17:7)(18:7)()(20:1)(21:21)(22:22)(23:23)(24:24)(25:25)(26:26)(27:26)(28:26)(29:26)(30:26)(31:26)(32:26)(33:26)(34:26)(35:26)(36:26)(37:26)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,12,2,5,7,11,19,34","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:6)(7:7)(8:7)(9:7)(10:7)(11:7)(12:7)(13:7)(14:7)(15:7)(16:7)(17:7)(18:7)(19:7)(20:7)()(22:1)(23:23)(24:24)(25:25)(26:26)(27:27)(28:28)(29:28)(30:28)(31:28)(32:28)(33:28)(34:28)(35:28)(36:28)(37:28)(38:28)(39:28)(40:26;38:28)(41:28)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,12,2,5,7,11,19,34,60","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:6)(7:7)(8:7)(9:7)(10:7)(11:7)(12:7)(13:7)(14:7)(15:7)(16:7)(17:7)(18:7)(19:7)(20:7)()(22:1)(23:23)(24:24)(25:25)(26:26)(27:27)(28:28)(29:28)(30:28)(31:28)(32:28)(33:28)(34:28)(35:28)(36:28)(37:28)(38:28)(39:28)(40:26;38:28)(41:28)(42:26;38:28)(43:28)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,12,2,5,7,11,19,35","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:6)(7:7)(8:7)(9:7)(10:7)(11:7)(12:7)(13:7)(14:7)(15:7)(16:7)(17:7)(18:7)(19:7)(20:7)()(22:1)(23:23)(24:24)(25:25)(26:26)(27:27)(28:28)(29:28)(30:28)(31:28)(32:28)(33:28)(34:28)(35:28)(36:28)(37:28)(38:28)(39:28)(40:28)(41:28)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,12,2,5,7,11,19,35,66","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:6)(7:7)(8:7)(9:7)(10:7)(11:7)(12:7)(13:7)(14:7)(15:7)(16:7)(17:7)(18:7)(19:7)(20:7)(21:7)(22:7)()(24:1)(25:25)(26:26)(27:27)(28:28)(29:29)(30:30)(31:30)(32:30)(33:30)(34:30)(35:30)(36:30)(37:30)(38:30)(39:30)(40:30)(41:30)(42:30)(43:30)(44:29;42:30)(45:30)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,12,2,5,7,11,19,35,66,123","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:6)(7:7)(8:7)(9:7)(10:7)(11:7)(12:7)(13:7)(14:7)(15:7)(16:7)(17:7)(18:7)(19:7)(20:7)(21:7)(22:7)()(24:1)(25:25)(26:26)(27:27)(28:28)(29:29)(30:30)(31:30)(32:30)(33:30)(34:30)(35:30)(36:30)(37:30)(38:30)(39:30)(40:30)(41:30)(42:30)(43:30)(44:29;42:30)(45:30)(46:29;42:30)(47:30)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,12,2,5,7,11,19,35,67","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:6)(7:7)(8:7)(9:7)(10:7)(11:7)(12:7)(13:7)(14:7)(15:7)(16:7)(17:7)(18:7)(19:7)(20:7)(21:7)(22:7)()(24:1)(25:25)(26:26)(27:27)(28:28)(29:29)(30:30)(31:30)(32:30)(33:30)(34:30)(35:30)(36:30)(37:30)(38:30)(39:30)(40:30)(41:30)(42:30)(43:30)(44:30)(45:30)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,12,2,5,7,12","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:6)(7:7)(8:8)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,12,2,5,7,12,2","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:6)(7:7)(8:8)(9:9)(10:9)(11:9)(12:9)(13:9)(14:9)(15:9)(16:9)()(18:1)(19:19)(20:20)(21:21)(22:22)(23:23)(24:24)(25:25)(26:26)(27:26)(28:26)(29:26)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,12,2,5,7,12,2,5","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:6)(7:7)(8:8)(9:9)(10:9)(11:9)(12:9)(13:9)(14:9)(15:9)(16:9)()(18:1)(19:19)(20:20)(21:21)(22:22)(23:23)(24:24)(25:25)(26:26)(27:26)(28:26)(29:26)(30:26)(31:26)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,12,2,5,7,12,2,5,6","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:6)(7:7)(8:8)(9:9)(10:9)(11:9)(12:9)(13:9)(14:9)(15:9)(16:9)()(18:1)(19:19)(20:20)(21:21)(22:22)(23:23)(24:24)(25:25)(26:26)(27:26)(28:26)(29:26)(30:26)(31:26)(32:19;28:26)(33:26)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,12,2,5,7,12,2,5,6,9","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:6)(7:7)(8:8)(9:9)(10:9)(11:9)(12:9)(13:9)(14:9)(15:9)(16:9)()(18:1)(19:19)(20:20)(21:21)(22:22)(23:23)(24:24)(25:25)(26:26)(27:26)(28:26)(29:26)(30:26)(31:26)(32:19;28:26)(33:26)(34:26)(35:26)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,12,2,5,7,12,2,5,6,9,10","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:6)(7:7)(8:8)(9:9)(10:9)(11:9)(12:9)(13:9)(14:9)(15:9)(16:9)()(18:1)(19:19)(20:20)(21:21)(22:22)(23:23)(24:24)(25:25)(26:26)(27:26)(28:26)(29:26)(30:26)(31:26)(32:19;28:26)(33:26)(34:26)(35:26)(36:19;28:26)(37:26)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,12,2,5,7,12,2,5,6,9,10,13","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:6)(7:7)(8:8)(9:9)(10:9)(11:9)(12:9)(13:9)(14:9)(15:9)(16:9)()(18:1)(19:19)(20:20)(21:21)(22:22)(23:23)(24:24)(25:25)(26:26)(27:26)(28:26)(29:26)(30:26)(31:26)(32:19;28:26)(33:26)(34:26)(35:26)(36:19;28:26)(37:26)(38:26)(39:26)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,12,2,5,7,12,2,5,7","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:6)(7:7)(8:8)(9:9)(10:9)(11:9)(12:9)(13:9)(14:9)(15:9)(16:9)()(18:1)(19:19)(20:20)(21:21)(22:22)(23:23)(24:24)(25:25)(26:26)(27:26)(28:26)(29:26)(30:26)(31:26)(32:26)(33:26)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,12,2,5,7,12,2,5,7,10","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:6)(7:7)(8:8)(9:9)(10:9)(11:9)(12:9)(13:9)(14:9)(15:9)(16:9)(17:9)(18:9)()(20:1)(21:21)(22:22)(23:23)(24:24)(25:25)(26:26)(27:27)(28:28)(29:28)(30:28)(31:28)(32:28)(33:28)(34:28)(35:28)(36:22;34:28)(37:28)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,12,2,5,7,12,2,5,7,10,14","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:6)(7:7)(8:8)(9:9)(10:9)(11:9)(12:9)(13:9)(14:9)(15:9)(16:9)(17:9)(18:9)()(20:1)(21:21)(22:22)(23:23)(24:24)(25:25)(26:26)(27:27)(28:28)(29:28)(30:28)(31:28)(32:28)(33:28)(34:28)(35:28)(36:22;34:28)(37:28)(38:22;34:28)(39:28)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,12,2,5,7,12,2,5,7,11","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:6)(7:7)(8:8)(9:9)(10:9)(11:9)(12:9)(13:9)(14:9)(15:9)(16:9)(17:9)(18:9)()(20:1)(21:21)(22:22)(23:23)(24:24)(25:25)(26:26)(27:27)(28:28)(29:28)(30:28)(31:28)(32:28)(33:28)(34:28)(35:28)(36:28)(37:28)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,12,2,5,7,12,2,5,7,11,18","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:6)(7:7)(8:8)(9:9)(10:9)(11:9)(12:9)(13:9)(14:9)(15:9)(16:9)(17:9)(18:9)(19:9)(20:9)()(22:1)(23:23)(24:24)(25:25)(26:26)(27:27)(28:28)(29:29)(30:30)(31:30)(32:30)(33:30)(34:30)(35:30)(36:30)(37:30)(38:30)(39:30)(40:25;38:30)(41:30)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,12,2,5,7,12,2,5,7,11,18,29","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:6)(7:7)(8:8)(9:9)(10:9)(11:9)(12:9)(13:9)(14:9)(15:9)(16:9)(17:9)(18:9)(19:9)(20:9)()(22:1)(23:23)(24:24)(25:25)(26:26)(27:27)(28:28)(29:29)(30:30)(31:30)(32:30)(33:30)(34:30)(35:30)(36:30)(37:30)(38:30)(39:30)(40:25;38:30)(41:30)(42:25;38:30)(43:30)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,12,2,5,7,12,2,5,7,11,19","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:6)(7:7)(8:8)(9:9)(10:9)(11:9)(12:9)(13:9)(14:9)(15:9)(16:9)(17:9)(18:9)(19:9)(20:9)()(22:1)(23:23)(24:24)(25:25)(26:26)(27:27)(28:28)(29:29)(30:30)(31:30)(32:30)(33:30)(34:30)(35:30)(36:30)(37:30)(38:30)(39:30)(40:30)(41:30)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,12,2,5,7,12,2,5,7,11,19,34","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:6)(7:7)(8:8)(9:9)(10:9)(11:9)(12:9)(13:9)(14:9)(15:9)(16:9)(17:9)(18:9)(19:9)(20:9)(21:9)(22:9)()(24:1)(25:25)(26:26)(27:27)(28:28)(29:29)(30:30)(31:31)(32:32)(33:32)(34:32)(35:32)(36:32)(37:32)(38:32)(39:32)(40:32)(41:32)(42:32)(43:32)(44:28;42:32)(45:32)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,12,2,5,7,12,2,5,7,11,19,34,60","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:6)(7:7)(8:8)(9:9)(10:9)(11:9)(12:9)(13:9)(14:9)(15:9)(16:9)(17:9)(18:9)(19:9)(20:9)(21:9)(22:9)()(24:1)(25:25)(26:26)(27:27)(28:28)(29:29)(30:30)(31:31)(32:32)(33:32)(34:32)(35:32)(36:32)(37:32)(38:32)(39:32)(40:32)(41:32)(42:32)(43:32)(44:28;42:32)(45:32)(46:28;42:32)(47:32)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,12,2,5,7,12,2,5,7,11,19,35","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:6)(7:7)(8:8)(9:9)(10:9)(11:9)(12:9)(13:9)(14:9)(15:9)(16:9)(17:9)(18:9)(19:9)(20:9)(21:9)(22:9)()(24:1)(25:25)(26:26)(27:27)(28:28)(29:29)(30:30)(31:31)(32:32)(33:32)(34:32)(35:32)(36:32)(37:32)(38:32)(39:32)(40:32)(41:32)(42:32)(43:32)(44:32)(45:32)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,12,2,5,7,12,2,5,7,11,19,35,66","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:6)(7:7)(8:8)(9:9)(10:9)(11:9)(12:9)(13:9)(14:9)(15:9)(16:9)(17:9)(18:9)(19:9)(20:9)(21:9)(22:9)(23:9)(24:9)()(26:1)(27:27)(28:28)(29:29)(30:30)(31:31)(32:32)(33:33)(34:34)(35:34)(36:34)(37:34)(38:34)(39:34)(40:34)(41:34)(42:34)(43:34)(44:34)(45:34)(46:34)(47:34)(48:31;46:34)(49:34)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,12,2,5,7,12,2,5,7,11,19,35,66,123","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:6)(7:7)(8:8)(9:9)(10:9)(11:9)(12:9)(13:9)(14:9)(15:9)(16:9)(17:9)(18:9)(19:9)(20:9)(21:9)(22:9)(23:9)(24:9)()(26:1)(27:27)(28:28)(29:29)(30:30)(31:31)(32:32)(33:33)(34:34)(35:34)(36:34)(37:34)(38:34)(39:34)(40:34)(41:34)(42:34)(43:34)(44:34)(45:34)(46:34)(47:34)(48:31;46:34)(49:34)(50:31;46:34)(51:34)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,2,5,7,12,2,5,7,12,2,5,7,11,19,35,67","m":"()(1:1)(2:2)(3:3)(4:4)(5:5)(6:6)(7:7)(8:8)(9:9)(10:9)(11:9)(12:9)(13:9)(14:9)(15:9)(16:9)(17:9)(18:9)(19:9)(20:9)(21:9)(22:9)(23:9)(24:9)()(26:1)(27:27)(28:28)(29:29)(30:30)(31:31)(32:32)(33:33)(34:34)(35:34)(36:34)(37:34)(38:34)(39:34)(40:34)(41:34)(42:34)(43:34)(44:34)(45:34)(46:34)(47:34)(48:34)(49:34)","method":"fixed-order-embedding-sample"},{"y":"1,3,4,2,5,7,12,3","m":"()(1:ω)","method":"paper-calibration"}]));
})(register_notation);
