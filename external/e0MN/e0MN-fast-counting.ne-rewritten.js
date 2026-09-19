/* e0MN custom notation for NER -- fast-counting edition, 2026-09-17
 * Notation invented by @test_alpha0; this local edition adds fast exact counts.
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
