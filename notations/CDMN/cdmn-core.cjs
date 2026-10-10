"use strict";

// CDMN: compact deep mountain notation, the guarded fixed-block rule.
// This is a new candidate, not an ordinal-equivalent implementation of HMN.
// Prefix-zero revision: at the active copy layer, [0] deletes its last column.
// Enclosing layers recurse at the same index; all positive-index rules are unchanged.
// Limits below are implementation guards, not parts of its mathematical rule.
function createCDMN(options = {}) {
  const limits = { milliseconds: 350, events: 500000, cells: 1200000,
    columns: 1200, depth: 180, ...options };
  let deadline, events, cells, depth;
  const ZERO = [], ONE = [[]];
  function reset() { deadline = Date.now() + limits.milliseconds; events = cells = depth = 0; }
  function enter() {
    if (++events > limits.events || ++depth > limits.depth ||
      (!(events % 128) && Date.now() > deadline)) throw Error("CDMN resource limit");
  }
  function leave(value) { depth--; return value; }
  function reserve(n) { if ((cells += n) > limits.cells) throw Error("CDMN allocation limit"); }
  reset();

  function compare(a, b) {
    enter();
    if (a === b) return leave(0);
    for (let j = 0; j < Math.min(a.length, b.length); j++) {
      for (let k = 0; k < Math.min(a[j].length, b[j].length); k++) {
        const x = a[j][k], y = b[j][k];
        const d = Math.sign(x.p - y.p) || compare(x.r, y.r);
        if (d) return leave(d);
      }
      if (a[j].length !== b[j].length) return leave(Math.sign(a[j].length - b[j].length));
    }
    return leave(Math.sign(a.length - b.length));
  }

  function move(g, cut, distance, memo = new WeakMap()) {
    enter();
    if (!distance) return leave(g);
    if (memo.has(g)) return leave(memo.get(g));
    reserve(1 + g.length + g.reduce((s, c) => s + 2 * c.length, 0));
    const out = g.map(c => c.map(e => ({ p: e.p < cut ? e.p : e.p + distance,
      r: move(e.r, cut, distance, memo) })));
    memo.set(g, out); return leave(out);
  }

  function replaceRow(g, row) {
    const column = g.at(-1), old = column.at(-1);
    reserve(g.length + column.length + 1);
    return [...g.slice(0, -1), [...column.slice(0, -1), ...(row.length ? [{ p: old.p, r: row }] : [])]];
  }

  function prune(g) {
    enter();
    if (!g.length || !g.at(-1).length) return leave(g.slice(0, -1));
    const row = g.at(-1).at(-1).r;
    return leave(row.at(-1).length ? replaceRow(g, prune(row)) : g.slice(0, -1));
  }

  function expand(g, n, context) {
    enter();
    if (!g.length || !g.at(-1).length) return leave(g.slice(0, -1));
    if (!n) return leave(prune(g));
    const all = context.concat(g), m = all.length - 1;
    const control = g.at(-1).at(-1), c = control.p, r = control.r;
    if (r.at(-1).length) return leave(replaceRow(g, expand(r, n, all.slice(0, -1))));

    const distance = m - c;
    if (distance <= 0) throw Error("Invalid CDMN parent");
    if (typeof options.trace === "function") options.trace({ c, m, n, base: context.length });
    if (n > (limits.columns - g.length + 1) / distance) throw Error("CDMN column limit");
    const seam = replaceRow(g, r.slice(0, -1)).at(-1);
    let floor = ZERO;
    for (const e of seam) if (compare(floor, e.r) < 0) floor = e.r;
    for (const e of all[c]) {
      const row = move(e.r, c, distance);
      if (compare(floor, row) < 0) { seam.push({ p: e.p, r: row }); floor = row; }
    }
    const block = [seam, ...move(all.slice(c + 1, m), c, distance)];
    const out = g.slice(0, -1);
    for (let j = 0; j < n; j++) { reserve(block.length); out.push(...move(block, c, j * distance)); }
    return leave(out);
  }

  function legal(g, base) {
    enter();
    return leave(Array.isArray(g) && g.length <= limits.columns && g.every((col, j) =>
      Array.isArray(col) && col.every((e, k) => e && Number.isSafeInteger(e.p) &&
        0 <= e.p && e.p < base + j && Array.isArray(e.r) && e.r.length &&
        (!k || col[k - 1].p > e.p) && legal(e.r, base + j))));
  }

  function seed(n) {
    reset();
    if (!Number.isSafeInteger(n) || n < 0 || n > 100) throw Error("CDMN seed limit");
    if (!n) return ONE;
    let row = ONE;
    for (let j = 1; j < n; j++) row = [[{ p: 0, r: row }]];
    return [[], [{ p: 0, r: row }]];
  }

  function FS(g, n, context = ZERO) {
    reset();
    if (!Number.isSafeInteger(n) || n < 0) throw Error("Invalid CDMN index");
    return expand(g, n, context);
  }

  return { ZERO, ONE, seed, FS,
    cmp: (a, b) => { reset(); return compare(a, b); },
    isLegal: (g, base = 0) => { reset(); return legal(g, base); },
    prune: g => { reset(); return prune(g); } };
}

module.exports = { createCDMN };
