'use strict';

// Research only. Published notation files are loaded read-only.
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const base = path.resolve(__dirname, '../..');
const started = Date.now();
function load(relative, expose = false) {
  let source = fs.readFileSync(path.join(base, relative), 'utf8');
  if (expose) source = source.replace('debug: { parseOrd, ordFS,',
    'debug: { shiftOrdNumbers, parseOrd, ordFS,');
  let result;
  new Function('register_notation', source)(value => { result = value; });
  return result;
}
const R = load('../../../notations/RPD/RPD-mountain.ne-rewritten.js');
const M = load('output/e0mn-counting-20260917/e0MN-counting.ne-rewritten.js', true);
const cmp = (a, b) => {
  for (let i = 0; i < Math.min(a.length, b.length); i++) {
    if (a[i] !== b[i]) return Math.sign(a[i] - b[i]);
  }
  return Math.sign(a.length - b.length);
};
const key = g => JSON.stringify(g);
function tick() {
  assert(Date.now() - started < 30000, '30-second deadline');
  assert(process.memoryUsage().rss < 640 * 1048576, '640-MiB RSS ceiling');
}
function skyline(col) {
  const byParent = new Map();
  for (const [k, p, q] of col) {
    const old = byParent.get(p);
    if (!old || cmp([k, q], [old[0], old[2]]) > 0) byParent.set(p, [k, p, q]);
  }
  const out = [];
  for (const p of [...byParent.keys()].sort((a, b) => b - a)) {
    const e = byParent.get(p);
    if (!out.length || cmp([e[0], e[2]], [out.at(-1)[0], out.at(-1)[2]]) > 0) out.push(e);
  }
  return out;
}
function step(g, n) {
  if (!g.length) return g;
  const out = g.slice(0, -1), col = g.at(-1);
  if (!n || !col.length) return out;
  const [K, c, r] = col.at(-1), L = g.length - 1 - c;
  const move = (e, b) => [e[0], e[1] < c ? e[1] : e[1] + b * L,
    e[2] < c ? e[2] : e[2] + b * L];
  for (let b = 0; b < n; b++) {
    const [k, p, q] = move([K, c, r], b);
    const pred = q ? [[k, p, q - 1]] : k ? [[k - 1, p, p]] : [];
    out.push(skyline([...col.slice(0, -1).map(e => move(e, b)), ...pred, ...g[c]]));
    for (const source of g.slice(c + 1, -1)) out.push(source.map(e => move(e, b + 1)));
  }
  return out;
}
function saturated(g) {
  return g.every(col => {
    const entries = new Set(col.map(e => e.join(',')));
    return col.every(([k, p]) => {
      for (let h = 0; h < k; h++) if (!entries.has([h, p, p].join(','))) return false;
      return true;
    });
  });
}
const full = text => R.debug.adjacency(text).map(c => c.map(e => e.map(Number)));
const nat = n => n ? [{exp: [], coeff: n}] : [];
const monomial = (d, coeff = 1) => [{exp: nat(d), coeff}];
function row(k, p, q, d) {
  return q === p ? monomial(d, k + 2)
    : [...monomial(d, k + 1), ...nat(d + q + 2)];
}
function gamma(g, N) {
  const d = N + 2;
  const out = [[], ...Array.from({length: d - 1}, (_, i) => [{a: i + 1, x: monomial(i + 1)}])];
  for (const col of g) out.push(col.length
    ? col.map(([k, p, q]) => ({a: d + p + 1, x: row(k, p, q, d)}))
    : [{a: d, x: monomial(d)}]);
  return out;
}
function reachable(from, wanted, maxSteps = 10000) {
  let h = from;
  for (let count = 0; count < maxSteps; count++) {
    tick();
    const c = M.compare(h, wanted);
    if (!c) return {status: 'hit', count};
    if (c < 0) return {status: 'skipped', count, at: M.debug.exprToPlain(h)};
    let found;
    if (M.compare(M.FS(h, 0), wanted) >= 0) found = M.FS(h, 0);
    else if (h.at(-1)?.length) {
      const span = h.length - h.at(-1).at(-1).a;
      const n = Math.max(1, Math.ceil((wanted.length + 1 - h.length) / span));
      // Once this width covers wanted, later indices cannot fix an earlier difference.
      const child = M.FS(h, n);
      if (M.compare(child, wanted) >= 0) found = child;
      else return {status: 'skipped', count, at: M.debug.exprToPlain(h),
        next: M.debug.exprToPlain(child)};
    }
    if (!found) return {status: 'skipped', count, at: M.debug.exprToPlain(h)};
    h = found;
  }
  return {status: 'budget', count: maxSteps};
}

async function main() {
  const stats = {states: 0, saturationChecks: 0, skylineSteps: 0, moveChecks: 0};
  const queue = [], seen = new Set();
  function add(raw, N) {
    if (queue.length >= 2200 || seen.has(raw) || full(raw).length > 15) return;
    seen.add(raw); queue.push({raw, N});
  }
  for (let N = 0; N < 5; N++) add(R.FS('Limit', N), N);
  for (let i = 0; i < queue.length && i < 1600; i++) {
    if (i % 24 === 0) await new Promise(resolve => setImmediate(resolve));
    tick();
    const {raw, N} = queue[i], f = full(raw), g = f.map(skyline);
    assert(saturated(f)); stats.saturationChecks++; stats.states++;
    const image = gamma(g, N);
    assert(M.debug.isLegalExpr(image));
    const control = g.at(-1)?.at(-1);
    for (let n = 0; n <= 3; n++) {
      const width = !g.length ? 0 : !n || !control ? g.length - 1
        : g.length - 1 + n * (g.length - 1 - control[1]);
      if (width > 36) continue;
      const child = R.FS(raw, n), fchild = full(child);
      assert(saturated(fchild)); stats.saturationChecks++;
      assert.deepEqual(fchild.map(skyline), step(g, n)); stats.skylineSteps++;
      add(child, N);
    }
  }
  for (let N = 0; N < 5; N++) {
    const d = N + 2;
    for (let k = 0; k <= N; k++) for (let p = 0; p < 12; p++) {
      for (let q = 0; q <= p; q++) for (let c = 0; c <= 12; c++) {
        const move = i => i < c ? i : i + 5;
        assert.deepEqual(M.debug.shiftOrdNumbers(row(k, p, q, d), d + c + 1, 5),
          row(k, move(p), move(q), d));
        stats.moveChecks++;
      }
    }
  }
  const seedCapture = [];
  for (let N = 0; N <= 1; N++) {
    const g = [[], [[N, 0, 0]]], d = N + 2;
    seedCapture.push({N, image: M.debug.exprToPlain(gamma(g, N)),
      result: reachable(M.FS(M.FS('Limit', 2), d + 1), gamma(g, N), 10000)});
  }
  const simulation = {hits: 0, skipped: [], budgets: 0};
  for (const {raw, N} of queue.slice(0, 100)) {
    if (N > 1) continue;
    const g = full(raw).map(skyline);
    if (g.length > 9 || !g.at(-1)?.length) continue;
    for (let n = 1; n <= 2; n++) {
      const h = step(g, n);
      if (h.length > 14) continue;
      const result = reachable(gamma(g, N), gamma(h, N), 1000);
      if (result.status === 'hit') simulation.hits++;
      else if (result.status === 'budget') simulation.budgets++;
      else if (simulation.skipped.length < 5) simulation.skipped.push({N, g, n,
        from: M.debug.exprToPlain(gamma(g, N)), wanted: M.debug.exprToPlain(gamma(h, N)), result});
    }
  }
  console.log(JSON.stringify({status: 'research, not an embedding theorem', ...stats,
    queue: queue.length, seedCapture, simulation, ms: Date.now() - started,
    rssMiB: Math.ceil(process.memoryUsage().rss / 1048576)}, null, 2));
}
module.exports = {R, M, skyline, step, full, row, gamma, reachable};
if (require.main === module) main().catch(error => { console.error(error); process.exitCode = 1; });
