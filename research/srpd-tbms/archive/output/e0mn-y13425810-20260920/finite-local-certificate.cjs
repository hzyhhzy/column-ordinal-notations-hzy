'use strict';

// Independent finite-row local counting/unranking certificate. Same exact
// trace recurrence as mn-omega-trace, but prefix traces are memoized across
// events. It does not call expose(), down(), or the reservoir projection to
// choose a local-macro endpoint. All accepted labels are positive naturals.
const assert = require('node:assert/strict');
function skyline(column) {
  const best = new Map();
  for (const [p, r] of column) if (!best.has(p) || best.get(p) < r) best.set(p, r);
  const out = []; let row = 0;
  for (const [p, r] of [...best].sort((a, b) => b[0] - a[0])) if (r > row) {out.push([p, r]); row = r;}
  return out;
}
function createCertifier(M, options = {}) {
  const tick = options.tick ?? (() => {}), maxNodes = options.maxNodes ?? 30000;
  const root = {children: new Map()}, stats = {nodes: 0, hits: 0, traceEntries: 0, macros: 0, fs: 0};
  function model(h) {
    const nodes = []; let prefix = root;
    for (let p = 0; p < h.length; p++) {
      tick();
      const column = h[p].map(e => {
        assert(e.x.length === 1 && e.x[0].exp.length === 0, 'finite-only certificate');
        const row = e.x[0].coeff;
        assert(Number.isSafeInteger(row) && row > 0 && row <= h.length - 1);
        return [e.a - 1, row];
      });
      const key = JSON.stringify(column); let node = prefix.children.get(key);
      if (node) stats.hits++;
      else {
        assert(stats.nodes < maxNodes, 'certificate prefix-cache guard');
        let current = column, steps = 0n; const trace = [];
        for (;;) {
          tick(); const edge = current.at(-1), top = edge?.[1] ?? 0;
          if (trace.length) assert(trace.at(-1).top > top);
          const entry = {top, steps, column: current}; trace.push(entry); stats.traceEntries++;
          if (!edge) break;
          const [parent, u] = edge; assert(parent >= 0 && parent < p);
          const lower = current.slice(0, -1); if (u > 1) lower.push([parent, u - 1]);
          const source = nodes[parent].trace; let lo = 0, hi = source.length - 1;
          while (lo < hi) {const mid = (lo + hi) >> 1; if (source[mid].top >= u) lo = mid + 1; else hi = mid;}
          entry.parent = parent; entry.lower = lower;
          current = skyline([...lower, ...source[lo].column]); steps += 1n + source[lo].steps;
        }
        node = {trace, children: new Map()}; prefix.children.set(key, node); stats.nodes++;
      }
      nodes.push(node); prefix = node;
    }
    function at(p, d) {
      tick(); const trace = nodes[p].trace;
      assert(d >= 0n && d <= trace.at(-1).steps);
      let lo = 0, hi = trace.length - 1;
      while (lo < hi) {const mid = (lo + hi + 1) >> 1; if (trace[mid].steps <= d) lo = mid; else hi = mid - 1;}
      const entry = trace[lo];
      if (entry.steps === d) return entry.column;
      return skyline([...entry.lower, ...at(entry.parent, d - entry.steps - 1n)]);
    }
    return {count: nodes.at(-1).trace.at(-1).steps + 1n,
      columnAtStep: d => at(h.length - 1, d).map(([p, r]) => ({a: p + 1, x: [{exp: [], coeff: r}]}))};
  }
  function certify(e) {
    tick();
    if (e.kind === 'FS') {assert.deepEqual(M.FS(e.before, e.n), e.after); stats.fs++; return 0n;}
    assert.deepEqual(e.before.slice(0, -1), e.after.slice(0, -1));
    const before = model(e.before), after = model(e.after), distance = before.count - after.count;
    assert(distance > 0n, 'positive true-local distance');
    assert.deepEqual(before.columnAtStep(distance), e.after.at(-1), 'independent exact local endpoint');
    if (e.kind === 'down') assert.equal(distance, 1n);
    stats.macros++; return distance;
  }
  return {model, certify, stats};
}
module.exports = {createCertifier};
