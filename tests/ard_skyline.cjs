'use strict';

// Bounded regression against the actual published NER script, not a mock core.
// Run: node --max-old-space-size=512 tests/ard_skyline.cjs
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const vm = require('node:vm');
const { performance } = require('node:perf_hooks');

function load(file) {
  let notation;
  vm.runInNewContext(fs.readFileSync(file, 'utf8'), {
    register_notation(value) { assert.equal(notation, undefined); notation = value; },
    queueMicrotask
  }, { filename: file, timeout: 3000 });
  assert.ok(notation);
  return notation;
}
const original = load(path.join(__dirname, '../notations/ARD-legacy/ARD-arcs.ne-rewritten.js'));
const simplified = load(path.join(__dirname, '../notations/ARD/ARD.ne-rewritten.js'));
const freshTask = () => new Promise(resolve => setImmediate(resolve));
const key = cols => cols.map(col => '[' + col.map(e => `(${e.k},${e.p},${e.q})`).join(',') + ']').join('') || '∅';
const pairCmp = (a, b) => a.k - b.k || a.q - b.q;

// Independent, quadratic definition: eliminate every dominated record at once.
function skyline(col) {
  return col.filter(e => !col.some(f => f.p >= e.p && pairCmp(f, e) >= 0 &&
    (f.p > e.p || pairCmp(f, e) > 0))).sort((a, b) => b.p - a.p);
}
const project = graph => key(graph.cols.map(skyline));
const countKey = (notation, raw) => notation.debug.counts(raw).map(String).join(',');
function invariant(graph) {
  for (let j = 0; j < graph.cols.length; j++) {
    const col = graph.cols[j];
    for (let i = 0; i < col.length; i++) {
      const e = col[i];
      assert.ok(e.k >= 0 && e.q >= 0 && e.k <= e.p && e.q <= e.p && e.p < j);
      if (i) assert.ok(col[i - 1].p > e.p && pairCmp(col[i - 1], e) < 0);
    }
  }
}
function smallEnough(graph, n) {
  const x = graph.cols.length - 1, col = graph.cols[x];
  if (!col?.length || n === 0) return true;
  const e = col.reduce((best, item) => !best || pairCmp(item, best) > 0 ||
    pairCmp(item, best) === 0 && item.p > best.p ? item : best, null);
  return x + n * (x - e.p) <= 18;
}

// Unaccelerated local rule, separately implemented; only used on small inputs.
function literalCounts(graph) {
  const answer = [];
  for (const source of graph.cols) {
    let col = source.slice(), steps = 1n, iterations = 0;
    while (col.length) {
      assert.ok(++iterations <= 100000, 'literal local-count iteration cap');
      const e = col[col.length - 1], rest = col.slice(0, -1);
      if (e.q) rest.push({ k: e.k, p: e.p, q: e.q - 1 });
      else if (e.k) rest.push({ k: e.k - 1, p: e.p, q: e.p });
      col = skyline(rest.concat(graph.cols[e.p]));
      steps++;
    }
    answer.push(steps.toString());
  }
  return answer.join(',');
}

async function main() {
  const started = performance.now(), deadline = started + 90000;
  const stats = { standard_states: 0, standard_steps: 0, raw_graphs: 0, raw_steps: 0,
    count_comparisons: 0, literal_count_comparisons: 0, count_decrements: 0,
    order_pairs: 0, adjacency_roundtrips: 0, rendered_graphs: 0, max_old_groups: 0,
    max_simplified_groups: 0 };
  const timeCheck = () => assert.ok(performance.now() < deadline, '90-second suite deadline');
  const seen = new Set(), imageSources = new Map(), queue = [];
  for (let n = 0; n <= 6; n++) {
    const raw = original.debug.seed(n).key;
    seen.add(raw); queue.push({ raw, depth: 0 });
  }
  for (let cursor = 0; cursor < queue.length; cursor++) {
    await freshTask(); timeCheck();
    const { raw, depth } = queue[cursor], g = original.debug.parse(raw), q = project(g);
    const s = simplified.debug.parse(raw);
    assert.equal(s.key, q); invariant(s);
    assert.equal(project(s), q);
    assert.equal(simplified.display.plain(q), q);
    assert.equal(simplified.is_limit(q), original.is_limit(raw));
    if (imageSources.has(q)) assert.equal(imageSources.get(q), raw, 'standard injectivity');
    imageSources.set(q, raw);
    const oldCounts = countKey(original, raw), newCounts = countKey(simplified, q);
    assert.equal(newCounts, oldCounts, `counts of ${raw}`); stats.count_comparisons++;
    stats.max_old_groups = Math.max(stats.max_old_groups, g.groups);
    stats.max_simplified_groups = Math.max(stats.max_simplified_groups, s.groups);
    const adjacency = simplified.debug.adjacency_text(q);
    assert.equal(simplified.debug.adjacency_from_text(adjacency), q);
    stats.adjacency_roundtrips++;
    let previous;
    for (let n = 0; n <= 4; n++) {
      if (!smallEnough(g, n)) continue;
      const oldChild = original.FS(raw, n), newChild = simplified.FS(q, n);
      const child = simplified.debug.parse(newChild);
      assert.equal(newChild, project(original.debug.parse(oldChild)), `FS(${raw}, ${n})`);
      invariant(child);
      if (previous) assert.equal(key(child.cols.slice(0, previous.cols.length)), previous.key);
      previous = child;
      if (g.cols.length) assert.ok(simplified.compare(newChild, q) < 0);
      if (n === 0) assert.equal(newChild, key(s.cols.slice(0, -1)));
      if (n === 1 && s.cols.at(-1)?.length) {
        const cs = simplified.debug.counts(newChild), before = simplified.debug.counts(q);
        const x = s.cols.length - 1;
        assert.equal(cs[x], before[x] - 1n);
        assert.equal(cs.slice(0, x).join(','), before.slice(0, x).join(','));
        stats.count_decrements++;
      }
      stats.standard_steps++;
      if (depth < 7 && seen.size < 1000 && !seen.has(oldChild)) {
        seen.add(oldChild); queue.push({ raw: oldChild, depth: depth + 1 });
      }
    }
    stats.standard_states++;
  }
  let randomState = 16092026;
  function random(n) { randomState = (Math.imul(randomState, 1664525) + 1013904223) >>> 0; return randomState % n; }
  for (let t = 0; t < 500; t++) {
    await freshTask(); timeCheck();
    const width = 2 + random(6), columns = Array.from({ length: width }, () => []);
    for (let j = 1; j < width; j++) for (let i = 0; i < random(3 * j + 1); i++) {
      const p = random(j); columns[j].push({ k: random(p + 1), p, q: random(p + 1) });
    }
    const g = original.debug.parse(key(columns)), q = project(g);
    assert.equal(simplified.display.plain(g.key), q);
    invariant(simplified.debug.parse(q));
    assert.equal(countKey(original, g.key), countKey(simplified, q)); stats.count_comparisons++;
    assert.equal(countKey(simplified, q), literalCounts(simplified.debug.parse(q)));
    stats.literal_count_comparisons++;
    for (let n = 0; n <= 4; n++) if (smallEnough(g, n)) {
      assert.equal(simplified.FS(q, n), project(original.debug.parse(original.FS(g.key, n))));
      stats.raw_steps++;
    }
    stats.raw_graphs++;
  }
  for (let t = 0; t < 3000; t++) {
    if (t % 50 === 0) { await freshTask(); timeCheck(); }
    const a = queue[random(queue.length)].raw, b = queue[random(queue.length)].raw;
    assert.equal(Math.sign(simplified.compare(a, b)), Math.sign(original.compare(a, b)));
    stats.order_pairs++;
  }
  for (let t = 0; t < 25; t++) {
    await freshTask(); timeCheck();
    const raw = queue[Math.floor(t * queue.length / 25)].raw;
    const g = simplified.debug.parse(raw), wanted = [];
    g.cols.forEach((col, j) => col.forEach(e => wanted.push([e.k, e.p, e.q, j].join(','))));
    const arc = simplified.debug.diagram(raw), table = simplified.debug.adjacency_diagram(raw);
    assert.equal(arc._anchored.complete, true);
    if (g.cols.length) {
      assert.equal(arc._anchored.groups, g.groups);
      assert.deepEqual(Array.from(arc._anchored.routes, e => [e.k, e.p, e.q, e.j].join(',')).sort(), wanted.slice().sort());
    }
    assert.equal(table._adjacency.complete, true);
    assert.deepEqual(Array.from(table._adjacency.entries, e => [e.k, e.p, e.q, e.j].join(',')).sort(), wanted.slice().sort());
    assert.equal(table._adjacency.countComplete, true);
    assert.equal(table.extra_text.filter(t => t._adjacency?.kind === 'diagonal-index').length,
      table._adjacency.layers.length * g.cols.length);
    assert.ok(simplified.debug.svg(raw).includes('<svg'));
    assert.ok(simplified.debug.adjacency_svg(raw).includes('<svg'));
    for (const view of [simplified.display, ...Object.values(simplified.display_equiv)]) {
      assert.equal(typeof view.plain(raw), 'string');
      assert.equal(typeof view.html(raw), 'string');
      assert.equal(typeof view.latex(raw), 'string');
      if (view.from_display) assert.equal(view.from_display(view.plain(raw)), g.key);
    }
    const displayed = simplified.draw_diagram.draw_diagram(raw, { current_equiv: '邻接表（图）' });
    assert.ok(displayed._adjacency);
    stats.rendered_graphs++;
  }
  await freshTask();
  assert.equal(simplified.id, 'ard-skyline-v01');
  assert.equal(simplified.name, 'ARD');
  assert.equal(original.name, 'ARD-legacy');
  assert.notEqual(simplified.id, original.id);
  assert.equal([simplified.display, ...Object.values(simplified.display_equiv)].filter(v => v.name === '列表').length, 1);
  assert.equal(Object.keys(simplified.display_equiv).length, 4);
  assert.equal(simplified.FS, simplified.FS_alter); assert.equal(simplified.FS, simplified.FS_short);
  assert.equal(simplified.display.plain('A3[1]'), '[][(0,0,0)][(1,1,0)]');
  assert.equal(countKey(simplified, 'A6'), '1,2,6,23,104,537');
  for (let n = 0; n <= 7; n++) assert.equal(simplified.FS('Limit of ARD', n), simplified.display.plain('A' + n));
  assert.equal(simplified.display.plain('Limit of Anchored-Rows'), 'Limit of ARD');
  assert.equal(simplified.display.plain('Limit[3][2]'), simplified.FS('A3', 2));
  assert.equal(simplified.FS('∅', 12345678901234567890n), '∅');
  assert.equal(simplified.FS('[]', 12345678901234567890n), '∅');
  assert.throws(() => simplified.FS('A2', -1), /指标/);
  assert.throws(() => simplified.FS('A2', 10000000000000000000n), /超限/);
  assert.throws(() => simplified.display.plain('A8193'), /超限/);
  assert.throws(() => simplified.display.plain('[][][(1,0,0)]'), /行锚/);
  assert.throws(() => simplified.debug.adjacency_from_text('[][][;0]'), /行锚/);
  assert.throws(() => simplified.debug.counts('A6', { maxWork: 0 }), /超限/);
  for (const raw of ['A2', '[][][][(0,2,2),(1,1,1)]', '[][][][(1,2,0)]']) {
    await freshTask();
    for (let n = 1; n <= 4; n++) assert.equal(simplified.FS(raw, n), project(original.debug.parse(original.FS(raw, n))));
  }
  stats.seconds = Math.round((performance.now() - started) / 10) / 100;
  stats.peak_rss_mib = Math.round(process.resourceUsage().maxRSS / 1024);
  console.log(JSON.stringify({ passed: true, ...stats }, null, 2));
}
main().catch(error => { console.error(error); process.exitCode = 1; });

