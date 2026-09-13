'use strict';

// Bounded, portable geometric contract audit for the published ARD renderer.
// Run: node --max-old-space-size=192 ard_arcs.cjs
// No browser, subprocess, network, screenshot or file-writing side effects.
const fs = require('node:fs');
const path = require('node:path');
const vm = require('node:vm');
const assert = require('node:assert/strict');
const crypto = require('node:crypto');

let oldSpaceMiB;
for (let i = 0; i < process.execArgv.length; i++) {
  const match = process.execArgv[i].match(/^--max[-_]old[-_]space[-_]size=(\d+)$/);
  if (match) oldSpaceMiB = Number(match[1]);
  else if (/^--max[-_]old[-_]space[-_]size$/.test(process.execArgv[i]))
    oldSpaceMiB = Number(process.execArgv[++i]);
}
assert(Number.isInteger(oldSpaceMiB) && oldSpaceMiB > 0 && oldSpaceMiB < 256,
  'Run with node --max-old-space-size=192 ard_arcs.cjs (old heap strictly below 256 MiB)');

const started = Date.now(), DEADLINE_MS = 19000;
function deadline() { assert(Date.now() - started < DEADLINE_MS, '19-second total test budget'); }
const newPath = path.join(__dirname, '..', 'notations', 'ARD', 'ARD-arcs.ne-rewritten.js');
const arcSource = fs.readFileSync(newPath, 'utf8');
const digest = source => crypto.createHash('sha256').update(source).digest('hex');
const releaseDigest = digest(arcSource);
assert(!/^\s*(?:import|export)\b/m.test(arcSource), 'Standalone classic script');

const ctx = vm.createContext({ queueMicrotask });
let registrations = 0;
ctx.register_notation = definition => { ctx.arcs = definition; registrations++; };
vm.runInContext(arcSource, ctx, { timeout: 1000, filename: path.basename(newPath) });
assert.equal(registrations, 1);
async function invoke(expression, args) {
  await Promise.resolve(); deadline(); ctx.args = args;
  return vm.runInContext(expression, ctx, { timeout: 1250 });
}
const native = value => JSON.parse(JSON.stringify(value));
const near = (a, b) => Math.abs(a - b) <= 0.001;
function point(p) {
  const answer = Array.isArray(p) ? { x: p[0], y: p[1] } : p;
  assert(answer && Number.isFinite(answer.x) && Number.isFinite(answer.y), 'Finite point');
  return answer;
}
function equalPoint(a, b) {
  a = point(a); b = point(b); return near(a.x, b.x) && near(a.y, b.y);
}
function graphText(columns) {
  return columns.length ? columns.map(column => '[' + column.map(edge => '(' + edge.join(',') + ')').join(',') + ']').join('') : '∅';
}
function parseCanonical(text) {
  if (text === '∅') return [];
  let consumed = '';
  const columns = [...text.matchAll(/\[([^\]]*)\]/g)].map(match => {
    consumed += match[0];
    const triples = [...match[1].matchAll(/\((\d+),(\d+),(\d+)\)/g)].map(m => m.slice(1).map(Number));
    assert.equal(match[1].replace(/\((\d+),(\d+),(\d+)\)/g, '').replaceAll(',', ''), '');
    return triples;
  });
  assert.equal(consumed, text); return columns;
}
function identity(route) { return [route.k, route.p, route.q, route.j].join(','); }
function intersects(a, b) {
  return Math.min(a.x + a.width, b.x + b.width) > Math.max(a.x, b.x) + 0.001 &&
    Math.min(a.y + a.height, b.y + b.height) > Math.max(a.y, b.y) + 0.001;
}
function liesOnSegment(p, a, b) {
  p = point(p); a = point(a); b = point(b);
  const length = Math.max(1, Math.hypot(b.x - a.x, b.y - a.y));
  return Math.abs((p.x - a.x) * (b.y - a.y) - (p.y - a.y) * (b.x - a.x)) <= 0.001 * length &&
    p.x >= Math.min(a.x, b.x) - 0.001 && p.x <= Math.max(a.x, b.x) + 0.001 &&
    p.y >= Math.min(a.y, b.y) - 0.001 && p.y <= Math.max(a.y, b.y) + 0.001;
}
const counters = { randomCases: 0, expansionCases: 0, comparisonCases: 0, countCases: 0,
  renderedCases: 0, renderedRelations: 0, laneChecks: 0, labelPairChecks: 0,
  drawnSegmentChecks: 0, rootFrames: 0, rootFrameSegments: 0, flipPairs: 0, guardCases: 0 };

function verifyRootFrame(diagram, route) {
  const box = route.label, id = identity(route);
  assert.equal(box.height, 18, 'Root outline reserves an 18-pixel-tall box');
  assert.equal(box.width, String(route.q).length * 8 + 10);
  const frame = diagram.elements.filter(element => element._anchored?.kind === 'root-frame' &&
    identity(element._anchored) === id);
  assert(frame.length >= 16, 'Every root has a finely segmented closed outline');
  const vertices = [];
  let areaTwice = 0;
  for (let i = 0; i < frame.length; i++) {
    const edge = frame[i], next = frame[(i + 1) % frame.length];
    assert.equal(edge.type, 'line', 'Root frames use host-supported line primitives');
    const a = { x: edge.x1, y: edge.y1 }, b = { x: edge.x2, y: edge.y2 };
    assert(equalPoint(b, { x: next.x1, y: next.y1 }), 'Adjacent root-frame segments close continuously');
    assert(!equalPoint(a, b), 'No degenerate frame segment');
    vertices.push(a);
    areaTwice += a.x * b.y - b.x * a.y;
    for (const p of [a, b]) {
      assert(p.x >= box.x - 0.001 && p.x <= box.x + box.width + 0.001 &&
        p.y >= box.y - 0.001 && p.y <= box.y + box.height + 0.001,
      'Every frame point stays inside its reserved label box');
      // A capsule is the fixed-radius neighborhood of a horizontal segment.
      // With one digit this segment degenerates to a point, giving a circle.
      const radius = box.height / 2, centerY = box.y + radius;
      const spineX = Math.max(box.x + radius, Math.min(box.x + box.width - radius, p.x));
      assert(near(Math.hypot(p.x - spineX, p.y - centerY), radius),
        'Single digits use a circle; multiple digits use a capsule outline');
    }
  }
  for (let i = 0; i < vertices.length; i++) for (let j = 0; j < i; j++)
    assert(!equalPoint(vertices[i], vertices[j]), 'Exactly one outline traversal, not duplicate closed loops');
  assert(Math.abs(areaTwice) / 2 > box.width * box.height * 0.6, 'Frame encloses the numeral region');
  const topSegments = diagram.elements.filter(element => element.type === 'line' &&
    ['relation', 'arc-segment'].includes(element._anchored?.kind) &&
    identity(element._anchored) === id && near(element.y1, route.y) && near(element.y2, route.y));
  const endpoints = topSegments.flatMap(element => [
    { x: element.x1, y: element.y1 }, { x: element.x2, y: element.y2 },
  ]);
  const left = { x: box.x, y: box.y + box.height / 2 };
  const right = { x: box.x + box.width, y: box.y + box.height / 2 };
  assert(endpoints.some(p => equalPoint(p, left)), 'Left arc reaches the frame exactly, with no extra gap');
  assert(endpoints.some(p => equalPoint(p, right)), 'Right arc reaches the frame exactly, with no extra gap');
  assert(vertices.some(p => equalPoint(p, left)) && vertices.some(p => equalPoint(p, right)),
    'Arc attachment points are actual frame vertices');
  counters.rootFrames++; counters.rootFrameSegments += frame.length;
}

function verifyDiagram(diagram, canonical, expectedCounts) {
  deadline();
  assert(Number.isFinite(diagram.width) && diagram.width > 0);
  assert(Number.isFinite(diagram.height) && diagram.height > 0);
  assert(Array.isArray(diagram.elements) && Array.isArray(diagram.extra_text));
  const data = diagram._anchored;
  assert(data && data.complete === true, 'Finite small graph must be fully rendered');
  assert.equal(data.layout, 'row-arcs');
  const columns = parseCanonical(canonical), expectedRelations = [];
  columns.forEach((column, j) => column.forEach(([k, p, q]) => expectedRelations.push([k, p, q, j].join(','))));
  assert.equal(data.columns, columns.length);
  assert.equal(data.groups, expectedRelations.length);
  assert.equal(data.rows, new Set(expectedRelations.map(e => Number(e.split(',')[0]))).size);
  assert.deepEqual(Array.from(data.counts, String), expectedCounts);
  assert(Array.isArray(data.routes));
  assert.deepEqual(data.routes.map(identity).sort(), expectedRelations.sort(),
    'Every compressed group occurs exactly once; no hidden or duplicated relationship');
  const tagged = diagram.elements.filter(element => element._anchored?.kind === 'relation');
  assert.deepEqual(tagged.map(element => identity(element._anchored)).sort(), expectedRelations.sort(),
    'Every group also has exactly one actual rendered relationship marker');
  const byIdentity = new Map(data.routes.map(route => [identity(route), route]));
  assert.equal(data.columnXs.length, columns.length);
  assert.equal(data.columnCells.length, columns.length);
  function inside(p) {
    p = point(p);
    assert(p.x >= -0.001 && p.x <= diagram.width + 0.001, 'x inside declared canvas');
    assert(p.y >= -0.001 && p.y <= diagram.height + 0.001, 'y inside declared canvas');
  }
  for (const element of diagram.elements) {
    assert(['line', 'circle', 'text'].includes(element.type), 'Native NER primitive only');
    if (element.type === 'line') {
      inside({ x: element.x1, y: element.y1 }); inside({ x: element.x2, y: element.y2 });
      assert(element.stroke === true);
      if (['relation', 'arc-segment'].includes(element._anchored?.kind)) {
        const route = byIdentity.get(identity(element._anchored));
        assert(route, 'Every drawn arc segment belongs to a real relation');
        const a = { x: element.x1, y: element.y1 }, b = { x: element.x2, y: element.y2 };
        assert(route.points.slice(1).some((end, i) =>
          liesOnSegment(a, route.points[i], end) && liesOnSegment(b, route.points[i], end)),
        'Actual broken drawing segment is a subsegment of its complete logical route');
        counters.drawnSegmentChecks++;
      }
      if (element._anchored?.kind === 'root-frame')
        assert(byIdentity.has(identity(element._anchored)), 'No frame for a nonexistent mathematical group');
    } else {
      inside(element);
      if (element.type === 'circle') {
        assert(Number.isFinite(element.r) && element.r >= 0);
        inside({ x: element.x - element.r, y: element.y - element.r });
        inside({ x: element.x + element.r, y: element.y + element.r });
      } else assert.equal(typeof element.text, 'string');
    }
  }
  for (const label of diagram.extra_text) { inside(label); assert.equal(typeof label.text, 'string'); }
  const topLabels = diagram.extra_text.filter(label => label._anchored?.kind === 'column');
  assert.equal(topLabels.length, columns.length, 'Exactly one exact numeric count per column');
  for (let j = 0; j < columns.length; j++) {
    const label = topLabels.find(item => item._anchored.j === j);
    assert(label, 'Column count is labeled');
    assert.equal(label.text, expectedCounts[j]);
    assert(near(label.x, data.columnXs[j]));
    assert(data.columnCells[j].left <= label.x && label.x <= data.columnCells[j].right);
  }
  for (let i = 0; i < data.routes.length; i++) {
    const route = data.routes[i], box = route.label;
    for (const coordinate of ['k', 'p', 'q', 'j', 'lane'])
      assert(Number.isSafeInteger(route[coordinate]) && route[coordinate] >= 0);
    assert(route.k < route.j && route.q <= route.p && route.p < route.j);
    assert(Number.isFinite(route.x1) && Number.isFinite(route.x2) && route.x1 < route.x2);
    assert(Number.isFinite(route.y) && Number.isFinite(route.base) && route.y !== route.base);
    assert(Array.isArray(route.points) && route.points.length >= 4, 'Complete logical arc polyline');
    route.points.forEach(inside);
    inside(route.sourcePort); inside(route.parentPort);
    const first = route.points[0], last = route.points.at(-1);
    assert(equalPoint(first, route.sourcePort) && equalPoint(last, route.parentPort) ||
      equalPoint(first, route.parentPort) && equalPoint(last, route.sourcePort), 'Polyline connects the declared endpoints');
    for (const [port, column] of [[route.sourcePort, route.j], [route.parentPort, route.p]]) {
      const p = point(port), cell = data.columnCells[column];
      assert(p.x >= cell.left && p.x <= cell.right, 'Port belongs to its actual parent/child column cell');
      assert(near(p.y, route.base), 'Both ports attach to their row baseline');
    }
    assert(box && Number.isFinite(box.width) && box.width > 0 && Number.isFinite(box.height) && box.height > 0);
    inside(box); inside({ x: box.x + box.width, y: box.y + box.height });
    const rootLabels = diagram.extra_text.filter(label => label._anchored?.kind === 'root' && identity(label._anchored) === identity(route));
    assert.equal(rootLabels.length, 1, 'Exactly one numerical root label per group');
    assert.equal(rootLabels[0].text, String(route.q));
    assert(!rootLabels[0].text.includes('q='));
    assert(rootLabels[0].x >= box.x && rootLabels[0].x <= box.x + box.width &&
      rootLabels[0].y >= box.y && rootLabels[0].y <= box.y + box.height, 'Label point lies inside advertised label box');
    verifyRootFrame(diagram, route);
    for (let j = 0; j < i; j++) {
      const other = data.routes[j]; counters.labelPairChecks++;
      assert(!intersects(box, other.label), 'Distinct root-label boxes do not overlap');
      if (route.k === other.k && route.lane === other.lane) {
        counters.laneChecks++;
        assert(route.j < other.p || other.j < route.p,
          'Same-row same-lane closed column intervals do not overlap or share a column');
        assert(route.x2 < other.x1 || other.x2 < route.x1, 'Same-lane actual x intervals do not overlap');
      }
    }
  }
  counters.renderedCases++; counters.renderedRelations += data.routes.length;
  return diagram;
}

function verifyFlip(normal, flipped) {
  assert.equal(normal.width, flipped.width); assert.equal(normal.height, flipped.height);
  const routes = normal._anchored.routes, other = new Map(flipped._anchored.routes.map(route => [identity(route), route]));
  let mirror;
  for (const route of routes) {
    const reverse = other.get(identity(route)); assert(reverse);
    assert.equal(route.lane, reverse.lane);
    assert(near(route.x1, reverse.x1) && near(route.x2, reverse.x2));
    assert.equal(route.points.length, reverse.points.length);
    const sum = route.base + reverse.base;
    if (mirror === undefined) mirror = sum;
    assert(near(sum, mirror));
    assert(near(route.y + reverse.y, mirror));
    assert((route.y - route.base) * (reverse.y - reverse.base) < 0);
    route.points.forEach((p, i) => {
      p = point(p); const q = point(reverse.points[i]);
      assert(near(p.x, q.x) && near(p.y + q.y, mirror), 'All route points are final flipped coordinates');
    });
    assert(near(route.label.x, reverse.label.x));
    assert(near(route.label.y + reverse.label.y + route.label.height, mirror));
    const filterFrame = diagram => diagram.elements.filter(element =>
      element._anchored?.kind === 'root-frame' && identity(element._anchored) === identity(route));
    const frame = filterFrame(normal), reversedFrame = filterFrame(flipped);
    assert.equal(frame.length, reversedFrame.length);
    frame.forEach((edge, i) => {
      const reversed = reversedFrame[i];
      assert(near(edge.x1, reversed.x1) && near(edge.x2, reversed.x2));
      assert(near(edge.y1 + reversed.y1, mirror) && near(edge.y2 + reversed.y2, mirror),
        'Every actual frame segment uses final flipped coordinates');
    });
  }
  counters.flipPairs++;
}

let rng = 0x5a17e9b3;
function random(max) {
  rng ^= rng << 13; rng ^= rng >>> 17; rng ^= rng << 5;
  return (rng >>> 0) % max;
}
function randomGraph() {
  return graphText(Array.from({ length: random(9) }, (_, j) => {
    const column = [];
    if (j) for (let i = random(7); i > 0; i--) {
      const p = random(j); column.push([random(j), p, random(p + 1)]);
    }
    return column;
  }));
}

async function render(raw, invert = false) {
  const result = await invoke(`({canonical:arcs.display.plain(args[0]),
    counts:arcs.debug.counts(args[0]).map(String),
    diagram:arcs.debug.diagram(args[0],{column_gap:40,invert_vertical:args[1]})})`, [raw, invert]);
  return verifyDiagram(native(result.diagram), result.canonical, Array.from(result.counts));
}

async function main() {
  assert.equal(await invoke('arcs.id'), 'ard-adjacency-v01');
  assert.equal(await invoke('arcs.name'), 'ARD（邻接表试用版）');
  assert.equal(await invoke('arcs.display.name'), '列表');
  assert.deepEqual(native(await invoke('Object.keys(arcs.display_equiv)')),
    ['计数序列', '弧线图', '邻接表（文字）', '邻接表（图）']);
  assert(await invoke('arcs.FS===arcs.FS_alter && arcs.FS===arcs.FS_short'));
  assert(await invoke('!arcs.display_equiv["计数序列"].from_display'));
  assert.deepEqual(native(await invoke('arcs.init()')), ['Limit of ARD', '[]', '∅']);

  const pool = ['∅', '[]', 'A2', 'A3', 'A4[2]', 'A3[3]'];
  for (let i = 0; i < 240; i++) {
    const raw = randomGraph(), comparison = pool[random(pool.length)], index = random(4);
    const result = await invoke(`(() => {
      function test(n) {return {canonical:n.display.from_display(args[0]),
        fs:n.FS(args[0],args[2]),big:n.FS(args[0],BigInt(args[2])),
        compare:Math.sign(n.compare(args[0],args[1])),reverse:Math.sign(n.compare(args[1],args[0])),
        limit:n.is_limit(args[0]),
        counts:n.debug.counts(args[0]).map(String),countText:n.display_equiv['计数序列'].plain(args[0])};}
      return {now:test(arcs)};
    })()`, [raw, comparison, index]);
    assert.equal(result.now.compare, -result.now.reverse || 0, 'Comparison antisymmetry');
    assert.equal(await invoke('arcs.display.plain(args)', result.now.canonical), result.now.canonical);
    assert.equal(result.now.fs, result.now.big);
    const columns = parseCanonical(result.now.canonical);
    assert.equal(result.now.limit, Boolean(columns.at(-1)?.length));
    assert.equal(result.now.counts.length, columns.length);
    assert(result.now.counts.every(value => BigInt(value) >= 1n));
    assert.equal(result.now.countText, result.now.counts.length ? result.now.counts.join(',') : '0');
    if (pool.length < 60) pool.push(result.now.canonical);
    counters.randomCases++; counters.expansionCases += 2; counters.comparisonCases += 2; counters.countCases++;
    if (i < 12 && result.now.canonical !== '∅') await render(result.now.canonical);
  }

  for (const raw of ['A3', 'A4[2]', 'A3[3]', '[][(0,0,0)][][][(3,1,1),(1,3,2),(0,2,2)]']) {
    const ordinary = await render(raw), flipped = await render(raw, true); verifyFlip(ordinary, flipped);
    const svg = await invoke('arcs.display_equiv["弧线图"].html(args)', raw);
    assert(svg.includes('<svg') && svg.includes('font-family:inherit'));
    assert(!/<script\b|onload=|onclick=|<image\b/i.test(svg), 'Self-contained declarative SVG');
  }
  // Dense, independently handwritten legal graph: long, nested and crossing
  // parent intervals, including row anchors that lie after their parents.
  const dense = graphText(Array.from({ length: 8 }, (_, j) => {
    const col = [];
    for (let k = 0; k < j; k++) for (let p = 0; p < j; p++) col.push([k, p, p]);
    return col;
  }));
  verifyFlip(await render(dense), await render(dense, true));

  // BigInt labels beyond signed 64-bit, with long adjacent-column intervals.
  const long = '[]' + Array.from({ length: 69 }, (_, j) => '[(0,' + j + ',' + j + ')]').join('');
  const values = await invoke('arcs.debug.counts(args).map(String)', long);
  for (let j = 0; j < values.length; j++) assert.equal(values[j], String(1n << BigInt(j)));
  assert(BigInt(values.at(-1)) > 2n ** 63n);
  counters.countCases++;
  verifyFlip(await render(long), await render(long, true));

  const limits = native(await invoke('arcs.debug.limits'));
  const rowSize = Math.floor(Math.sqrt(limits.drawGroups)) + 1;
  const tooMany = graphText([...Array.from({ length: rowSize }, () => []),
    Array.from({ length: rowSize * rowSize }, (_, i) => [Math.floor(i / rowSize), i % rowSize, 0])]);
  const refused = await invoke('arcs.draw_diagram.draw_diagram(args,{})', tooMany);
  assert.equal(refused._anchored.complete, false);
  assert.equal(refused.elements.length, 0, 'Over-limit rendering never returns a partial graph');
  assert(refused.extra_text.some(label => /超限/.test(label.text)));
  assert(!refused._anchored.routes || refused._anchored.routes.length === 0);
  counters.guardCases++;
  await assert.rejects(() => invoke('arcs.debug.diagram(args,{})', tooMany), /超限/); counters.guardCases++;
  await assert.rejects(() => invoke('arcs.debug.counts("A3",{maxWork:1})'), /超限/); counters.guardCases++;
  for (const raw of ['[][(1,0,0)]', '[][(0,1,0)]', '[][(0,0,1)]', 'A3[-1]', '<svg onload=alert(1)>']) {
    await assert.rejects(() => invoke('arcs.display.from_display(args)', raw)); counters.guardCases++;
  }
  assert.equal(digest(fs.readFileSync(newPath, 'utf8')), releaseDigest, 'Renderer is read-only during testing');
  deadline();
  console.log(JSON.stringify({ status: 'passed', file: path.basename(newPath),
    releaseSha256: releaseDigest, oldSpaceMiB, ...counters,
    elapsedMs: Date.now() - started, rssMiB: Math.round(process.memoryUsage().rss / 1048576),
    scope: 'Independent bounded geometry and root-frame audit; Python/NER rule equivalence is checked separately. No live browser or screenshot test.' }, null, 2));
}

main().catch(error => { console.error(error); process.exitCode = 1; });
