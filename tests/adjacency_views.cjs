'use strict';
// Bounded, portable adjacency-display audit. No network, subprocesses or file writes.
// Run: node --max-old-space-size=256 tests/adjacency_views.cjs
const fs = require('node:fs');
const path = require('node:path');
const vm = require('node:vm');
const crypto = require('node:crypto');
const assert = require('node:assert/strict');
const started = Date.now();
const counts = { graphs: 0, roundTrips: 0, expansions: 0, prefixes: 0, comparisons: 0,
  diagrams: 0, entries: 0, oldViews: 0, guards: 0 };
const names = ['RPD', 'ARD'], loaded = {}, helpers = [];
// Published source at commit 542d47a, normalized to LF with trailing whitespace removed.
const CORE_HASHES = {
  RPD: '91cd3b90aa91d8b1fdc887aec1727879df7ffc82a6bcc93564ee4f60b9f14ad0',
  ARD: '04b2856b3568862553b034d2b02f38db29c6559f157c1fed053ee8e2fcac0f08'
};
function load(source) {
  const context = vm.createContext({ queueMicrotask });
  context.register_notation = value => { assert(!context.ne); context.ne = value; };
  vm.runInContext(source, context, { timeout: 1200 });
  return context;
}
async function call(context, expression, args) {
  await Promise.resolve(); assert(Date.now() - started < 25000, '25-second test deadline');
  context.args = args;
  return vm.runInContext(expression, context, { timeout: 1500 });
}
const native = value => JSON.parse(JSON.stringify(value));
const textOf = columns => columns.length ? columns.map(col => '[' +
  col.map(e => '(' + e.join(',') + ')').join(',') + ']').join('') : '∅';
function groupsOf(text) {
  const groups = new Map(); let j = 0;
  for (const column of text.matchAll(/\[([^\]]*)\]/g)) {
    for (const triple of column[1].matchAll(/\((\d+),(\d+),(\d+)\)/g)) {
      const [k, p, q] = triple.slice(1).map(Number), key = [k, p, j].join(',');
      const old = groups.get(key);
      if (!old || q > old.q) groups.set(key, { k, p, q, j });
    }
    j++;
  }
  return { size: j, entries: [...groups.values()] };
}
const identities = entries => entries.map(e => [e.k, e.p, e.q, e.j].join(',')).sort();
function referenceText(text) {
  if (text === 'Limit' || text === 'Limit of ARD') return text;
  const { size, entries } = groupsOf(text), columns = Array.from({ length: size }, () => []);
  for (const { k, p, q, j } of entries) {
    columns[j][k] ??= []; columns[j][k][p] = String(q);
  }
  return size ? columns.map(col => '[' + Array.from(col, layer => layer ?
    Array.from(layer, value => value ?? '').join(',') : '').join(';') + ']').join('') : '∅';
}
function checkDiagram(diagram, expected) {
  assert(diagram._adjacency.complete);
  assert.deepEqual(identities(diagram._adjacency.entries), identities(expected.entries));
  if (expected.size) assert.equal(diagram._adjacency.columns, expected.size);
  for (const element of diagram.elements) for (const [x, y] of [[element.x1, element.y1], [element.x2, element.y2]]) {
    assert(Number.isFinite(x) && x >= 0 && x <= diagram.width);
    assert(Number.isFinite(y) && y >= 0 && y <= diagram.height);
  }
  for (const item of diagram.extra_text) {
    assert(item.x >= 0 && item.x <= diagram.width && item.y >= 0 && item.y <= diagram.height);
  }
  for (const entry of diagram._adjacency.entries) {
    const table = diagram._adjacency.layers.find(layer => layer.k === entry.k);
    assert.equal(entry.x, diagram._adjacency.columnXs[entry.j]);
    assert.equal(entry.y, table.y + (entry.p + 0.5) * diagram._adjacency.rowHeight);
    assert(entry.p < entry.j, 'Relation values stay strictly above the diagonal');
  }
  assert(diagram._adjacency.triangular);
  assert.equal(diagram.extra_text.filter(text => text._adjacency?.kind === 'counts').length, 1);
  assert.equal(diagram.extra_text[0]._adjacency.kind, 'counts');
  for (const text of diagram.extra_text)
    assert(['counts', 'layer', 'cell', 'diagonal-index'].includes(text._adjacency.kind),
      'No external column, parent-row, or corner label');
  for (const table of diagram._adjacency.layers) {
    const { cell, rowHeight } = diagram._adjacency;
    const texts = diagram.extra_text.filter(text => text._adjacency.k === table.k);
    const labels = texts.filter(text => text._adjacency.kind === 'diagonal-index');
    assert.equal(labels.length, expected.size);
    assert.deepEqual(labels.map(text => text.text), Array.from({ length: expected.size }, (_, j) => String(j)));
    assert.equal(texts.find(text => text._adjacency.kind === 'layer').text, table.k);
    const elements = diagram.elements.filter(element => element._adjacency.k === table.k);
    const backgrounds = elements.filter(element => element._adjacency.kind === 'diagonal-background');
    assert.equal(backgrounds.length, expected.size);
    for (let j = 0; j < expected.size; j++) {
      assert.equal(labels[j].x, table.x + (j + 0.5) * cell);
      assert.equal(labels[j].y, table.y + (j + 0.5) * rowHeight);
      assert.deepEqual([backgrounds[j].x1, backgrounds[j].x2], [table.x + j * cell, table.x + (j + 1) * cell]);
      assert.equal(backgrounds[j].y1, labels[j].y); assert.equal(backgrounds[j].y2, labels[j].y);
      assert.equal(backgrounds[j].width, rowHeight, 'Whole diagonal cell, not clipped in half');
      assert(backgrounds[j].stroke_color.color.a > 0);
    }
    const horizontal = elements.filter(element => element._adjacency.kind === 'grid-horizontal');
    const vertical = elements.filter(element => element._adjacency.kind === 'grid-vertical');
    assert.equal(horizontal.length, expected.size + 1); assert.equal(vertical.length, expected.size + 1);
    for (let r = 0; r <= expected.size; r++) {
      assert.deepEqual([horizontal[r].x1, horizontal[r].x2, horizontal[r].y1, horizontal[r].y2],
        [table.x + Math.max(0, r - 1) * cell, table.x + table.width, table.y + r * rowHeight, table.y + r * rowHeight]);
      assert.deepEqual([vertical[r].x1, vertical[r].x2, vertical[r].y1, vertical[r].y2],
        [table.x + r * cell, table.x + r * cell, table.y, table.y + Math.min(expected.size, r + 1) * rowHeight]);
    }
    assert.equal(elements.length, backgrounds.length + horizontal.length + vertical.length,
      'No slanted cut or grid cells below the diagonal');
  }
  if (expected.size) {
    assert.equal(diagram._adjacency.rowHeight, 14, 'Tight rows, without shrinking the 12px font');
    for (let j = 0; j < expected.size; j++)
      assert.equal(diagram._adjacency.columnWidths[j], Math.ceil(String(expected.size - 1).length * 7.4 + 3));
  }
  counts.diagrams++; counts.entries += expected.entries.length;
}
let randomState = 634771;
const random = n => { randomState = (Math.imul(randomState, 1664525) + 1013904223) >>> 0; return randomState % n; };
async function main() {
  for (const name of names) {
    const file = path.resolve(__dirname, '../notations', name === 'ARD' ? 'ARD-legacy' : name,
      name === 'RPD' ? 'RPD-mountain.ne-rewritten.js' : 'ARD-arcs.ne-rewritten.js');
    const source = fs.readFileSync(file, 'utf8').replace(/\r\n/g, '\n');
    const startMark = '(function (register_notation) {\n';
    const start = source.indexOf(startMark), end = source.indexOf('\n})(value => {', start);
    assert(start >= 0 && end > start, 'Published core wrapper is intact');
    const original = source.slice(start + startMark.length, end).trimEnd();
    assert.equal(crypto.createHash('sha256').update(original).digest('hex'), CORE_HASHES[name],
      'The exact previous published core remains embedded, without rule edits');
    const helperStart = source.indexOf('function addAdjacencyDisplays(');
    const helperEnd = source.indexOf('\naddAdjacencyDisplays(definition,', helperStart);
    assert(helperStart >= 0 && helperEnd > helperStart);
    helpers.push(source.slice(helperStart, helperEnd));
    const old = load(original), next = load(source); loaded[name] = next;
    if (name === 'RPD') {
      assert.equal(next.ne.name, 'RDP'); assert.equal(next.ne.simple_name, 'RDP');
    }
    assert.equal(Object.keys(next.ne.display_equiv).length, Object.keys(old.ne.display_equiv).length + 2);
    assert.notEqual(next.ne.id, old.ne.id, 'Original and trial can coexist');
    for (const key of Object.keys(old.ne.display_equiv)) assert(key in next.ne.display_equiv);
    const raws = ['∅', '[]', '[][][]', name === 'RPD' ? 'Limit' : 'Limit of ARD'];
    for (let n = 0; n <= 4; n++) {
      const seed = name === 'RPD' ? 'Limit[' + n + ']' : 'A' + n;
      raws.push(seed);
      for (const index of [1, 2]) raws.push(await call(old, 'ne.FS(args.raw,args.n)', { raw: seed, n: index }));
    }
    for (let t = 0; t < 65; t++) {
      const columns = Array.from({ length: 1 + random(7) }, () => []);
      for (let j = 1; j < columns.length; j++) for (let a = 0, total = random(6); a < total; a++) {
        const k = random(name === 'ARD' ? j : 5), p = random(j), q = random(p + 1);
        columns[j].push([k, p, q]);
      }
      raws.push(textOf(columns));
    }
    for (const raw of raws) {
      const canonical = await call(old, 'ne.display.plain(args)', raw);
      const display = await call(next, 'ne.debug.adjacency_text(args)', raw);
      assert.equal(display, referenceText(canonical), name + ' positional text');
      assert.equal(await call(next, 'ne.debug.adjacency_from_text(args)', display), canonical);
      counts.roundTrips++; counts.graphs++;
      for (let n = 0; n < 4; n++) {
        assert.equal(await call(next, 'ne.FS(args.raw,args.n)', { raw, n }),
          await call(old, 'ne.FS(args.raw,args.n)', { raw, n }));
        counts.expansions++;
      }
      if (canonical !== 'Limit' && canonical !== 'Limit of ARD') {
        let previous;
        for (let n = 0; n < 4; n++) {
          const text = await call(next, 'ne.debug.adjacency_text(ne.FS(args.raw,args.n))', { raw, n });
          if (previous !== undefined && previous !== '∅') assert(text.startsWith(previous),
            'Appending columns never rewrites earlier textual columns');
          previous = text;
        }
        counts.prefixes += 3;
      }
      const diagram = native(await call(next, 'ne.debug.adjacency_diagram(args)', raw));
      if (canonical === 'Limit' || canonical === 'Limit of ARD') assert(diagram._adjacency.complete);
      else {
        checkDiagram(diagram, groupsOf(canonical));
        const key = name === 'RPD' ? '数字序列' : '计数序列';
        assert.equal(diagram._adjacency.countText, await call(old, 'ne.display_equiv[args.key].plain(args.raw)', { key, raw }),
          'Counts above the tables reuse the original exact display');
      }
      const popup = native(await call(next,
        "ne.draw_diagram.draw_diagram(args,{...ne.draw_diagram.default_data,current_equiv:'邻接表（图）'})", raw));
      assert.deepEqual(popup, diagram, 'Native NER popup selects the matching new view');
      const flipped = native(await call(next, 'ne.debug.adjacency_diagram(args,{invert_vertical:true})', raw));
      assert.deepEqual(identities(flipped._adjacency.entries), identities(diagram._adjacency.entries));
      const svg = await call(next, 'ne.debug.adjacency_svg(args)', raw);
      assert.equal((svg.match(/data-adjacency=/g) || []).length, diagram._adjacency.entries.length);
      assert(svg.includes('font-family:inherit'));
      for (const [key, spec] of Object.entries(old.ne.display_equiv)) {
        if (!spec.plain) continue;
        // Trace histories are intentionally session-dependent and not an encoding.
        if (key === '操作序列') continue;
        assert.equal(await call(next, 'ne.display_equiv[args.key].plain(args.raw)', { key, raw }),
          await call(old, 'ne.display_equiv[args.key].plain(args.raw)', { key, raw }));
        counts.oldViews++;
      }
    }
    for (let i = 0; i < 80; i++) {
      const args = { a: raws[random(raws.length)], b: raws[random(raws.length)] };
      assert.equal(await call(next, 'ne.compare(args.a,args.b)', args), await call(old, 'ne.compare(args.a,args.b)', args));
      counts.comparisons++;
    }
    for (const raw of ['[0]', '[][1]', '[][,0]', '[][-1]', '[][0]junk', '[1.5]', '[][0,,]']) {
      await assert.rejects(() => call(next, 'ne.debug.adjacency_from_text(args)', raw)); counts.guards++;
    }
  }
  assert.equal(helpers[0], helpers[1], 'Both notations share the same presentation-only helper');
  const ard = loaded.ARD, rpd = loaded.RPD;
  assert.equal(await call(ard, 'ne.debug.adjacency_text(args)', 'A3[2]'),
    '[][0][0,1;,0][0,,2;,,2;,,1]');
  assert.equal(await call(rpd, 'ne.debug.adjacency_text(args)', '[][(0,0,0),(2,0,0)]'), '[][0;;0]');
  assert.equal(await call(ard, 'ne.debug.adjacency_text(args)', '[][][][(0,0,0),(0,2,2),(1,1,1)]'),
    '[][][][0,,2;,1]');
  await assert.rejects(() => call(ard, 'ne.debug.adjacency_from_text(args)', '[][][;;0]'));
  assert.equal(await call(rpd, 'ne.debug.adjacency_from_text(args)', '[][][;;0]'), '[][][(2,0,0)]');
  await assert.rejects(() => call(rpd, 'ne.debug.adjacency_text(args)', '[][(1000000,0,0)]'), /超限/);
  const hugeLayer = native(await call(rpd, 'ne.debug.adjacency_diagram(args)', '[][(1000000,0,0)]'));
  assert.equal(hugeLayer._adjacency.layers[0].k, '1000000', 'Do not renumber sparse high layers');
  const tooWide = native(await call(ard, "ne.draw_diagram.draw_diagram(args,{current_equiv:'邻接表（图）'})", '8192'));
  assert(tooWide._adjacency.complete, 'All-empty natural numbers need no tables');
  assert.equal(tooWide._adjacency.entries.length, 0); assert.equal(tooWide._adjacency.layers.length, 0);
  assert.equal(tooWide._adjacency.countComplete, false);
  assert.match(tooWide._adjacency.countText, /未截断/);
  const multiDigit = '[]'.repeat(12) + '[(0,10,10),(0,11,11),(2,9,9)]';
  for (const next of [rpd, ard]) {
    const compact = native(await call(next, 'ne.debug.adjacency_diagram(args)', multiDigit));
    checkDiagram(compact, groupsOf(multiDigit));
    assert.equal(compact._adjacency.columnWidths[9], 18);
    assert.equal(compact._adjacency.columnWidths[10], 18);
    assert.deepEqual(native(await call(next, 'ne.debug.adjacency_diagram(args,{column_gap:100})', multiDigit)), compact,
      'Original arc/mountain spacing does not make the new tables loose');
    const warning = native(await call(next, `(() => {
      const spec = ne.display_equiv['数字序列'] || ne.display_equiv['计数序列'], original = spec.plain;
      spec.plain = () => '（计数超限；未返回近似数字）';
      try { return ne.debug.adjacency_diagram(args); } finally { spec.plain = original; }
    })()`, multiDigit));
    assert(warning._adjacency.complete); assert.equal(warning._adjacency.countComplete, false);
    assert.deepEqual(warning._adjacency.entries, compact._adjacency.entries,
      'An explicit count warning must not hide or truncate a complete graph');
    counts.guards++;
  }
  counts.guards += 4;
  console.log(JSON.stringify({ status: 'passed', ...counts, ms: Date.now() - started,
    rssMiB: Math.round(process.memoryUsage().rss / 1024 / 1024) }));
}
main().catch(error => { console.error(error); process.exitCode = 1; });
