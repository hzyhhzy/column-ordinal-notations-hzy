/** Full profile-layer diagrams, not a claimed reconstruction of wY mountains. */
export const escape = text => String(text).replace(/[&<>"']/g, c => ({'&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;'}[c]));
export function polynomialText(powers) {
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
export function compareCantor(a, b, tick = () => {}) {
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
export function decodeCantor(g, K) {
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
export function cantorText(cnf, options = {}) {
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
export function unavailable(reason) {
  return {width: 620, height: 44, elements: [], extra_text: [
    {text: '完整图暂不可显示：' + reason, x: 8, y: 20, size: 12, color: {type: 'text'}, align: 'left'}],
    _omegaCWY2: {complete: false, reason}};
}
export function mountain(g, K, settings = {}) {
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
export function withCounts(diagram, counts) {
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
export function svg(diagram, staticColors = false) {
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
