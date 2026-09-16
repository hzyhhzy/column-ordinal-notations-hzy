/* CWY2 direct-column research kernel, 2026-09-16.
 * No numeric wY engine, geometry, heights, nodes or stored expansion history.
 * Current status: finite tests only; see README before treating as equivalent.
 * Data: columns of [parent, nondecreasing normalized address word].
 */

export function compareWords(a, b) {
  if (a[0] !== b[0]) return Math.sign(a[0] - b[0]);
  if (a.length !== b.length) return Math.sign(a.length - b.length);
  for (let i = 1; i < a.length; i++)
    if (a[i] !== b[i]) return Math.sign(a[i] - b[i]);
  return 0;
}

export function normalizeWord(word) {
  let start = 0;
  while (start + 1 < word.length && word[start] === word[start + 1]) start++;
  return word.slice(start);
}

export function skyline(rows) {
  const largest = new Map();
  for (const [p, word] of rows)
    if (!largest.has(p) || compareWords(word, largest.get(p)) > 0) largest.set(p, word);
  const result = [];
  for (const [p, word] of [...largest].sort((a, b) => b[0] - a[0]))
    if (!result.length || compareWords(result.at(-1)[1], word) < 0) result.push([p, word]);
  return result;
}

const lift = (word, from, to) => word.map(q => q === from ? to : q);

// Look below the original cap in its origin column. Do NOT graft a new tail.
export function belowOrigin(columns, word) {
  const origin = word.at(-1);
  let previous = null;
  for (const [parent, maximum] of columns[origin]) {
    if (compareWords(maximum, word) < 0) { previous = maximum; continue; }
    const lower = word.slice();
    lower[lower.indexOf(origin)] = parent;
    const normalized = normalizeWord(lower);
    return previous && compareWords(previous, normalized) > 0 ? previous : normalized;
  }
  return previous;
}

export function removeOriginalTop(columns, column = columns.at(-1), child = columns.length - 1) {
  const [parent, word] = column.at(-1), lower = belowOrigin(columns, word);
  return skyline([...column.slice(0, -1),
    ...(lower ? [[parent, lift(lower, word.at(-1), child)]] : [])]);
}

export function minusColumn(columns) {
  const child = columns.length - 1, column = columns[child];
  if (!column?.length) throw Error('Expected a nonempty limit column');
  const parent = column.at(-1)[0];
  return skyline([...removeOriginalTop(columns),
    ...columns[parent].map(([p, word]) => [p, lift(word, parent, child)])]);
}

// The optional long convention retains the final lowered column, as wY does.
export function fs(columns, index, maxColumns = 20000, longer = false) {
  if (!Number.isSafeInteger(index) || index < 0) throw Error('Index must be a natural safe integer');
  if (!columns.length) return [];
  if ((!index && !longer) || !columns.at(-1).length) return columns.slice(0, -1);
  const last = columns.length - 1, cut = columns[last].at(-1)[0], width = last - cut;
  if (last + index * width + Number(longer) > maxColumns) throw Error('Output column budget exceeded');
  const lowered = minusColumn(columns), result = columns.slice(0, last);
  function moved(column, block) {
    const shift = q => q < cut ? q : q + block * width;
    return column.map(([p, word]) => [shift(p), word.map(shift)]);
  }
  for (let block = 0; block < index; block++) {
    result.push(moved(lowered, block));
    for (let k = cut + 1; k < last; k++) result.push(moved(columns[k], block + 1));
  }
  if (longer) result.push(moved(lowered, index));
  return result;
}

export function seed(m) {
  if (!Number.isSafeInteger(m) || m < 1 || m > 10000) throw Error('Seed out of range');
  return m === 1 ? [[], []] : [[], [[0, [0, ...Array(m - 2).fill(1)]]]];
}

export function compare(a, b) {
  function lex(x, y, cmp) {
    for (let i = 0; i < Math.min(x.length, y.length); i++) {
      const result = cmp(x[i], y[i]);
      if (result) return result;
    }
    return Math.sign(x.length - y.length);
  }
  return lex(a, b, (x, y) => lex(x, y,
    (v, w) => Math.sign(v[0] - w[0]) || compareWords(v[1], w[1])));
}

export function display(columns) {
  return columns.map(column => '[' + column.map(([p, word]) =>
    p + ':(' + word.join(',') + ')').join(';') + ']').join('') || '0';
}
