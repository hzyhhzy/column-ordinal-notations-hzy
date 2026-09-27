'use strict';

// A bounded BigInt adapter around the accepted Y rules. The source file is
// read, not modified. This module computes rules; it does not certify that an
// arbitrary input sequence is a standard (seed-reachable) Y expression.
const fs = require('node:fs');
const path = require('node:path');
const vm = require('node:vm');

const DEFAULTS = Object.freeze({
  timeoutMs: 150,
  maxWidth: 64,
  maxLayers: 32,
  maxDigits: 2000,
  maxAtoms: 40000,
});

class BudgetError extends RangeError {
  constructor(message) {
    super(message);
    this.name = 'BudgetError';
    this.code = 'Y_BUDGET';
  }
}

function replaceOnce(source, before, after) {
  const at = source.indexOf(before);
  if (at < 0 || source.indexOf(before, at + before.length) >= 0) {
    throw new Error(`Unexpected Y source: expected one occurrence of ${before}`);
  }
  return source.slice(0, at) + after + source.slice(at + before.length);
}

function bigintRules(source) {
  const start = source.indexOf('var itemSeparatorRegex=');
  const end = source.indexOf("//Naruyoko's code ends here");
  if (start < 0 || end <= start) throw new Error('Cannot locate the Y rule body');
  let core = source.slice(start, end);

  // Mathematical values are BigInts; positions and explicit parent indices
  // deliberately remain Numbers. NaN is retained as the unfilled-cell marker.
  core = replaceOnce(core, 'var numval=Number(s);', 'var numval=BigInt(s);');
  core = replaceOnce(core, 'value:Number(s.substring(0,s.indexOf("v"))),',
    'value:BigInt(s.substring(0,s.indexOf("v"))),');
  core = replaceOnce(core, 'if (!isNaN(result[i][j].value)) continue;',
    'if (typeof result[i][j].value === "bigint") continue;');
  core = replaceOnce(core,
    'result[i][j].value=result[i][result[i][j].parentIndex].value+result[i+1][k].value;',
    'result[i][j].value=result[i][result[i][j].parentIndex].value+result[i+1][k].value; __checkValue(result[i][j].value);');

  // Wrappers also intercept recursive calls, without changing any branch of
  // the underlying mathematical rules.
  for (const name of ['calcMountain', 'getBadRoot', 'expand']) {
    core = replaceOnce(core, `function ${name}(`, `function __original_${name}(`);
  }
  return core;
}

const RUNTIME = `
let __badDepth = 0, __expandDepth = 0;
function __budget(message) {
  const error = new RangeError(message);
  error.name = 'BudgetError'; error.code = 'Y_BUDGET'; throw error;
}
function __checkValue(value) {
  if (typeof value !== 'bigint' || value < 1n) throw new RangeError('Y values must be positive integers');
  if (value.toString().length > __limits.maxDigits) __budget('Y integer digit limit');
}
function __checkMountain(mountain) {
  if (mountain.length > __limits.maxLayers) __budget('Y mountain layer limit');
  for (const row of mountain) {
    if (row.length > __limits.maxWidth) __budget('Y mountain width limit');
    for (const entry of row) __checkValue(entry.value);
  }
  return mountain;
}
function calcMountain(sequence) {
  return __checkMountain(__original_calcMountain(sequence));
}
function getBadRoot(sequence) {
  if (++__badDepth > __limits.maxLayers) { --__badDepth; __budget('Y diagonal recursion layer limit'); }
  try { return __original_getBadRoot(sequence); } finally { --__badDepth; }
}
function expand(sequence, n, stringify) {
  if (++__expandDepth > __limits.maxLayers) { --__expandDepth; __budget('Y expansion recursion layer limit'); }
  try { return __original_expand(sequence, n, stringify); } finally { --__expandDepth; }
}
function __reset() { __badDepth = 0; __expandDepth = 0; }
function __fs() {
  __reset();
  const mountain = calcMountain(__input);
  const x = mountain[0].length - 1;
  if (mountain[0][x].parentIndex >= 0) {
    const cut = getBadRoot(mountain);
    if (!Number.isSafeInteger(cut) || cut < 0 || cut >= x) throw new RangeError('Invalid Y bad root');
    if (BigInt(x) + BigInt(__n) * BigInt(x - cut) > BigInt(__limits.maxWidth)) {
      __budget('Y expanded width limit');
    }
  }
  const result = expand(mountain, __n, false);
  __checkMountain(result);
  return result[0] ? result[0].map(entry => entry.value) : [];
}
function __root(row, index) {
  for (let hops = 0; row[index].parentIndex >= 0; hops++) {
    if (hops >= __limits.maxWidth) __budget('Y ancestor traversal limit');
    const parent = row[index].parentIndex;
    if (!Number.isSafeInteger(parent) || parent < 0 || parent >= index) throw new RangeError('Invalid Y parent');
    index = parent;
  }
  return index;
}
function __diagram(genuineOnly = false) {
  __reset();
  let mountain = calcMountain(__input);
  const size = mountain[0].length, atoms = new Map();
  for (let k = 0; k < __limits.maxLayers; k++) {
    for (let r = 0; r < mountain.length; r++) {
      const row = mountain[r];
      for (const entry of row) {
        if (entry.parentIndex < 0) continue;
        const root = __root(row, entry.parentIndex);
        const qMax = row[root].position + r;
        const parent = row[entry.parentIndex].position + r;
        const child = entry.position + r;
        if (!(0 <= qMax && qMax <= parent && parent < child && child < size)) {
          throw new RangeError('Invalid canonical Y edge');
        }
        for (let q = genuineOnly ? qMax : 0; q <= qMax; q++) {
          const atom = [k, q, parent, child];
          atoms.set(atom.join(','), atom);
          if (atoms.size > __limits.maxAtoms) __budget('Y canonical atom limit');
        }
      }
    }
    mountain = calcMountain(calcDiagonal(mountain));
    if (mountain[0].every(entry => entry.value === 1n)) {
      const ordered = [...atoms.values()].sort((a, b) => {
        for (let i = 0; i < 4; i++) if (a[i] !== b[i]) return a[i] - b[i];
        return 0;
      });
      return {size, atoms: ordered};
    }
  }
  __budget('Y canonical diagonal layer limit');
}
// Direct mountain-row edges before adding weaker root labels. This is an
// observation of the original mountain, not the graph rewrite algorithm.
function __genuine() { return __diagram(true); }
function __control() {
  __reset();
  let mountain = calcMountain(__input);
  const x = mountain[0].length - 1;
  if (mountain[0][x].parentIndex < 0) return null;
  for (let k = 0; k < __limits.maxLayers; k++) {
    const next = calcMountain(calcDiagonal(mountain));
    if (next[0].at(-1).value !== 1n) { mountain = next; continue; }
    let height = mountain.length - 1;
    while (height >= 0 && !mountain[height].some(entry => entry.position + height === x)) height--;
    if (height <= 0) throw new RangeError('Missing Y top edge');
    const r = height - 1, row = mountain[r];
    const entry = row.find(item => item.position + r === x);
    if (!entry || entry.parentIndex < 0) throw new RangeError('Missing Y control parent');
    const parent = entry.parentIndex, root = __root(row, parent);
    return [k, row[root].position + r, row[parent].position + r, x];
  }
  __budget('Y control diagonal layer limit');
}
`;

function createYEngine(options = {}) {
  const limits = {...DEFAULTS};
  for (const key of Object.keys(DEFAULTS)) {
    if (options[key] !== undefined) limits[key] = options[key];
    if (!Number.isSafeInteger(limits[key]) || limits[key] < 1) {
      throw new RangeError(`${key} must be a positive safe integer`);
    }
  }
  const sourcePath = options.sourcePath ?? path.resolve(__dirname,
    '../../vendor/hypcos/1-Y.js');
  const source = bigintRules(fs.readFileSync(sourcePath, 'utf8'));
  const context = vm.createContext({
    __limits: Object.freeze({...limits}),
    console: Object.freeze({log() {}, warn() {}}),
  });
  new vm.Script(source + RUNTIME, {filename: 'bounded-y-rules.vm.js'})
    .runInContext(context, {timeout: limits.timeoutMs});
  const scripts = Object.fromEntries(['fs', 'diagram', 'genuine', 'control'].map(name =>
    [name, new vm.Script(`__${name}()`, {filename: `bounded-y-${name}.vm.js`})]));

  function checkSequence(sequence) {
    if (!Array.isArray(sequence)) throw new TypeError('Y sequence must be a BigInt array');
    if (sequence.length > limits.maxWidth) throw new BudgetError('Y input width limit');
    for (const value of sequence) {
      if (typeof value !== 'bigint' || value < 1n) throw new TypeError('Y values must be positive BigInts');
      if (value.toString().length > limits.maxDigits) throw new BudgetError('Y input integer digit limit');
    }
  }
  function invoke(name, sequence, n = 0) {
    context.__input = sequence.join(',');
    context.__n = n;
    try {
      return scripts[name].runInContext(context, {timeout: limits.timeoutMs});
    } catch (error) {
      if (error.code === 'ERR_SCRIPT_EXECUTION_TIMEOUT' || error.code === 'Y_BUDGET') {
        throw new BudgetError(error.message);
      }
      const converted = new RangeError(error.message);
      converted.cause = error;
      throw converted;
    } finally {
      context.__input = '';
    }
  }
  return {
    fs(sequence, n) {
      checkSequence(sequence);
      if (!Number.isSafeInteger(n) || n < 0) throw new RangeError('Y FS index must be a nonnegative safe integer');
      if (!sequence.length) return [];
      // These identities avoid all unnecessary mountain construction.
      if (n === 0 || sequence.at(-1) === 1n) return sequence.slice(0, -1);
      return Array.from(invoke('fs', sequence, n));
    },
    diagram(sequence) {
      checkSequence(sequence);
      if (!sequence.length) return {size: 0, atoms: []};
      const result = invoke('diagram', sequence);
      return {size: result.size, atoms: Array.from(result.atoms, atom => Array.from(atom))};
    },
    genuine(sequence) {
      checkSequence(sequence);
      if (!sequence.length) return {size: 0, atoms: []};
      const result = invoke('genuine', sequence);
      return {size: result.size, atoms: Array.from(result.atoms, atom => Array.from(atom))};
    },
    control(sequence) {
      checkSequence(sequence);
      if (!sequence.length || sequence.at(-1) === 1n) return null;
      const result = invoke('control', sequence);
      return result === null ? null : Array.from(result);
    },
  };
}

module.exports = {createYEngine, BudgetError};
