'use strict';

// Pure finite-graph Y expansion on canonical Y root diagrams Q(s).
// This is NOT RPD.fs: only genuine mountain-row templates may form seams.
// Arbitrary valid RPD graphs need not be realizable Y mountain diagrams.
// fs / normalize / realEdges never load or evaluate numerical Y values.
const R = require('./rpd-engine.cjs');

function compareAtoms(a, b) {
  for (let i = 0; i < 4; i++) if (a[i] !== b[i]) return a[i] - b[i];
  return 0;
}

// Input here is already root-closed. Dynamic programming along increasing
// child indices computes maximum-parent-chain endpoints without long walks.
function genuineFromClosed(graph, budget) {
  const groups = new Map();
  for (const [k, q, p, j] of graph.atoms) {
    budget.tick();
    const key = `${k},${q}`;
    let group = groups.get(key);
    if (!group) { group = {k, q, parents: new Map()}; groups.set(key, group); }
    group.parents.set(j, Math.max(p, group.parents.get(j) ?? -1));
  }
  const atoms = [];
  for (const {k, q, parents} of groups.values()) {
    const endpoints = new Map();
    const ordered = [...parents.entries()].sort((a, b) => a[0] - b[0]);
    for (const [j, p] of ordered) {
      budget.tick();
      // p < j, so an earlier defined maximum-parent endpoint is available.
      const root = endpoints.get(p) ?? p;
      endpoints.set(j, root);
      if (root === q) atoms.push([k, q, p, j]);
    }
  }
  atoms.sort(compareAtoms);
  return atoms;
}

function realEdgesWithBudget(graph, budget) {
  return genuineFromClosed(R.normalize(graph, budget), budget);
}

function normalizeWithBudget(graph, budget) {
  const closed = R.normalize(graph, budget);
  return R.normalize({size: closed.size, atoms: genuineFromClosed(closed, budget)}, budget);
}

function chooseControl(genuine, size) {
  let chosen = null;
  for (const atom of genuine) {
    if (atom[3] === size - 1 && (chosen === null || compareAtoms(atom, chosen) > 0)) chosen = atom;
  }
  return chosen;
}

function stepWithBudget(graph, n, budget) {
  if (!Number.isSafeInteger(n) || n < 0) throw new TypeError('Y mountain FS index must be a nonnegative safe integer');
  const closed = R.normalize(graph, budget);
  if (!closed.size) return closed;
  const x = closed.size - 1;
  if (n === 0) return R.drop(closed);
  const genuine = genuineFromClosed(closed, budget);
  const controller = chooseControl(genuine, closed.size);
  if (controller === null) return R.drop(closed);
  const [K, root, cut] = controller, length = x - cut;
  const exactSize = BigInt(x) + BigInt(n) * BigInt(length);
  if (exactSize > BigInt(budget.maxWidth) || exactSize > BigInt(Number.MAX_SAFE_INTEGER)) {
    throw new R.BudgetError('Y mountain expanded width limit; no truncated graph returned');
  }

  const result = new Map();
  function add(k, q, p, j) {
    for (let u = 0; u <= q; u++) {
      budget.tick();
      const atom = [k, u, p, j];
      result.set(atom.join(','), atom);
      if (result.size > budget.maxAtoms) throw new R.BudgetError('Y mountain temporary atom limit');
    }
  }
  const inside = genuine.filter(atom => atom[3] < x);
  // The guard is on ORIGINAL GENUINE roots, before root weakening/movement.
  const seams = genuine.filter(([k, q, , j]) => j === x && (k < K || k === K && q < root));
  for (let b = 0; b <= n; b++) {
    budget.tick();
    const move = i => i < cut ? i : i + b * length;
    for (const [k, q, p, j] of inside) {
      budget.tick(); add(k, move(q), move(p), move(j));
    }
    if (b < n) {
      for (const [k, q, p] of seams) {
        budget.tick(); add(k, move(q), move(p), x + b * length);
      }
    }
  }
  // F may have ancestral shortcut edges. Norm = downward closure of Gen
  // removes these and recovers the next canonical Y root diagram exactly.
  return normalizeWithBudget({size: Number(exactSize), atoms: [...result.values()]}, budget);
}

function createYMountainEngine(options = {}) {
  let numericalEngine;
  const newBudget = () => new R.Budget(options);
  return {
    encode(sequence) {
      // Only the input adapter needs values. Subsequent graph steps do not.
      if (!numericalEngine) {
        const {createYEngine} = require('./y-engine.cjs');
        numericalEngine = createYEngine({
          maxWidth: options.maxWidth ?? 64,
          maxLayers: options.maxLayers ?? ((options.maxLayer ?? 31) + 1),
          maxDigits: options.maxDigits ?? 2000,
          timeoutMs: options.timeoutMs ?? 150,
          maxAtoms: options.maxAtoms ?? 40000,
          ...(options.sourcePath === undefined ? {} : {sourcePath: options.sourcePath}),
        });
      }
      // A graph-domain certificate is supplied by this canonical constructor.
      if (!Array.isArray(sequence) || (sequence.length && sequence[0] !== 1n)) {
        throw new TypeError('Legal Y is empty or starts with BigInt 1');
      }
      return numericalEngine.diagram(sequence);
    },
    fs(graph, n, budget = newBudget()) { return stepWithBudget(graph, n, budget); },
    normalize(graph, budget = newBudget()) { return normalizeWithBudget(graph, budget); },
    realEdges(graph, budget = newBudget()) { return realEdgesWithBudget(graph, budget); },
    control(graph, budget = newBudget()) {
      const closed = R.normalize(graph, budget);
      return chooseControl(genuineFromClosed(closed, budget), closed.size);
    },
  };
}

const defaultEngine = createYMountainEngine();
module.exports = {...defaultEngine, createYMountainEngine};
