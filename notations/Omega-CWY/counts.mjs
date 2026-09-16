/** Exact local column counts; bounded evaluation, never a guessed approximation. */
export function countSequence(g, K, options = {}) {
  if (g === 'Limit') return {text: 'Limit of Ω-CWY', complete: true, values: null};
  if (!g.columns.length) return {text: '0', complete: true, values: []};
  const now = options.now ?? Date.now, started = now();
  const maxSteps = options.steps ?? 30000, milliseconds = options.ms ?? 450;
  let steps = 0; const values = Array(g.columns.length).fill(null);
  const asText = () => values.map(value => value === null ? '?' : String(value)).join(',');
  const checkTime = () => {
    if (now() - started >= milliseconds) throw Error('计数计算达到时间预算，不是整数溢出');
  };
  for (let child = 0; child < g.columns.length; child++) {
    try {
      checkTime(); K.tick(true);
      let current = K.term(g.columns.slice(0, child + 1)), count = 1n;
      while (current.columns.at(-1).length) {
        checkTime();
        if (steps >= maxSteps) throw Error('计数计算达到步数预算，不是整数溢出');
        steps++; K.tick();
        // The first retained replacement is D_0 for every positive FS index.
        const lowered = K.minusColumn(current, 0);
        const next = K.term([...current.columns.slice(0, -1), lowered]);
        if (K.compare(next, current) >= 0) throw Error('计数下降检查失败');
        current = next; count++;
      }
      values[child] = count;
    } catch (error) {
      // Never display the unfinished column's running total as its value.
      // Also preserve the prefix if the nested kernel reaches its own budget.
      return {text: asText(), complete: false, values, steps, completedColumns: child,
        reason: error instanceof Error ? error.message : String(error)};
    }
  }
  return {text: asText(), complete: true, values, steps, completedColumns: values.length};
}
