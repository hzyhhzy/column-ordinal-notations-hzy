/* CTN — linear limit sequences, rules 2026-09-27; packaged 2026-10-01.
 * Former research name CTN2; the original CTN frontend is retired.
 * Standalone NER custom notation. No imports, network, or decompression.
 * Actual expressions are 1/2 strings; all grouped views are display-only.
 * Globally ill-founded; well-founded initial part omega_1^CK by the paper
 * argument in ../../proofs/paper/ctn-well-founded-part.zh-CN.md, not by these finite algorithms.
 */
(() => {
  'use strict';
  const LIMITS = {columns: 200000, characters: 1000000, milliseconds: 600, work: 3000000};
  const now = () => typeof performance === 'undefined' ? Date.now() : performance.now();
  class ResourceLimit extends Error {
    constructor(message) { super('CTN：' + message); this.name = 'ResourceLimit'; }
  }
  class Budget {
    constructor() { this.deadline = now() + LIMITS.milliseconds; this.work = 0; this.next = 0; }
    tick(amount = 1) {
      this.work += amount;
      if (this.work > LIMITS.work) throw new ResourceLimit('超过网页运算量预算；没有改写或截断结果。');
      if (this.work >= this.next) {
        this.next = this.work + 128;
        if (now() > this.deadline) throw new ResourceLimit('超过单次网页时间预算；数学规则未改变。');
      }
    }
    size(length) {
      this.tick();
      if (length > LIMITS.columns) throw new ResourceLimit('完整表达式超过实际列数预算。');
    }
  }
  const pending = Symbol('table entry not supplied');
  const pair = (a, b) => (a + b) * (a + b + 1n) / 2n + b;
  const cons = (head, tail) => 1n + pair(head, tail);
  function isqrt(n) {
    if (n < 2n) return n;
    let x = 1n << BigInt(Math.ceil(n.toString(2).length / 2));
    for (;;) {
      const y = (x + n / x) / 2n;
      if (y >= x) return x;
      x = y;
    }
  }
  function unpair(code) {
    const diagonal = (isqrt(8n * code + 1n) - 1n) / 2n;
    const b = code - diagonal * (diagonal + 1n) / 2n;
    return [diagonal - b, b];
  }
  function decodeList(code, budget) {
    const out = [];
    while (code) {
      budget.tick();
      const [head, tail] = unpair(code - 1n);
      out.push(head); code = tail;
    }
    return out;
  }
  function encodeList(values) {
    let code = 0n;
    for (let i = values.length - 1; i >= 0; i--) code = cons(values[i], code);
    return code;
  }
  // Formula operations: zero, equality, successor, addition, multiplication,
  // membership, negation, conjunction, existential number, existential set.
  function scoped(code, nc, sc, budget) {
    budget.tick();
    const [op, data] = unpair(code);
    if (op === 0n) return data < BigInt(nc);
    if (op === 1n || op === 2n || op === 5n) {
      const [i, j] = unpair(data);
      return i < BigInt(nc) && j < BigInt(op === 5n ? sc : nc);
    }
    if (op === 3n || op === 4n) {
      const [i, rest] = unpair(data), [j, k] = unpair(rest);
      return i < BigInt(nc) && j < BigInt(nc) && k < BigInt(nc);
    }
    if (op === 6n) return scoped(data, nc, sc, budget);
    if (op === 7n) {
      const [a, b] = unpair(data);
      return scoped(a, nc, sc, budget) && scoped(b, nc, sc, budget);
    }
    if (op === 8n) return scoped(data, nc + 1, sc, budget);
    if (op === 9n) return scoped(data, nc, sc + 1, budget);
    return false;
  }
  const context = (code, ns, ss) => pair(code, pair(ns, ss));
  const truthAddress = (code, ns, ss) => pair(1n, context(code, ns, ss));
  const membershipAddress = (row, number) => pair(0n, pair(row, number));
  function checkEntry(size, readVisible, index, budget) {
    budget.tick();
    const [kind, data] = unpair(index), value = readVisible(index);
    if (kind === 0n) return value === 0n || value === 1n;
    if (kind > 5n) return value === 0n;
    let payload = data, number = null;
    if (kind === 4n || kind === 5n) {
      if (value !== 0n) return false;
      [payload, number] = unpair(data);
    }
    const [code, environment] = unpair(payload), [ns, ss] = unpair(environment);
    const numbers = decodeList(ns, budget), sets = decodeList(ss, budget);
    const extra = Number(kind === 3n || kind === 4n);
    if (!scoped(code, numbers.length + extra, sets.length, budget)) return value === 0n;
    const [op, body] = unpair(code);
    const truth = (child, n = ns, s = ss) => readVisible(truthAddress(child, n, s));
    function instance(argument) {
      if (argument >= size) throw pending;
      return op === 8n ? truth(body, cons(argument, ns), ss) : truth(body, ns, cons(argument, ss));
    }
    if (kind === 3n) return true;
    if (kind === 2n) return op === 8n || op === 9n || value === 0n;
    if (kind === 4n) {
      const row = readVisible(pair(3n, payload));
      if (row >= size) throw pending;
      return readVisible(membershipAddress(row, number)) === truth(code, cons(number, ns), ss);
    }
    if (kind === 5n) {
      if ((op !== 8n && op !== 9n) || truth(code) === 1n) return true;
      return instance(number) === 0n;
    }
    if (value !== 0n && value !== 1n) return false;
    if (op === 0n) return value === BigInt(numbers[Number(body)] === 0n);
    if (op === 1n || op === 2n || op === 5n) {
      const [i, j] = unpair(body), a = numbers[Number(i)];
      if (op === 5n) return value === readVisible(membershipAddress(sets[Number(j)], a));
      return value === BigInt(a + (op === 2n ? 1n : 0n) === numbers[Number(j)]);
    }
    if (op === 3n || op === 4n) {
      const [i, rest] = unpair(body), [j, k] = unpair(rest);
      const a = numbers[Number(i)], b = numbers[Number(j)];
      return value === BigInt((op === 3n ? a + b : a * b) === numbers[Number(k)]);
    }
    if (op === 6n) return value === 1n - truth(body);
    if (op === 7n) {
      const [a, b] = unpair(body);
      return value === (truth(a) & truth(b));
    }
    return value === 0n || instance(readVisible(pair(2n, payload))) === 1n;
  }
  function tableOK(values, budget = new Budget()) {
    const size = BigInt(values.length);
    const read = address => {
      if (address >= size) throw pending;
      return values[Number(address)];
    };
    for (let i = 0; i < values.length; i++) {
      budget.tick();
      if (typeof values[i] !== 'bigint' || values[i] < 0n) return false;
      try { if (!checkEntry(size, read, BigInt(i), budget)) return false; }
      catch (error) { if (error !== pending) throw error; }
    }
    return true;
  }
  // Every original table value k is uniformly coded by k+1.
  // Encoded value 0 is a terminal branch at every node.
  function tableTree(values, budget = new Budget(), length = values.length) {
    const decoded = [];
    for (let i = 0; i < length; i++) {
      budget.tick();
      if (values[i] <= 0n) return false;
      decoded.push(values[i] - 1n);
    }
    return tableOK(decoded, budget);
  }
  function syntax(word, budget) {
    if (typeof word !== 'string') throw new Error('CTN：内部表达式必须是原始 1/2 串。');
    budget.size(word.length);
    if (!/^[12]*$/.test(word)) throw new Error('CTN：每一列只能是 1 或 2。');
  }
  function inspect(word, budget = new Budget()) {
    syntax(word, budget);
    const values = [], blocks = [];
    let offset = 0, lastPositive = -1, kind = 'entry', opened = 0;
    while (offset < word.length) {
      budget.tick();
      if (word[offset] === '2') {
        const tail = word.slice(offset + 1);
        if (!/^1*$/.test(tail)) throw new Error('CTN：封口后只能接后继列 1。');
        if (!values.length && tail) throw new Error('CTN：全系统顶端 2 后面不能再接列。');
        if (!tableTree(values, budget)) throw new Error('CTN：未通过检查的候选不能接封口。');
        return {values, blocks, kind: tail ? 'tail' : 'cap', opened: 0, tail: tail.length};
      }
      const start = offset++;
      opened = 0;
      while (offset < word.length && word[offset] === '2') { budget.tick(); opened++; offset++; }
      if (offset === word.length) { kind = 'gap'; break; }
      values.push(BigInt(opened));
      if (opened) lastPositive = values.length - 1;
      offset++; blocks.push([start, offset]); kind = 'entry';
    }
    const length = word.endsWith('2') ? values.length : Math.max(0, lastPositive);
    if (!tableTree(values, budget, length))
      throw new Error('CTN：终止分支后不能再出现 2，只能接后继列 1。');
    return {values, blocks, kind, opened, tail: 0};
  }
  function parse(input) {
    const raw = String(input).trim();
    if (raw.length > LIMITS.characters) throw new ResourceLimit('输入文本超过网页预算。');
    if (/^(top|Limit\s+of\s+CTN)$/i.test(raw)) return '2';
    if (!raw || raw === '0' || raw === '∅' || raw === '[]') return '';
    let word;
    if (raw.includes('[')) {
      const compact = raw.replace(/\s+/g, ''), matches = [...compact.matchAll(/\[([12])\]/g)];
      if (matches.map(m => m[0]).join('') !== compact) throw new Error('CTN：列表格式是 [1][2][1]，每对方括号一列。');
      word = matches.map(m => m[1]).join('');
    } else {
      if (!/^[12]+(?:\s*[,，\s]\s*[12]+)*$/.test(raw))
        throw new Error('CTN：请输入原始 1/2 列串，可用逗号或空格分隔。');
      word = raw.replace(/[,，\s]/g, '');
    }
    inspect(word); return word;
  }
  const compare = (a, b) => a === b ? 0 : a < b ? -1 : 1;
  function FS(word, n) {
    if (!Number.isSafeInteger(n) || n < 0) throw new Error('CTN：基本列下标必须是非负安全整数。');
    const budget = new Budget(), info = inspect(word, budget);
    if (!word) return '';
    const prefix = word.slice(0, -1);
    if (n === 0 || word.endsWith('1')) return prefix;
    if (info.kind === 'cap') {
      budget.size(prefix.length + n);
      return prefix + '1' + '2'.repeat(n - 1);
    }
    if (tableTree([...info.values, BigInt(info.opened - 1)], budget)) {
      budget.size(prefix.length + n + 1);
      return prefix + '12' + '1'.repeat(n - 1);
    }
    budget.size(prefix.length + n);
    return prefix + '1'.repeat(n);
  }
  function encodeTable(values, cap = false) {
    const out = [], budget = new Budget();
    let length = Number(cap);
    for (const raw of values) {
      if (typeof raw === 'number' && (!Number.isSafeInteger(raw) || raw < 0))
        throw new Error('CTN：不能舍入表值。');
      const value = BigInt(raw);
      if (value < 0n) throw new Error('CTN：表值必须为自然数。');
      if (value > BigInt(LIMITS.columns - length)) throw new ResourceLimit('实际列数超过网页预算。');
      length += Number(value) + 3; budget.size(length);
      out.push('1' + '2'.repeat(Number(value) + 1) + '1');
    }
    if (cap) out.push('2');
    return out.join('');
  }
  const sequenceText = word => word ? word.split('').join(',') : '0';
  const listText = word => word ? '[' + word.split('').join('][') + ']' : '[]';
  const powersHTML = text => text.replace(/([12])\^(\d+)/g, '$1<sup>$2</sup>');

  // This is a DISPLAY analysis, never part of FS. Find the first failed
  // completed table prefix so that its trailing 1s aren't shown as more data.
  function displayParts(word, budget = new Budget()) {
    const info = inspect(word, budget);
    if (tableTree(info.values, budget)) return {...info, failed: null};
    let low = 1, high = info.values.length;
    while (low < high) {
      const middle = Math.floor((low + high) / 2);
      if (tableTree(info.values, budget, middle)) low = middle + 1;
      else high = middle;
    }
    return {...info, failed: low - 1, tail: word.length - info.blocks[low - 1][1]};
  }
  function groupedText(word) {
    if (!word) return '0';
    const info = displayParts(word);
    const length = info.failed === null ? info.values.length : info.failed + 1;
    const blocks = info.values.slice(0, length).map(k => '⟦' + k + '⟧').join('');
    if (info.failed !== null) return blocks + '!' + (info.tail ? '·1^' + info.tail : '');
    if (info.kind === 'cap' || info.kind === 'tail')
      return blocks + '|2' + (info.tail ? '·1^' + info.tail : '');
    if (info.kind === 'gap') return blocks + '|1' + (info.opened ? '·2^' + info.opened : '');
    return blocks;
  }
  function tableText(word) {
    const info = displayParts(word), validLength = info.failed === null ? info.values.length : info.failed;
    const values = info.values.slice(0, validLength).map(k => String(k - 1n)).join(',');
    if (info.failed !== null) {
      const encoded = info.values[info.failed];
      const reason = encoded === 0n ? '零号终止分支' : '候选 ' + (encoded - 1n) + ' 未通过检查';
      return '⟨' + values + '⟩ | ' + reason + (info.tail ? '；后接 ' + info.tail + ' 个 1' : '');
    }
    const labels = {entry: '入口', cap: '封口', tail: '封口后接 ' + info.tail + ' 个 1',
      gap: '未闭合块 ' + info.opened};
    return '⟨' + values + '⟩ | ' + labels[info.kind];
  }

  // Requested run view: at each actual 1, emit the length of the immediately
  // preceding run of 2s. Keep the unfinished trailing run separately: dropping
  // it would identify 1 and 12, i.e. the natural number 1 and omega.
  function runCounts(word) {
    const budget = new Budget(); syntax(word, budget);
    const counts = [];
    let tail = 0;
    for (const digit of word) {
      budget.tick();
      if (digit === '2') tail++;
      else { counts.push(tail); tail = 0; }
    }
    return {counts, tail};
  }
  function runText(word) {
    const {counts, tail} = runCounts(word);
    return (counts.length ? counts.join(',') : '∅') + (tail ? ' | 2^' + tail : '');
  }
  // A different grouping starts each block AT a 1: 1, followed by k twos.
  // Its local clearance count is k+1. The exceptional top '2' has no such 1.
  // These are block counts, not one count per original column.
  function blockCounts(word) {
    const budget = new Budget(); syntax(word, budget);
    if (word === '2') return null;
    const counts = [];
    for (const digit of word) {
      budget.tick();
      if (digit === '1') counts.push(1);
      else {
        if (!counts.length) throw new Error('CTN：只有顶端 2 可以不以 1 开头。');
        counts[counts.length - 1]++;
      }
    }
    return counts;
  }
  function blockCountText(word) {
    const counts = blockCounts(word);
    return counts === null ? 'Top of CTN' : counts.length ? counts.join(',') : '0';
  }
  // Genuine LOCAL column-clearance counts equal the original digits:
  // P1 -> P in one step; P2 -> P1... -> (truncate appended tail) P1 -> P.
  const columnCounts = word => word.split('').map(Number);
  const notation = {
    id: 'ctn-linear-20261001', name: 'CTN', simple_name: 'CTN',
    description: [
      '线性基本列伪序记号。整体不良序；最大良序初始段恰为 ω₁ᴄᴋ 的纸面论证见配套定义。合法不等于属于良序段。',
      '空串为零，1 是自然数 1，1,2 恰为 ω；单列 2 是整个系统的顶端，不是一个真实序数。',
      '末列 1 当且仅当有直接前驱，所有 [n] 都删末列。末列 2 没有直接前驱，基本列严格递增且前缀相容；第 1 项之后每次增加一列。',
      '原始列直接参与展开，实际列只有 1 和 2。三个基本列选项规则相同，[0] 一律删一列；无解压步骤或旧版的恒定极限保护。',
      '原始列本身就是逐列清空计数：1 一次清空，2 先变成 1 再清空。新视图「1前连续2数」统计另一件事，不是这个计数序列。',
      '「1前连续2数」每遇到一个 1，写出其前面紧邻的连续 2 的个数。末尾未遇到 1 的 2 用 | 2^k 保留，∅ 表示没有已结束的段。',
      '「分块计数（后2数+1）」把每个 1 和它后面的 k 个连续 2 视为一块，显示 k+1；这是按块的清空计数，1221 显示 3,1。单列顶端 2 单独标作 Top of CTN。',
      '分块计数不改变数学列边界：副视图的 [0] 可能只是末数减 1，其基本列的数字个数也可能不增长。完整前缀和线性长度条件仍针对原始列。',
      '分组简写 ⟦k⟧ 表示整个块 1·2^k·1，不是一列；它编码原表值 k−1。! 表示终止分支，后面只能接 1。上标均为重复次数。',
      '只有原始列和列列表支持输入。其他副视图不改变列边界、比较或展开规则；资源超限明确报错，不输出截断结果。'
    ],
    display: {name: '原始列（计数序列）', plain: sequenceText, html: sequenceText, from_display: parse},
    display_equiv: {
      '列列表': {plain: listText, html: listText, from_display: parse},
      '分组简写（非列）': {plain: groupedText, html: word => powersHTML(groupedText(word))},
      '有限表': {plain: tableText, html: tableText},
      '1前连续2数': {plain: runText, html: word => powersHTML(runText(word))},
      '分块计数（后2数+1）': {plain: blockCountText, html: blockCountText}
    },
    init: () => ['2', '12', '1', ''],
    is_limit: word => word.endsWith('2'), compare, FS, FS_alter: FS, FS_short: FS,
    debug: {LIMITS, Budget, ResourceLimit, pending, pair, unpair, cons, encodeList, decodeList,
      scoped, context, truthAddress, membershipAddress, checkEntry, tableOK, tableTree, inspect,
      parse, compare, fundamental: FS, encodeTable, displayParts, sequenceText, listText,
      groupedText, tableText, runCounts, runText, columnCounts, blockCounts, blockCountText}
  };
  if (typeof register_notation === 'function') register_notation(notation);
  if (typeof module !== 'undefined' && module.exports) module.exports = notation;
})();
