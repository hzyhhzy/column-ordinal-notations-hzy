import {createKernel} from './core.mjs';
import {escape, mountain, unavailable, withCounts, svg} from './views.mjs';
import {countSequence} from './counts.mjs';

const NAME = 'Ω-CWY', TOP = 'Limit', cache = new Map(); let cacheSize = 0;
let lastCount = null;
function operation(fn) { const K = createKernel(); const result = fn(K); K.tick(true); return result; }
function parse(raw, K) {
  const text = String(raw); if (text.length > K.limits.text) throw Error('输入过长');
  const found = cache.get(text); if (found) return found;
  const g = K.read(text);
  const cost = text.length + (g === TOP ? 0 : g.size * 8);
  if (cost < 100000) {
    while (cache.size && (cache.size >= 32 || cacheSize + cost > 1000000)) {
      const oldest = cache.keys().next().value, previous = cache.get(oldest);
      cacheSize -= oldest.length + (previous === TOP ? 0 : previous.size * 8); cache.delete(oldest);
    }
    cache.set(text, g); cacheSize += cost;
  }
  return g;
}
const canonical = raw => operation(K => { const g = parse(raw, K); return g === TOP ? TOP : K.write(g); });
const plain = raw => operation(K => { const g = parse(raw, K); return g === TOP ? 'Limit of ' + NAME : K.write(g); });
const latex = raw => {
  const value = plain(raw);
  return value.startsWith('Limit') ? '\\mathrm{Limit\\ of\\ }\\Omega\\mathrm{-CWY}' :
    '\\mathtt{' + value.replace(/[{}]/g, c => '\\' + c) + '}';
};
function draw(raw, settings = {}) {
  try {
    const diagram = operation(K => mountain(parse(raw, K), K, settings));
    return diagram._omegaCWY2.complete ? withCounts(diagram, counts(raw)) : diagram;
  }
  catch (error) { return unavailable(error instanceof Error ? error.message : String(error)); }
}
function counts(raw) {
  // A trailing operation() time check would discard a correctly preserved
  // partial prefix after the nested kernel reported its time budget.
  try {
    const key = String(raw); if (lastCount?.key === key) return lastCount.result;
    const K = createKernel(), result = countSequence(parse(raw, K), K);
    if (key.length + result.text.length < 100000) lastCount = {key, result};
    return result;
  }
  catch (error) { return {text: '?', complete: false, values: null,
    reason: error instanceof Error ? error.message : String(error)}; }
}
register_notation({
  id: 'omega-cwy2-self-v1', name: NAME, simple_name: NAME,
  description: [
    'Ω-CWY：列标使用同类有限表达式的自索引轮廓候选。良序性、共尾性及与 wY 的强度比较尚未证明。',
    '列的位置地址仍为自然数；序数列标是有限、无环的严格子表达式，有自己的局部列编号。',
    'T0=1，T(n+1)=S(Tn)，Top[n]=Tn；S(D) 是以 D 为唯一变点列标的固定两列种子。因此 Tn 恰有 n 层标签嵌套。',
    '默认列表：[父:(普通有限词)]，或 [父:(根|{列标表达式}:地址,…)]; 多条父关系用分号隔开。有限列标可写自然数。',
    '有限词中的重复地址全部逐项列出，不使用重复幂、乘数或省略号。复杂列标以花括号包含完整表达式。',
    '展开的第 b 个块（b 从 0 起），对后继列标删末列、对极限列标取 D[b+1]；自然数地址搬运不进入嵌套列标内部。',
    '所有非零有限式的第零项删末列，后续项满足逐列前缀关系。外顶端按嵌套深度展开，不要求顶端项相互为前缀。',
    '输入 T0、T1、T2、T2[4]、Top[3]、自然数或完整列表。Wk 是规范 ω 的 k 次幂片段的输入别名，W=W1；WW 是其 ω^ω 界。',
    '三个视图为“原式”“计数序列”“山脉图”。计数使用 BigInt，计算每列作为末列反复降低再删除的步数；计数不是唯一编码或比较键。',
    '山脉图也可打开“显示图表”并悬停查看；有限层标不受 ω^ω 限制，统一按记号自身的比较规则排序。',
    '精确识别为 ε0 以下康托正规式的层标用 ω 幂、系数与和表示；其余层标写完整原式，长层标换行但不省略。',
    '这是完整的轮廓分层图，不是已证明的 wY 几何重建。红色底点为列地址，斜线给出父列，黑点数为轮廓地址；变点间恒定。',
    '山脉图最底部另列完整计数序列，未知项为 ?；红色底点仍为父列寻址用的自然数，不是计数。',
    '不合适或超限时整图提示原因，不截取部分列/层。超过绘图范围仍可在列表中展开。',
    '单次接口约 700ms 预算；有列数、嵌套、文本与缓存上限。超限不是数学上的终止或非终止。',
    '计数遇到预算时保留已算出的前缀，当前及后续每列用 ? 占位；未知计数不参与比较或展开。',
    '手写式只检查结构，不等于标准域成员。文件使用独立 ID，不修改旧 CWY2 或 ω+1 版。',
  ],
  display: {name: '原式', plain, html: raw => '<span style="font-family:inherit;white-space:nowrap">' + escape(plain(raw)) + '</span>', from_display: canonical, latex},
  display_equiv: {
    '计数序列': {plain: raw => counts(raw).text,
      html: raw => { const c = counts(raw); return '<span style="font-family:inherit;white-space:nowrap"' +
        (c.reason ? ' title="' + escape(c.reason) + '"' : '') + '>' + escape(c.text) + '</span>'; },
      latex: raw => { const c = counts(raw); return c.complete && c.values === null ? latex('Top') : c.text; }},
    '山脉图': {plain, html: raw => svg(draw(raw)), from_display: canonical, latex}},
  FS: (raw, n) => operation(K => { const g = parse(raw, K); K.natural(n); return K.write(g === TOP ? K.tower(Number(n)) : K.fs(g, n)); }),
  compare: (a, b) => operation(K => { const x = parse(a, K), y = parse(b, K); return x === TOP ? y === TOP ? 0 : 1 : y === TOP ? -1 : K.compare(x, y); }),
  is_limit: raw => operation(K => { const g = parse(raw, K); return g === TOP || K.isLimit(g); }),
  init: () => [TOP, '[]', '0'],
  draw_diagram: {default_data: {invert_vertical: false, column_width: 42}, draw_diagram: draw,
    settings: [{type: 'number', name: '列间距', min: 34, max: 100, field_name: 'column_width'},
      {type: 'boolean', name: '上下翻转', field_name: 'invert_vertical'}],
    handle_action: (data, action) => action.type === 'scroll' && ['up', 'down'].includes(action.direction)
      ? {...data, invert_vertical: action.direction === 'down'} : null},
  debug: {canonical, diagram: draw, counts, svg: raw => svg(draw(raw), true),
    inspect: raw => operation(K => { const g = parse(raw, K); return g === TOP ? {top: true} :
      {columns: g.columns.length, depth: g.depth, size: g.size, polynomial: K.decodePolynomial(g)}; }),
    clear_cache: () => { cache.clear(); cacheSize = 0; lastCount = null; }, cache_stats: () => ({entries: cache.size, estimatedSize: cacheSize})},
});
