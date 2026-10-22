'use strict';

// Mechanical collection of the pre-existing paper manuscripts.
// Usage: node tools/collect.cjs <AutoGuogao workspace>
// The workspace sources are not required to read or validate this package.
const fs = require('node:fs');
const path = require('node:path');
const crypto = require('node:crypto');
const cp = require('node:child_process');
const assert = require('node:assert/strict');

const workspace = path.resolve(process.argv[2] || (() => { throw Error('workspace required'); })());
const dest = path.resolve(__dirname, '..');
const comparison = 'output/bt3ss-bms-comparison-20261019';
const finite = 'output/btnss-wellorder-20261013';
const mappings = [
  [comparison + '/BTnSS极限的固定行数BMS上界.md', 'upper-bound.zh-CN.md'],
  [comparison + '/省略所属绑定的上下文编码.md', 'lemmas/context-encoder.zh-CN.md'],
  [comparison + '/最高键条件的跨叶延拓.md', 'lemmas/cross-leaf.zh-CN.md'],
  [comparison + '/任意维最高两行的块运输.md', 'lemmas/top-row-transport.zh-CN.md'],
  [comparison + '/任意维部分变基的键比较.md', 'lemmas/partial-key-comparison.zh-CN.md'],
  [comparison + '/任意维森林入口键下降.md', 'lemmas/owner-entry.zh-CN.md'],
  [comparison + '/任意行数的首对角引理.md', 'lemmas/first-diagonal.zh-CN.md'],
  [finite + '/MAIN-PROOF.zh-CN.md', 'source-finite/definitions-and-invariants.zh-CN.md'],
];
const finiteNames = [
  'TRANSPORT', 'NUMERIC-CHAINS', 'NUMERIC-COPY-TRANSPORT', 'NUMERIC-EXPANSION',
  'BLOCK-TRANSPORT', 'PARTIAL-TRANSPORT', 'PARTIAL-REBASE', 'KEY-COVARIANCE',
  'VIRTUAL-OWNER-KEYS', 'ROOT-BLOCK-PREFIX', 'BN-HW-CLOSURE', 'SB-CLOSURE',
  'G-CLOSURE', 'PHASE-PARTITION', 'DELAY-AUDIT', 'LOW-COVERAGE',
  'LAST-HOLE', 'LAST-HOLE-AUDIT',
];
for (const name of finiteNames) {
  mappings.push([finite + '/' + name + '.zh-CN.md', 'source-finite/' + name + '.zh-CN.md']);
}
const slash = s => s.replaceAll('\\', '/');
const absoluteMap = new Map(mappings.map(([src, dst]) => [path.resolve(workspace, src), dst]));
const packagedNames = new Set(mappings.map(([, dst]) => dst).concat(['upper-bound.md', 'README.md', 'README.zh-CN.md']));
const hash = bytes => crypto.createHash('sha256').update(bytes).digest('hex');
const records = [];

function write(relative, text) {
  const target = path.join(dest, relative);
  assert(target.startsWith(dest + path.sep));
  fs.mkdirSync(path.dirname(target), { recursive: true });
  fs.writeFileSync(target, text);
}

for (const [src, dst] of mappings) {
  const inputPath = path.resolve(workspace, src);
  const bytes = fs.readFileSync(inputPath);
  const original = bytes.toString('utf8').replaceAll('\r\n', '\n');
  let text = original;
  const changes = ['Normalize CRLF to LF', 'Use GitHub display-math delimiters', 'Relocate included manuscript links'];
  let sourceLineRange = null;
  if (src.endsWith('/MAIN-PROOF.zh-CN.md')) {
    const begin = original.indexOf('## 1. 有限语法与比较');
    const end = original.indexOf('## 4. 有限解释与模型工具');
    assert(begin >= 0 && end > begin);
    sourceLineRange = [original.slice(0, begin).split('\n').length, original.slice(0, end).split('\n').length - 1];
    text = '# BTnSS 的定义与标准域有限不变量\n\n' +
      '本篇摘录旧统一良序稿的第1至3节，供[固定行数 BMS 上界](../upper-bound.zh-CN.md)引用。只保留有限语法、冻结规则、标准域不变量及覆盖论证；原稿第4至7节的模型解释、反射、大基数初始化和良序反证没有收入，也不是本次比较的前提。来源段落及哈希见[收录清单](../MANIFEST.json)。\n\n' +
      text.slice(begin, end).trimEnd() + '\n\n## 有限组合引理索引\n\n' +
      finiteNames.map(name => '- [' + name + '](' + name + '.zh-CN.md)').join('\n') + '\n';
    changes.push('Extract original sections 1–3 only; append finite-dependency index');
  } else if (dst === 'upper-bound.zh-CN.md') {
    text = text.replace('\n\n', '\n\n[English](upper-bound.md) · [收录范围与证据状态](README.zh-CN.md)\n\n');
    text = text.replace('既有[BTnSS 主证明第三节]', '既有[BTnSS 定义与有限不变量第3节]');
    text += '\n\n收录说明：文中实验脚本名指原研究中的审计程序，本次没有打包为可运行测试套件。有限核对记录见[历史检验收据](verification.json)；源规则版本、收录范围及标准／非标准的区别见[总览](README.zh-CN.md)。\n';
    changes.push('Add bilingual navigation, accurate excerpt label and historical-test scope');
  } else {
    text = text.replace('\n\n', '\n\n> 收录说明：本篇为配套局部引理，不单独承担整个比较定理。总体状态以[主证明](' +
      slash(path.relative(path.dirname(path.join(dest, dst)), path.join(dest, 'upper-bound.zh-CN.md'))) +
      ')为准。实验脚本与旧研究日志的文件名是历史来源记录，未作为可运行附件收录。\n\n');
    changes.push('Add local-lemma and historical-test scope banner');
  }
  if (dst === 'lemmas/partial-key-comparison.zh-CN.md') {
    const old = '它不单独证明候选 BMS 编码的全部块条件，因此任意维上界目标仍未完成。';
    assert(text.includes(old));
    text = text.replace(old, '它不单独证明 BMS 编码的全部块条件；这些条件在所链接的总证明中另行接合。');
    changes.push('Replace superseded whole-project pending sentence; local lemma scope unchanged');
  }
  if (dst === 'source-finite/TRANSPORT.zh-CN.md') {
    text = text.replace('## 对完整良序证明还缺什么', '## 本局部引理的范围').replace('尚未证明：每类基本列', '本篇未证明：每类基本列');
    changes.push('Clarify that the final pending paragraph describes this local lemma, not the collected theorem');
  }
  if (dst === 'lemmas/context-encoder.zh-CN.md') {
    const missingClose = '\\tag{2}\n\n右边只取新输出的部分';
    assert(text.includes(missingClose));
    text = text.replace(missingClose, '\\tag{2}\n\\]\n\n右边只取新输出的部分');
    changes.push('Restore the missing display-math closing delimiter after equation (2); formula unchanged');
  }
  text = text.replace(/\]\(([^)]+\.md)(#[^)]*)?\)/g, (whole, target, anchor = '') => {
    if (/^[a-z]+:/i.test(target)) return whole;
    const mapped = absoluteMap.get(path.resolve(path.dirname(inputPath), target));
    if (!mapped) {
      const packaged = slash(path.relative(dest, path.resolve(dest, path.dirname(dst), target)));
      if (packagedNames.has(packaged)) return whole;
      throw Error('Uncollected Markdown dependency: ' + src + ' -> ' + target);
    }
    const relative = slash(path.relative(path.dirname(path.join(dest, dst)), path.join(dest, mapped)));
    return '](' + relative + anchor + ')';
  });
  // Original manuscript links are relocated; generated navigation is already
  // relative to the destination and is checked against packagedNames above.
  text = text.replace(/^\\\[$/gm, '$$$$').replace(/^\\\]$/gm, '$$$$');
  text = text.replace(/\x60([^\x60\r\n]+\.zh-CN\.md)\x60/g, (whole, target) => {
    const relativeName = slash(path.relative(dest, path.resolve(dest, path.dirname(dst), target)));
    return packagedNames.has(relativeName) ? '[' + target + '](' + target + ')' : whole;
  });
  changes.push('Make included inline manuscript filenames into local hyperlinks');
  text = text.trimEnd() + '\n';
  changes.push('Normalize the final newline');
  write(dst, text);
  records.push({ source: src, file: dst, source_sha256: hash(bytes), collected_sha256: hash(Buffer.from(text)), source_line_range: sourceLineRange, changes });
}

const receiptPath = comparison + '/BTNSS-UPPER-BOUND-VERIFICATION.json';
const receiptOriginal = fs.readFileSync(path.join(workspace, receiptPath));
const receipt = Buffer.from(receiptOriginal.toString('utf8').replaceAll('\r\n', '\n'));
write('verification.json', receipt);
records.push({ source: receiptPath, file: 'verification.json', source_sha256: hash(receiptOriginal), collected_sha256: hash(receipt), changes: ['Historical record unchanged except CRLF-to-LF normalization; not a new package-validation result'] });

const mirror = path.join(workspace, '.research-ne-rewritten');
const upstreamRevision = cp.execFileSync('git', ['-C', mirror, 'rev-parse', 'HEAD'], { encoding: 'utf8' }).trim();
const rulePaths = [
  'src/notations/BM-like/Minus1_Y_nSS-series/BT_star_Minus1_Y_nSS-v2.ts',
  'src/notations/BM-like/BM.ts',
];
const rules = rulePaths.map(file => {
  const working = fs.readFileSync(path.join(mirror, file));
  const committed = cp.execFileSync('git', ['-C', mirror, 'show', upstreamRevision + ':' + file]);
  return { file, sha256: hash(working), matches_recorded_commit_ignoring_crlf: working.toString().replaceAll('\r\n', '\n') === committed.toString().replaceAll('\r\n', '\n'), url: 'https://github.com/SmileLee-lyx/ne-rewritten/blob/' + upstreamRevision + '/' + file };
});
assert(rules.every(r => r.matches_recorded_commit_ignoring_crlf), 'Frozen rule file differs from recorded upstream revision');
write('MANIFEST.json', JSON.stringify({
  collected: '2026-10-22',
  scope: 'Paper comparison and finite combinatorial dependencies; no Lean theorem, no private PDF, no external source code or historical audit scripts redistributed.',
  upstream_repository: 'https://github.com/SmileLee-lyx/ne-rewritten',
  upstream_revision: upstreamRevision,
  frozen_rules: rules,
  manuscripts: records,
}, null, 2) + '\n');
console.log(JSON.stringify({ manuscripts: records.length, rules, output: slash(dest) }, null, 2));
