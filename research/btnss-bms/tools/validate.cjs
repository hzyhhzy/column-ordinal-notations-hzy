'use strict';

// Finite packaging checks only. This does not verify the mathematics.
const fs = require('node:fs');
const path = require('node:path');
const crypto = require('node:crypto');
const assert = require('node:assert/strict');
const root = path.resolve(__dirname, '..');
const hash = bytes => crypto.createHash('sha256').update(bytes).digest('hex');
const manifest = JSON.parse(fs.readFileSync(path.join(root, 'MANIFEST.json'), 'utf8'));
let hashes = 0, links = 0, markdown = 0;
for (const record of manifest.manuscripts) {
  const file = path.resolve(root, record.file);
  assert(file.startsWith(root + path.sep), 'manifest path escape');
  // Git normalizes collected text to LF, including after a fresh checkout.
  const bytes = fs.readFileSync(file);
  assert.equal(hash(bytes), record.collected_sha256, 'hash: ' + record.file);
  hashes++;
}
function scan(dir) {
  for (const e of fs.readdirSync(dir, { withFileTypes: true })) {
    const file = path.join(dir, e.name);
    if (e.isDirectory()) { scan(file); continue; }
    if (!e.name.endsWith('.md')) continue;
    markdown++;
    const text = fs.readFileSync(file, 'utf8');
    assert(!/[A-Z]:[\\/]Users[\\/]/i.test(text), 'private absolute path: ' + file);
    const mathDelimiters = text.match(/^\$\$$/gm) || [];
    assert.equal(mathDelimiters.length % 2, 0, 'unpaired display math: ' + file);
    const fences = text.match(/^```/gm) || [];
    assert.equal(fences.length % 2, 0, 'unpaired code fence: ' + file);
    // Match actual file links, not a bracketed expression in a displayed formula.
    for (const match of text.matchAll(/\]\(([^)]+\.(?:md|json|cjs))(?:#[^)]*)?\)/g)) {
      const target = match[1];
      if (/^[a-z]+:/i.test(target)) continue;
      assert(fs.existsSync(path.resolve(path.dirname(file), target)), 'broken link: ' + file + ' -> ' + target);
      links++;
    }
  }
}
scan(root);
const repository = path.resolve(root, '../..');
for (const name of ['README.md', 'README.zh-CN.md', 'SOURCES.md', 'SOURCES.zh-CN.md', 'research/README.md']) {
  const file = path.join(repository, name);
  const text = fs.readFileSync(file, 'utf8');
  for (const match of text.matchAll(/\]\(([^)]*btnss-bms[^)]*\.md)\)/g)) {
    assert(fs.existsSync(path.resolve(path.dirname(file), match[1])), 'broken entry link: ' + name);
    links++;
  }
}
const receipt = JSON.parse(fs.readFileSync(path.join(root, 'verification.json'), 'utf8'));
assert.equal(receipt.status, 'paper_proof_completed_not_lean');
assert.equal(receipt.pruned_raw_structure.standardness, 'not assumed');
assert(receipt.definition_heads_mixed.raw_standardness.includes('unverified'));
assert.equal(receipt.full_regression.standard_sources_per_dimension * receipt.full_regression.dimension_order.length, 1560);
assert.equal(receipt.full_regression.lower_transport_pairs.reduce((x, y) => x + y, 0), 3922);
assert(receipt.excluded_run.includes('30 second'));
assert(manifest.frozen_rules.every(r => r.matches_recorded_commit_ignoring_crlf));
assert.equal(manifest.manuscripts.length, 27);
console.log(JSON.stringify({ status: 'passed', checks: 'collection integrity only, not mathematical proof checking', imported_hashes: hashes, markdown_files: markdown, local_links: links, historical_receipt_consistent: true }, null, 2));
