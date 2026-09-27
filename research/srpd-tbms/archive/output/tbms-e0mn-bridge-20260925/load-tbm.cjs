'use strict';

// Read-only loader of the ordinary TBMS implementation, NOT Bubby3's BTBMS.
// Mathematical rules are not patched. Every external evaluation is bounded.
const fs = require('node:fs');
const path = require('node:path');
const vm = require('node:vm');
const crypto = require('node:crypto');
// TypeScript output is pinned alongside its source; no compiler install is required.

function loadTBM() {
  const root = path.resolve(__dirname, '../../vendor/ne-rewritten');
  const context = vm.createContext({});
  const modules = new Map();
  const hashes = {};
  for (const [name, file] of [
    ['utils', 'src/utils.ts'],
    ['notation_utils', 'src/notations/notation_utils.ts'],
    ['TBM', 'src/notations/BM-like/TBM.ts'],
  ]) {
    const source = fs.readFileSync(path.join(root, file), 'utf8');
    hashes[file] = crypto.createHash('sha256').update(source).digest('hex');
    const code = fs.readFileSync(path.join(root, 'compiled', name + '.cjs'), 'utf8');
    const exports = {};
    context.exports = exports;
    context.require = specifier => {
      if (specifier === '@/utils.ts') return modules.get('utils');
      if (specifier === '@/notations/notation_utils.ts') return modules.get('notation_utils');
      throw Error('Unexpected import: ' + specifier);
    };
    new vm.Script('(function(exports,require){' + code + '\n})(exports,require);')
      .runInContext(context, {timeout: 2000});
    modules.set(name, exports);
  }
  context.B = modules.get('TBM');
  return {
    B: context.B,
    context,
    hashes,
    run(code, timeout = 1000) {
      return new vm.Script(code).runInContext(context, {timeout});
    },
  };
}

module.exports = {loadTBM};
