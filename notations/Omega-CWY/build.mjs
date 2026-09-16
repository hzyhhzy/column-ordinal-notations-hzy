// Rebuild only this directory's standalone NER artifact; no compatibility copies.
import {readFile, writeFile} from 'node:fs/promises';
import {fileURLToPath} from 'node:url';
import path from 'node:path';

const directory = path.dirname(fileURLToPath(import.meta.url));
async function wrap(file) {
  const source = await readFile(path.join(directory, file), 'utf8');
  const names = [...source.matchAll(/^export (?:function|const) (\w+)/gm)].map(m => m[1]);
  const body = source.replace(/^export /gm, '');
  if (/^import /m.test(body)) throw Error('Unexpected dependency in fixed local module');
  return `(() => {\n${body}\nreturn {${names.join(',')}};\n})()`;
}
const entry = (await readFile(path.join(directory, 'entry.mjs'), 'utf8')).replace(/^import .*;\r?\n/gm, '');
const code = '/* Ω-CWY — self-indexed candidate. No well-ordering theorem claimed.\n' +
  ' * Full finite lists; diagrams are profile layers, not reconstructed wY geometry. */\n"use strict";\n(() => {\n' +
  `const {createKernel} = ${await wrap('core.mjs')};\nconst {escape,mountain,unavailable,withCounts,svg} = ${await wrap('views.mjs')};\nconst {countSequence} = ${await wrap('counts.mjs')};\n` + entry + '\n})();\n';
const definitions = [];
new Function('register_notation', code)(n => definitions.push(n));
if (definitions.length !== 1 || definitions[0].id !== 'omega-cwy2-self-v1') throw Error('Registration failed');
const destination = path.join(directory, 'Omega-CWY.ne-rewritten.js');
await writeFile(destination, code, 'utf8');
console.log('Built ' + path.basename(destination));
