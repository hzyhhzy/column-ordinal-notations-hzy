"use strict";

// Read-only archival QA. This is deliberately not a mathematical proof checker.
const fs = require("node:fs");
const path = require("node:path");
const crypto = require("node:crypto");
const vm = require("node:vm");

const here = __dirname;
const root = path.resolve(here, "../../..");
const manifest = JSON.parse(fs.readFileSync(path.join(here, "manifest.json"), "utf8"));
const slash = s => s.replace(/\\/g, "/");
const normalized = file => fs.readFileSync(file, "utf8").replace(/\r\n/g, "\n");
const digest = text => crypto.createHash("sha256").update(text).digest("hex");
const inside = (file, directory) => file.startsWith(directory + path.sep);

function walk(directory) {
  return fs.readdirSync(directory, {withFileTypes: true}).flatMap(entry => {
    const file = path.join(directory, entry.name);
    return entry.isDirectory() ? walk(file) : [file];
  });
}

if (manifest.schema_version !== 1 || manifest.research_status !== "paused" ||
    manifest.not_a_new_proof_or_lean_certificate !== true) {
  throw new Error("Missing archival scope/status boundary");
}

const listed = new Set();
const kinds = {};
let bytes = 0, syntaxChecks = 0;
for (const item of manifest.files) {
  const file = path.resolve(root, item.file);
  if (!inside(file, here) || listed.has(file)) throw new Error("Escaping or duplicate record: " + item.file);
  listed.add(file);
  const text = normalized(file);
  if (digest(text) !== item.packaged_sha256_lf || Buffer.byteLength(text) !== item.bytes) {
    throw new Error("Hash/length mismatch: " + item.file);
  }
  if (!/^[0-9a-f]{64}$/.test(item.original_sha256)) throw new Error("Missing original hash");
  if (item.kind === "original-language-proof-excerpt" && !text.includes("归档研究稿／Archived research manuscript")) {
    throw new Error("Missing manuscript status banner: " + item.file);
  }
  if (file.endsWith(".json")) JSON.parse(text);
  if (item.kind === "standalone-historical-explorer") {
    new vm.Script(text, {filename: item.file});
    syntaxChecks++;
  }
  kinds[item.kind] = (kinds[item.kind] || 0) + 1;
  bytes += item.bytes;
}

const actual = new Set(["papers", "evidence", "explorers"].flatMap(part => walk(path.join(here, part))));
const mismatch = [...new Set([...actual, ...listed])].filter(file => actual.has(file) !== listed.has(file));
if (mismatch.length) throw new Error("Unlisted/missing imported files: " + mismatch.map(x=>slash(path.relative(root,x))).join(", "));

let markdownFiles = 0, relativeLinks = 0;
const broken = [];
const documents = walk(here).filter(x => x.endsWith(".md"));
if (process.argv.includes("--entry-points")) {
  for (const name of ["README.md", "README.zh-CN.md", "research/README.md",
    "research/order-comparisons/README.md", "research/order-comparisons/README.zh-CN.md",
    "research/srpd-tbms/README.md", "research/srpd-tbms/README.zh-CN.md"]) {
    documents.push(path.join(root,name));
  }
}
for (const file of documents) {
  markdownFiles++;
  // Ignore code examples; check destinations, not GitHub's heading slug rules.
  const text = normalized(file).replace(/```[\s\S]*?```|`[^`\n]*`/g, "");
  for (const match of text.matchAll(/\[[^\]\n]+\]\(([^)\s]+)\)/g)) {
    const href = match[1];
    if (/^(?:https?:|mailto:|#)/.test(href)) continue;
    const target = decodeURIComponent(href.split("#")[0]);
    const resolved = path.resolve(path.dirname(file), target);
    relativeLinks++;
    if (!inside(resolved, root) || !fs.existsSync(resolved)) {
      broken.push({file:slash(path.relative(root,file)),target});
    }
  }
}
if (broken.length) throw new Error("Broken/escaping links: " + JSON.stringify(broken, null, 2));

console.log(JSON.stringify({
  status: "archive identity, inventory, relative file links and viewer syntax verified",
  importedFiles: listed.size, kinds, bytesLF: bytes, markdownFiles, relativeLinks,
  viewerSyntaxChecks: syntaxChecks, researchStatus: "paused", mathematicalProofVerified: false,
}, null, 2));
