'use strict';

// Preserve the preceding regression suite, including genuine amplification.
const assert=require('node:assert/strict'),fs=require('node:fs'),path=require('node:path'),Module=require('node:module');
const target=path.join(__dirname,'check-one-port-recursive-case.cjs');
let source=fs.readFileSync(target,'utf8');
function replace(before,after){assert.equal(source.split(before).length-1,1);source=source.replace(before,after);}
replace("require('./one-port-recursive-row-bank.cjs')","require('./weak-archive-row-bank.cjs')");
replace("{name:'four layers nonzero actual refinement',levels:4,c:2,path:[1,0]}",
  "{name:'four layers nonzero actual refinement',levels:4,c:2,path:[1,0]},\n"+
  "  {name:'minimal high reserve actually amplifies',levels:1,c:2,path:[7,0]},\n"+
  "  {name:'larger finite row request amplifies',levels:1,c:2,path:[18,0]}");
replace("'ONE-PORT-WHOLE-TBMS.zh-CN.md'","'WEAK-ARCHIVE-SEED.zh-CN.md'");
const runtime=new Module(target,module);runtime.filename=target;runtime.paths=module.paths;
runtime._compile(source,target);
