"use strict";

// Mechanical, dependency-free bundle; --check never writes anything.
const fs=require("node:fs"),path=require("node:path");
const read=name=>fs.readFileSync(path.join(__dirname,name),"utf8").replace(/\r\n/g,"\n");
const output="/* CDMN — Compact Deep Mountain Notation. Well-ordering remains open. */\n"+
  "(() => {\nconst module={exports:{}};\n"+read("cdmn-core.cjs")+"\n"+
  read("cdmn-ner-wrapper.js")+"\n})();\n";
const target=path.join(__dirname,"CDMN.ne-rewritten.js");
if(process.argv.includes("--check")) {
  if(!fs.existsSync(target)||fs.readFileSync(target,"utf8").replace(/\r\n/g,"\n")!==output)
    throw Error("CDMN bundle differs from its local core and adapter");
  console.log("CDMN bundle is current");
} else {
  fs.writeFileSync(target,output);
  console.log("Built CDMN.ne-rewritten.js");
}
