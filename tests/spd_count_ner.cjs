'use strict';
const fs=require('node:fs'),vm=require('node:vm'),assert=require('node:assert/strict');
const path=require('node:path');
const payload=fs.readFileSync(0,'utf8');
assert(payload.length<=16*1024*1024,'16-MiB vector payload bound');
const vectors=JSON.parse(payload.trim().replace(/^\uFEFF/,''));
assert(vectors.cases.length<=200);
const context=vm.createContext({queueMicrotask});
context.register_notation=notation=>{context.ne=notation;};
vm.runInContext(fs.readFileSync(path.join(__dirname,'../notations/SPD/SPD.ne-rewritten.js'),'utf8'),context,{timeout:1500});
const started=Date.now();
async function main() {
    let valid=0,invalid=0;
    for(const record of vectors.cases) {
        if(Date.now()-started>20000)throw new Error('Global 20 second test deadline');
        await Promise.resolve();
        context.input='C('+record.counts.join(',')+')';
        if(record.graph===null) {
            assert.throws(()=>vm.runInContext('ne.debug.columns(input)',context,{timeout:1600}),
                error=>error.name!=='SPDLimit'&&/不是标准 SPD/.test(error.message));
            invalid++;
        } else {
            const result=vm.runInContext('ne.debug.columns(input)',context,{timeout:1600});
            assert.deepEqual(JSON.parse(JSON.stringify(result)),record.graph);
            valid++;
        }
    }
    console.log(JSON.stringify({ok:true,valid,invalid,seconds:(Date.now()-started)/1000,
        memoryMB:Math.round(process.memoryUsage().rss/1048576)}));
}
main().catch(error=>{console.error(error);process.exitCode=1;});
