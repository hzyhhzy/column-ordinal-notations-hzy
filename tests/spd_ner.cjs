'use strict';
const fs=require('node:fs'),vm=require('node:vm'),assert=require('node:assert/strict');
const path=require('node:path');
const source=fs.readFileSync(path.join(__dirname,'../notations/SPD/SPD.ne-rewritten.js'),'utf8');
const started=Date.now();
const ctx=vm.createContext({queueMicrotask});
ctx.register_notation=x=>{assert(!ctx.ne);ctx.ne=x;};
vm.runInContext(source,ctx,{timeout:1500});
const native=x=>JSON.parse(JSON.stringify(x));
let calls=0;
async function call(code,args) {
    assert(Date.now()-started<45000,'45-second SPD test deadline');
    await Promise.resolve();ctx.args=args;calls++;
    return vm.runInContext(code,ctx,{timeout:1600});
}
async function main() {
    assert.equal(ctx.ne.name,'SPD');
    assert.equal(ctx.ne.display.name,'列表');
    assert.deepEqual(native(Object.keys(ctx.ne.display_equiv)),['计数序列']);
    assert(!ctx.ne.display_equiv['计数序列'].from_display);
    assert.equal(await call('ne.display_equiv["计数序列"].plain(args)','S5'),'1,3,16,45,96,175');
    for(let n=0;n<6;n++) {
        assert.equal(await call('ne.FS("TOP",args)',n),await call('ne.display.plain(args)','S'+n));
        if(n)assert.equal(await call('ne.FS(args,0)','S'+n),await call('ne.display.plain(args)','S'+(n-1)));
    }
    const queue=['S0','S1','S2','S3'],seen=new Set();
    let expansions=0,counts=0;
    while(queue.length&&seen.size<65) {
        const text=await call('ne.display.plain(args)',queue.shift());
        if(seen.has(text))continue;
        seen.add(text);
        const old=native(await call('ne.debug.columns(args)',text));
        let previous=[];
        for(let n=0;n<4;n++) {
            const out=await call('ne.FS(args.s,args.n)',{s:text,n});
            const columns=native(await call('ne.debug.columns(args)',out));
            assert.deepEqual(columns.slice(0,previous.length),previous);
            assert.deepEqual(columns.slice(0,Math.max(0,old.length-1)),old.slice(0,-1));
            if(old.length)assert.equal(await call('ne.compare(args.a,args.b)',{a:out,b:text}),-1);
            assert.equal(await call('ne.FS_alter(args.s,args.n)',{s:text,n}),out);
            assert.equal(await call('ne.FS_short(args.s,args.n)',{s:text,n}),out);
            if(n&&old.at(-1)?.length) {
                const before=native(await call('ne.debug.counts(args).map(String)',text));
                const after=native(await call('ne.debug.counts(args).map(String)',out));
                assert.deepEqual(after.slice(0,old.length-1),before.slice(0,-1));
                assert.equal(BigInt(after[old.length-1]),BigInt(before.at(-1))-1n);counts++;
            }
            if(columns.length<=12&&columns.reduce((n,c)=>n+c.length,0)<1200)queue.push(out);
            previous=columns;expansions++;
        }
    }
    for(const text of ['S-1','[0,0,0,*]','[][0,0,0,9]','[][0,0,0,^]','C(1,4)','[][1,0,0,*]']) {
        await assert.rejects(call('ne.display.from_display(args)',text),/SPD/);
    }
    for(const n of [-1,1.2,true,Number.MAX_SAFE_INTEGER+1])await assert.rejects(call('ne.FS("S1",args)',n),/SPD/);
    assert.equal(await call('ne.FS("[]",10n**100n)'), '0');
    await assert.rejects(call('ne.FS("S1",10n**100n)'),/预算/);
    assert.match(await call('ne.display.html(args)','S2'),/font-family:inherit/);
    assert.equal(await call('ne.display.plain(args)',' [] [0,0,0,+] '),'[][0,0,0,+]');
    assert.equal(await call('ne.display.plain(args)','C()'),'0');
    assert.equal(await call('ne.display.plain(args)','1,3,16'),await call('ne.display.plain(args)','S2'));
    assert.equal(await call('ne.display.plain(args)','C(1,1,1)'),'[][][]');
    assert.equal(await call('ne.display.plain(args)','C(1,3)[1]'),await call('ne.FS("S1",1)'));
    const medium=await call('ne.display.plain(args)','S3[4]');
    const mediumCounts=await call('ne.debug.counts(args).map(String).join(",")',medium);
    assert.equal(await call('ne.display.plain(args)','C('+mediumCounts+')'),medium);
    let parity=null;
    if(process.argv.includes('--vectors')) {
        const payload=fs.readFileSync(0,'utf8');
        assert(payload.length<=16*1024*1024,'16-MiB vector payload bound');
        const vectors=JSON.parse(payload.trim().replace(/^\uFEFF/,''));
        assert(vectors.cases.length<=100&&vectors.comparisons.length<=1000);
        const keys=[];let comparisons=0,outputs=0;
        for(const r of vectors.cases) {
            const key=await call('ne.debug.from_columns(args)',r.graph);keys.push(key);
            assert.deepEqual(native(await call('ne.debug.columns(args)',key)),r.normalized);
            assert.deepEqual(native(await call('ne.debug.counts(args).map(String)',key)),r.counts.map(String));
            for(let n=0;n<r.outputs.length;n++) {
                const out=await call('ne.FS(args.s,args.n)',{s:key,n});
                assert.deepEqual(native(await call('ne.debug.columns(args)',out)),r.outputs[n]);outputs++;
            }
        }
        for(const {left:i,right:j,expected:r} of vectors.comparisons) {
            assert.equal(await call('ne.compare(args.a,args.b)',{a:keys[i],b:keys[j]}),r);comparisons++;
        }
        parity={records:keys.length,outputs,comparisons};
    }
    console.log(JSON.stringify({ok:true,scope:'portable NER registration stub, not live browser',
        states:seen.size,expansions,countDecrements:counts,parity,calls,
        memoryMB:Math.round(process.memoryUsage().rss/1048576)}));
}
main().catch(error=>{console.error(error);process.exitCode=1;});
