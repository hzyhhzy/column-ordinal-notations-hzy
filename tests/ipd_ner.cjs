/* NER contract, independent Python parity, exact counts, safety and portable
   registration-stub integration. Run with Python vectors piped to stdin. */
'use strict';
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm');
const assert=require('node:assert/strict');
const source=fs.readFileSync(path.join(__dirname,'../notations/IPD/IPD.ne-rewritten.js'),'utf8');
const started=Date.now();
const stats={graphs:0,standardGraphs:0,expansions:0,prefixes:0,comparisons:0,
    countGraphs:0,countDecrements:0,guards:0,largeCountTerms:0,treeViews:0};
const ctx=vm.createContext({queueMicrotask,source});
ctx.register_notation=definition=>{assert(!ctx.ne);ctx.ne=definition;};
vm.runInContext("new Function('register_notation','register_category',source)(register_notation,()=>{})",ctx,{timeout:1200});
const native=value=>JSON.parse(JSON.stringify(value));
async function call(code,args) {
    await Promise.resolve();
    assert(Date.now()-started<45000,'45-second bounded test deadline');
    ctx.args=args;return vm.runInContext(code,ctx,{timeout:1600});
}
async function rejects(code,args,pattern=/IPD/) {
    await assert.rejects(call(code,args),pattern);stats.guards++;
}

async function main() {
    assert.equal(ctx.ne.id,'ipd-v01');assert.equal(ctx.ne.name,'IPD');
    assert.equal(ctx.ne.display.name,'列表');
    assert.deepEqual(Object.keys(ctx.ne.display_equiv),['计数序列','树形图']);
    assert(!ctx.ne.display_equiv['计数序列'].from_display,'Do not pretend to invert arbitrary counts');
    assert.deepEqual(native(ctx.ne.init()),['Limit of IPD','[]','0']);
    const data=JSON.parse(fs.readFileSync(0,'utf8').trim().replace(/^\uFEFF/,'')),keys=[];
    for(const record of data.records) {
        const key=await call('ne.display.from_display(args)',record.text);keys.push(key);
        assert.deepEqual(native(await call('ne.debug.columns(args)',key)),record.cols);
        assert.equal(await call('ne.display.plain(args)',key),record.text);
        assert(!String(await call('ne.display.plain(args)',key)).includes('~'));
        assert.equal(await call('ne.debug.from_columns(args)',record.cols),key);
        assert.match(await call('ne.display.html(args)',key),/font-family:inherit/);
        assert.equal(await call('ne.is_limit(args)',key),!!record.cols.at(-1)?.length);
        let previous;
        for(let n=0;n<4;n++) {
            const result=await call('ne.FS(args.key,args.n)',{key,n});
            const columns=native(await call('ne.debug.columns(args)',result));
            assert.deepEqual(columns,record.outputs[n],record.text+'['+n+']');
            assert.equal(await call('ne.FS_alter(args.key,args.n)',{key,n}),result);
            assert.equal(await call('ne.FS_short(args.key,args.n)',{key,n}),result);
            if(record.cols.length)assert.equal(await call('ne.compare(args.a,args.b)',{a:result,b:key}),-1);
            assert.deepEqual(columns.slice(0,Math.max(0,record.cols.length-1)),record.cols.slice(0,-1));
            if(previous){assert.deepEqual(columns.slice(0,previous.length),previous);stats.prefixes++;}
            previous=columns;stats.expansions++;
        }
        assert.deepEqual(native(await call('ne.debug.columns(args)',key)),record.cols,'Input is immutable');
        stats.graphs++;if(record.standard)stats.standardGraphs++;
    }
    for(const [a,b,expected] of data.comparisons) {
        assert.equal(await call('ne.compare(args.a,args.b)',{a:keys[a],b:keys[b]}),expected);stats.comparisons++;
    }
    for(const record of data.countRecords) {
        assert.deepEqual(native(await call('ne.debug.counts(args).map(String)',record.text)),record.values,
            'Exact local oracle: '+record.text);
        assert.equal(await call('ne.display_equiv["计数序列"].plain(args)',record.text),record.values.join(',')||'0');
        const columns=native(await call('ne.debug.columns(args)',record.text));
        if(columns.at(-1)?.length)for(let n=1;n<=3;n++) {
            const output=await call('ne.FS(args.text,args.n)',{text:record.text,n});
            const local=await call('ne.debug.from_columns(ne.debug.columns(args.text).slice(0,args.width))',
                {text:output,width:columns.length});
            const expected=record.values.slice();expected[expected.length-1]=String(BigInt(expected.at(-1))-1n);
            assert.deepEqual(native(await call('ne.debug.counts(args).map(String)',local)),expected,
                'Old final count decreases exactly one: '+record.text);
            stats.countDecrements++;
        }
        stats.countGraphs++;
    }
    for(let i=0;i<keys.length;i++) {
        const html=await call('ne.display_equiv["树形图"].html(args)',keys[i]);
        assert(!html.includes('~'),'No visible run-length abbreviation');
        if(data.records[i].cols.length)assert.match(html,/data-ipd-tree-view="complete"/);
        else assert(!html.includes('<svg'));
        assert.equal((html.match(/<svg /g)||[]).length,data.records[i].cols.reduce((n,c)=>n+c.length,0));
        stats.treeViews++;
    }
    for(let n=0;n<80;n++) {
        assert.equal(await call('ne.FS(args,1)','A'+(n+1)),await call('ne.display.plain(args)','A'+n));
        assert.equal(await call('ne.display_equiv["计数序列"].plain(args)','A'+n),'1,'+(n+2));
    }
    for(const n of [12,30,100,500])for(const seed of [0,1]) {
        const values=native(await call('ne.debug.counts(args).map(String)','A'+seed+'['+n+']'));
        const expected=Array.from({length:n+1},(_,j)=>j===0?'1':String(seed===0?1n<<BigInt(j-1):BigInt(j)*(1n<<BigInt(j-1))+1n));
        assert.deepEqual(values,expected);stats.largeCountTerms+=values.length;
    }
    assert.equal(await call('ne.display.plain(args)',' [ ] [0:1/^(. , . , .)] '),'[][0:1/^(.,.,.)]');
    assert.equal(await call('ne.display.plain(args)','[][0:2/{*(.)}(.,.)]'),'[][0:2/{*(.)}(.,.)]');
    assert.equal(await call('ne.display.plain(args)','[][0:0/0;0:0/*]'),'[][0:0/*]');
    assert.equal(await call('ne.display.plain(args)','TOP[2][3]'),await call('ne.display.plain(args)','A2[3]'));
    assert.equal(await call('ne.FS(args,10n**100n)','0'),'0');
    assert.equal(await call('ne.FS(args,10n**100n)','[]'),'0');
    for(const input of ['[0:0/0]','[][][0:0/1]','[][0:1/^(.~0)]','[][0:1/^(.~2),.]',
        '[][0:2/*]','[][0:0/^]','1,4','A0[-1]','A0[1.5]','<script>x</script>','A1junk'])
        await rejects('ne.display.from_display(args)',input);
    for(const n of [-1,1.5,true,Number.MAX_SAFE_INTEGER+1])await rejects('ne.FS("A0",args)',n);
    for(const input of ['A1000001','A'+'9'.repeat(10000),'[][0:1/^(.~8193)]','5000','A0'+'[0]'.repeat(257)])
        await rejects('ne.display.from_display(args)',input,/预算/);
    await rejects('ne.FS("TOP",10n**100n)',null,/预算/);
    await rejects('ne.FS("A0",4096)',null,/预算/);
    assert.equal(await call('ne.FS("A2",1)'), '[][0:1/.]');
    // A complex count may consume its own budget, but structure remains usable
    // in that SAME event. The placeholder never masquerades as a numeric value.
    const warning=native(await call('(()=>{const s=ne.display_equiv["计数序列"].plain("A2[20]");'+
        'return [s,ne.display.plain("A1"),ne.FS("A1",1)];})()'));
    assert.match(warning[0],/预算内未算完/);
    assert.equal(warning[1],'[][0:1/.]');assert.equal(warning[2],'[][0:0/0]');
    assert.equal(await call('ne.display_equiv["计数序列"].plain("A2")'),'1,4');

    // The portable release does not require a private NER source checkout.
    // Browser-engine clicks and KaTeX integration are outside this stub test.
    console.log(JSON.stringify({ok:true,integrationScope:'registration stub, not a live browser',...stats,oracle:data.stats,milliseconds:Date.now()-started,
        memoryMB:Math.round(process.memoryUsage().rss/1048576)}));
}
main().catch(error=>{console.error(error);process.exitCode=1;});
