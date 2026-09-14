/* Display-only regression: full lists, complete typed forests, isolated limits. */
'use strict';
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm');
const assert=require('node:assert/strict');
const started=Date.now();
const scope=vm.createContext({queueMicrotask,register_notation:n=>scope.ne=n});
vm.runInContext(fs.readFileSync(path.join(__dirname,'../notations/IPD/IPD.ne-rewritten.js'),'utf8'),scope,{timeout:1200});
async function call(code,args) {
    await Promise.resolve();assert(Date.now()-started<20000,'20-second test limit');
    scope.args=args;return vm.runInContext(code,scope,{timeout:1800});
}
const times=(s,re)=>(s.match(re)||[]).length;
function size(d,t) {
    if(d===0 || t.length===0)return {nodes:1,links:0,heads:0};
    const [h,children]=t;
    const sum={nodes:1,links:children.length,heads:h!==-1 && d>1?1:0};
    const parts=children.map(c=>size(d,c));
    if(h!==-1 && d>1)parts.push(size(d-1,h));
    for(const child of parts)for(const key of ['nodes','links','heads'])sum[key]+=child[key];
    return sum;
}
async function main() {
    const samples=['A0','A1','A2[4]','A8[4]',
        '[][][][2:3/{^}({^}(.));0:3/.]',
        '[][0:3/{{*(.)}(.)}(.,.)]',
        '[][0:3/{^(.,.)}({^}(.),{{*(.,.)}}(.,.))]',
        '[][0:2/{.}]', '[][0:1/^(.~30)]','4','0','TOP'];
    let nodes=0,heads=0,links=0;
    for(const raw of samples) {
        const text=await call('ne.display.plain(args)',raw);
        assert(!text.includes('~'),text);
        assert.equal(await call('ne.compare(args.a,args.b)',{a:raw,b:text}),0);
        assert.equal(await call('ne.display_equiv["树形图"].plain(args)',raw),text);
        const html=await call('ne.display_equiv["树形图"].html(args)',raw);
        assert(!html.includes('~'));assert(!html.includes('NaN'));assert(!html.includes('Infinity'));
        assert(!/<script|on\w+=|https?:\/\/[^w]/i.test(html),'No scripts or external assets');
        const cols=await call('ne.debug.columns(args)',raw);
        if(cols===null || !cols.length){assert(!html.includes('<svg'));continue;}
        assert.match(html,/data-ipd-tree-view="complete"/);
        assert.equal(times(html,/data-column=/g),cols.length);
        assert.equal(times(html,/<svg /g),cols.reduce((n,c)=>n+c.length,0));
        const expected={nodes:0,heads:0,links:0};
        for(const column of cols)for(const [p,[d,t]] of column) {
            const part=size(d,t);for(const key of ['nodes','heads','links'])expected[key]+=part[key];
        }
        assert.equal(times(html,/data-ipd-node=/g),expected.nodes,raw+' all node occurrences');
        assert.equal(times(html,/data-ipd-head=/g),expected.heads,raw+' distinct head relation');
        assert.equal(times(html,/data-ipd-link="child"/g),expected.links,raw+' ordered child links');
        nodes+=expected.nodes;heads+=expected.heads;links+=expected.links;
    }
    assert.equal(await call('ne.display.plain(args)','[][0:1/^(.~3)]'),'[][0:1/^(.,.,.)]');
    assert.equal(await call('ne.display.plain(args)','[][0:2/{^}({^}(.~2)~2)]'),
        '[][0:2/{^}({^}(.,.),{^}(.,.))]');
    assert.equal(await call('ne.FS("A2",1)'),'[][0:1/.]');
    // Complete or explicit failure: never display the first 6,000 nodes as if
    // they were the complete tree. Failure must leave FS usable in that event.
    const result=await call('(()=>{const picture=ne.display_equiv["树形图"].html(args);'+
        'return [picture,ne.FS("A2",1),ne.compare("A1","A2")];})()', '[][0:1/^(.~7000)]');
    assert.match(result[0],/未显示局部图/);assert(!result[0].includes('<svg'));
    assert.equal(result[1],'[][0:1/.]');assert.equal(result[2],-1);
    // Expansion-size guard is checked before materializing a gigantic string.
    let enormous='.';for(let n=0;n<7;n++)enormous='^('+enormous+'~10)';
    await assert.rejects(call('ne.display.plain(args)','[][0:1/'+enormous+']'),/完整列表长度/);
    assert.equal(await call('ne.FS("A2",1)'),'[][0:1/.]');
    console.log(JSON.stringify({ok:true,samples:samples.length,nodes,heads,links,guards:2,
        milliseconds:Date.now()-started,memoryMB:Math.round(process.memoryUsage().rss/1048576)}));
}
main().catch(error=>{console.error(error);process.exitCode=1;});
