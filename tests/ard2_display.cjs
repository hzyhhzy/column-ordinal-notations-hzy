/* ARD2 display regression: complete graphs, both SELF slots, tight triangles.
   Run node --max-old-space-size=256 tests/ard2_display.cjs.
   One process, <=512 MiB RSS, 25-second overall and 1.5-second VM call limits.
   No browser/network, files are read-only, no screenshot claim. */
'use strict';
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm');
const assert=require('node:assert/strict');
const started=Date.now(),scope=vm.createContext({queueMicrotask});
scope.register_notation=n=>{assert(!scope.ne);scope.ne=n;};
vm.runInContext(fs.readFileSync(path.join(__dirname,'../notations/ARD2/ARD2.ne-rewritten.js'),'utf8'),scope,{timeout:1200});
async function call(code,args){
  await Promise.resolve();assert(Date.now()-started<25000,'25-second deadline');
  assert(process.memoryUsage().rss<512*1048576,'512 MiB RSS ceiling');
  scope.args=args;return vm.runInContext(code,scope,{timeout:1500});
}
const native=value=>JSON.parse(JSON.stringify(value));
const identity=e=>[e.k,e.p,e.q,e.j].join(',');
const ids=entries=>entries.map(identity).sort();
const counters={samples:0,arcGroups:0,tableEntries:0,roundTrips:0,guards:0};
function parse(text){
  return [...text.matchAll(/\[([^\]]*)\]/g)].map(m=>
    [...m[1].matchAll(/\((\d+),(\d+),(\d+)\)/g)].map(t=>t.slice(1).map(Number)));
}
function allEntries(cols){return cols.flatMap((col,j)=>col.map(([k,p,q])=>({k,p,q,j})));}
function inside(d,x,y){
  assert(Number.isFinite(x)&&Number.isFinite(y));
  assert(x>=-1e-6&&x<=d.width+1e-6&&y>=-1e-6&&y<=d.height+1e-6,
    `Point (${x},${y}) outside ${d.width}x${d.height}`);
}
function geometry(d){
  assert(d.width>0&&d.height>0);
  for(const e of d.elements){
    if(e.type==='line'){inside(d,e.x1,e.y1);inside(d,e.x2,e.y2);}
    else if(e.type==='circle'){inside(d,e.x-e.r,e.y-e.r);inside(d,e.x+e.r,e.y+e.r);}
    else throw Error('Unexpected NER drawing primitive');
  }
  for(const t of d.extra_text){inside(d,t.x,t.y);assert.equal(typeof t.text,'string');}
}
function arc(d,cols){
  geometry(d);const m=d._anchored,entries=allEntries(cols);
  assert(m.complete);assert.equal(m.groups,entries.length);assert.equal(m.columns,cols.length);
  assert.deepEqual(ids(m.routes),ids(entries),'all source groups exactly once');
  assert.deepEqual(ids(d.elements.filter(e=>e._anchored?.kind==='relation').map(e=>e._anchored)),ids(entries));
  for(let i=0;i<m.routes.length;i++){
    const route=m.routes[i],box=route.label;
    assert(route.k<=route.j&&route.q<=route.j&&route.p<route.j,'ARD2 scope, not old ARD scope');
    for(const point of route.points)inside(d,point.x,point.y);
    inside(d,box.x,box.y);inside(d,box.x+box.width,box.y+box.height);
    assert.equal(route.sourcePort.x,m.columnXs[route.j]);
    assert.equal(route.parentPort.x,m.columnXs[route.p]);
    const labels=d.extra_text.filter(t=>t._anchored?.kind==='root'&&identity(t._anchored)===identity(route));
    assert.equal(labels.length,1);assert.equal(labels[0].text,String(route.q));
    const rim=d.elements.filter(e=>e._anchored?.kind==='root-frame'&&identity(e._anchored)===identity(route));
    assert(rim.length>=30,'root number has its closed outline');
    for(let n=0;n<i;n++){
      const b=m.routes[n].label;
      assert(!(box.x<b.x+b.width-1e-6&&b.x<box.x+box.width-1e-6&&
        box.y<b.y+b.height-1e-6&&b.y<box.y+box.height-1e-6),'root labels do not overlap');
    }
  }
  if(m.countComplete){
    assert(m.counts.every(s=>/^\d+$/.test(s)));
    const labels=d.extra_text.filter(t=>t._anchored?.kind==='column');
    assert.deepEqual(labels.map(t=>t.text),m.counts);
  }else{
    assert(m.counts.every(s=>s===''),'no fake numbers when counting fails');
    assert(d.extra_text.some(t=>t._anchored?.kind==='count-warning'&&/计数超限/.test(t.text)));
  }
  counters.arcGroups+=entries.length;
}
function table(d,cols){
  geometry(d);const m=d._adjacency,entries=allEntries(cols);
  assert(m.complete&&m.triangular);assert.deepEqual(ids(m.entries),ids(entries));
  assert.equal(m.columns,cols.length);assert.equal(m.groups,entries.length);
  assert.equal(m.rowHeight,14);assert(m.cell<=String(Math.max(0,cols.length-1)).length*8+4);
  assert.equal(d.extra_text[0]._adjacency.kind,'counts');
  for(const t of d.extra_text)assert(['counts','layer','cell','diagonal-index'].includes(t._adjacency.kind));
  for(const layer of m.layers){
    const labels=d.extra_text.filter(t=>t._adjacency.kind==='diagonal-index'&&t._adjacency.k===layer.k);
    const fills=d.elements.filter(e=>e._adjacency.kind==='diagonal-background'&&e._adjacency.k===layer.k);
    assert.equal(labels.length,cols.length);assert.equal(fills.length,cols.length);
    labels.forEach((t,j)=>{assert.equal(t.text,String(j));assert.equal(t.x,m.columnXs[j]);});
    for(const e of fills){assert.equal(e.width,m.rowHeight);assert(e.stroke_color.color.a>0);}
    const rowLabel=d.extra_text.find(t=>t._adjacency.kind==='layer'&&t._adjacency.k===layer.k);
    assert.equal(rowLabel.text,layer.k);assert(!rowLabel.text.includes('k='));
  }
  for(const e of m.entries){
    assert(e.p<e.j,'off-diagonal relations strictly above diagonal');
    const layer=m.layers.find(t=>t.k===e.k);
    assert.equal(e.x,m.columnXs[e.j]);assert.equal(e.y,layer.y+(e.p+0.5)*m.rowHeight);
  }
  counters.tableEntries+=entries.length;
}
async function main(){
  assert.equal(scope.ne.id,'ard2-v01');assert.equal(scope.ne.name,'ARD2');
  assert.deepEqual(native(await call('Object.keys(ne.display_equiv)')),
    ['计数序列','弧线图','邻接表（文字）','邻接表（图）']);
  assert.equal(scope.ne.display.name,'列表');assert(!scope.ne.display_equiv['列表']);
  assert(!scope.ne.display_equiv['计数序列'].from_display);
  assert(await call('ne.FS===ne.FS_alter&&ne.FS===ne.FS_short'));
  assert.deepEqual(native(await call('ne.init()')),['Limit of ARD2','[]','∅']);
  const samples=['A1','A2','A3','A4','A2[2]',
    '[][][][(3,0,3),(1,2,0)]',
    '[][][][][(4,2,4),(0,3,4),(2,1,0)]'];
  for(const raw of samples){
    const canonical=await call('ne.display.plain(args)',raw),cols=parse(canonical);
    assert((await call('ne.display.html(args)',raw)).includes('font-family:inherit'));
    assert(!(await call('ne.display.html(args)',raw)).includes('<br'));
    const text=await call('ne.debug.adjacency_text(args)',raw);
    assert(!/\s/.test(text));assert.equal(await call('ne.debug.adjacency_from_text(args)',text),canonical);
    counters.roundTrips++;
    const normal=native(await call('ne.debug.diagram(args)',raw));arc(normal,cols);
    const flipped=native(await call('ne.debug.diagram(args,{invert_vertical:true})',raw));arc(flipped,cols);
    assert.deepEqual(ids(normal._anchored.routes),ids(flipped._anchored.routes));
    const d=native(await call('ne.debug.adjacency_diagram(args)',raw));table(d,cols);
    const nd=native(await call('ne.draw_diagram.draw_diagram(args,{current_equiv:"邻接表（图）"})',raw));table(nd,cols);
    for(const view of ['弧线图','邻接表（图）']){
      const svg=await call('ne.display_equiv[args.view].html(args.raw)',{view,raw});
      assert(svg.includes('<svg')&&svg.includes('font-family:inherit'));
      assert(!/\bNaN\b|\bInfinity\b|<script\b|onload=|onclick=|<image\b/i.test(svg));
      const attr=view==='弧线图'?/data-relation=/g:/data-adjacency=/g;
      assert.equal((svg.match(attr)||[]).length,allEntries(cols).length);
    }
    counters.samples++;
  }
  assert.equal(await call('ne.debug.adjacency_text("A2")'),'[][;1]');
  assert.equal(await call('ne.debug.adjacency_from_text("[][;0]")'),'[][(1,0,0)]');
  for(const s of ['[0]','[][;;0]','[][;2]','[][,0]'])
    await assert.rejects(call('ne.debug.adjacency_from_text(args)',s));
  // A deterministic counter refusal must not suppress any geometry or poison FS.
  const raw='A3',cols=parse(await call('ne.display.plain(args)',raw));
  const refused=native(await call('ne.debug.diagram(args,{count_max_work:1})',raw));
  arc(refused,cols);assert.equal(refused._anchored.countComplete,false);counters.guards++;
  const fallback=native(await call(`(()=>{
    const original=ne.display_equiv['计数序列'].plain;
    try {ne.display_equiv['计数序列'].plain=()=> '（计数超限；未给出近似值，请查看列表）';
      return ne.debug.adjacency_diagram(args);
    }finally{ne.display_equiv['计数序列'].plain=original;}
  })()`,raw));
  table(fallback,cols);assert.equal(fallback._adjacency.countComplete,false);counters.guards++;
  // Dense crossing/nested intervals exercise geometry independently of counting.
  const denseColumns=Array.from({length:7},(_,j)=>
    Array.from({length:j*(j+1)},(_,i)=>[Math.floor(i/j),i%j,j]));
  const crossing=denseColumns.map(col=>'['+col.map(e=>'('+e.join(',')+')').join(',')+']').join('');
  const crossingDiagram=native(await call('ne.debug.diagram(args,{count_max_work:1})',crossing));
  arc(crossingDiagram,denseColumns);counters.samples++;
  // Exercise a real budget refusal, not only the injected maxWork=1 branch.
  const costly=native(await call('ne.debug.diagram("A8")'));
  assert(costly._anchored.complete&&!costly._anchored.countComplete);
  arc(costly,Array.from({length:8},(_,j)=>j?[[j,j-1,j]]:[]));counters.guards++;
  const dense='[]'.repeat(46)+'['+Array.from({length:47*46},(_,i)=>
    '('+Math.floor(i/46)+','+(i%46)+',0)').join(',')+']';
  const large=native(await call('ne.draw_diagram.draw_diagram(args,{})',dense));
  assert.equal(large._anchored.complete,false);assert.equal(large.elements.length,0);
  assert(large.extra_text.some(t=>/未绘制局部图/.test(t.text)));counters.guards++;
  assert.equal(await call('ne.FS("A2",1)'),'[][(1,0,0),(0,0,1)]');
  await assert.rejects(call('ne.FS("A2",10n**80n)'),/超限/);counters.guards++;
  console.log(JSON.stringify({ok:true,...counters,milliseconds:Date.now()-started,
    rssMiB:Math.ceil(process.memoryUsage().rss/1048576),processes:1,
    scope:'Native NER primitives and SVG structural audit; no live browser screenshot'}));
}
main().catch(error=>{console.error(error);process.exitCode=1;});
