'use strict';

// Native TARGET paths only. Does not implement or prove the TBMS simulation.
// Even truncation/exposure macros below execute bounded actual SRPD steps.
const assert=require('node:assert/strict');
const S=require('../notations/SRPD/SRPD.ne-rewritten.js');
const started=Date.now(),limits={ms:15000,rssMiB:512,events:60000,width:800};
let g=S.INITIAL,events=0,localSteps=0;const stages=[];
function tick(){assert(Date.now()-started<limits.ms,'path time guard');assert(process.memoryUsage().rss<limits.rssMiB*2**20,'RSS guard');assert(++events<=limits.events,'event guard');}
function fs(n){tick();const old=g;g=S.expand(g,n);assert(g.length<=limits.width);if(old.length)assert(S.compare(g,old)<0);}
function trim(n){assert(n>=0&&n<=g.length);while(g.length>n)fs(0);}
function down(){assert(g.at(-1)?.length);const before=g,N=g.length,c=before.at(-1),p=c.at(-1);
  fs(1);trim(N);assert.deepEqual(g,before.slice(0,-1).concat([c.slice(0,-1).concat(S.parentColumn(before,p).slice(c.length-1))]));localSteps++;}
function truncate(h){assert(h>=1&&h<=g.at(-1).length);const expected=g.at(-1).slice(0,h);
  while(g.at(-1).length>h)down();assert.deepEqual(g.at(-1),expected);}
function expose(p,h){for(;;){assert(g.at(-1).length>=h);truncate(h);if(g.at(-1).at(-1)===p)return;
  assert(g.at(-1).at(-1)>p);down();}}
function record(name,counts){assert.equal(S.counts(g),counts,name);stages.push({name,counts,graph:g.map(c=>c.slice()),events});return g.map(c=>c.slice());}
function resetKnown(a){g=a.map(c=>c.slice());} // Branch from an already certified native ancestor.
const prefix='1,2,4,8,4,1,2,9,38,4';
fs(5);expose(3,1);fs(1);trim(6);expose(2,1);fs(1);trim(6);
const W=record('W','1,2,4,8,4,2');fs(1);
record('W[1]','1,2,4,8,4,1,2,9,38,9');for(let i=0;i<4;i++)down();
fs(1);fs(4);expose(7,2);fs(1);trim(17);
record('Q1',prefix+',12,44,156,503,504,511,548');
trim(12);truncate(9);fs(2);expose(10,3);fs(1);trim(14);truncate(3);fs(2);expose(7,2);fs(1);trim(17);
const Qtrim=record('Qtrim',prefix+',12,42,73,105,106,113,150');
trim(13);expose(10,2);fs(1);trim(14);truncate(2);fs(2);expose(7,2);fs(1);trim(17);
const Qw=record('Qw',prefix+',12,42,44,46,47,54,91');
fs(11);trim(26);for(let i=0;i<9;i++)down();
record('V',prefix+',12,42,44,46,47,54,90,266,1072,4384,16474,56026,173593,495365,1315558,3281173');
resetKnown(Qtrim);trim(11);truncate(5);fs(2);expose(7,2);fs(1);trim(14);
const Ceps=record('Cepsilon',prefix+',9,10,17,51');
trim(11);down();down();record('Z',prefix+',7');fs(2);fs(1);trim(13);truncate(2);
const candidate=record('open epsilon candidate',prefix+',6,7,9');
for(const n of [0,1,2,3,4,8,16,32]){tick();const expected=candidate.slice(0,12).concat(Array.from({length:n},(_,i)=>[12+i]));assert.deepEqual(S.expand(candidate,n),expected);}
assert(S.compare(candidate,Ceps)<0&&S.compare(Ceps,Qw)<0&&S.compare(Qw,W)<0);
console.log(JSON.stringify({scope:'actual native target reachability and candidate FS formula only; not a TBMS rank proof',
  limits,stages,events,localSteps,candidateIndices:[0,1,2,3,4,8,16,32],
  elapsedMs:Date.now()-started,rssMiB:process.memoryUsage().rss/2**20},null,2));
