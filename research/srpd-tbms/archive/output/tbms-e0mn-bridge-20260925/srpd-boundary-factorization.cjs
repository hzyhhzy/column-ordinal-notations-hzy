'use strict';

// Algebraic auxiliary operations, NOT new fundamental-sequence rules.
const assert=require('node:assert/strict');
const L=require('../m13-lists-20260926/M13-lists.ne-rewritten.js');

function tail(graph,s) {
  assert(Number.isSafeInteger(s)&&s>=0&&s<=graph.length);
  return graph.slice(s).map(column=>column.slice(s).map(p=>p-s));
}

// The removed lower rows carry a control address, despite the remaining last
// column being empty. Keep that address as external data instead of falsely
// treating this operation as the ordinary FS of the upper graph.
function ghostExpand(graph,cut,n) {
  assert(Number.isSafeInteger(n)&&n>=0);
  assert(graph.length&&graph.at(-1).length===0);
  assert(Number.isSafeInteger(cut)&&cut>=0&&cut<graph.length);
  if(!n)return graph.slice(0,-1);
  const out=graph.slice(),span=graph.length-cut;
  for(let b=0;b<n;b++) {
    const copies=out.slice(cut).map(column=>{
      const moved=column.map(p=>p>=cut?p+span:p);
      return moved.slice(0,cut).concat(
        moved.length>cut?Array(span).fill(moved[cut]):[],moved.slice(cut));
    });
    out[out.length-1]=cut?out[cut-1].slice():[];
    out.push(...copies);cut+=span;
  }
  return out.slice(0,-1);
}

// A block starting t columns farther to the right: duplicate its first row t
// times and relabel every parent. Every dependency remains inside that block.
function inflate(graph,t) {
  assert(Number.isSafeInteger(t)&&t>=0);
  return graph.map(column=>{
    const moved=column.map(p=>p+t);
    return moved.length?Array(t).fill(moved[0]).concat(moved):[];
  });
}

function rootGhostClosedForm(graph,n) {
  assert(graph.length&&graph.at(-1).length===0);
  const out=[];
  for(let b=0;b<=n;b++)out.push(...inflate(graph,b*graph.length));
  return out.slice(0,-1);
}

function values(graph) {
  const result=[];
  for(const column of graph)
    result.push(column.map((p,t)=>(result[p-1][t]??0)+1));
  return result;
}

function padFirstRow(matrix,t) {
  return matrix.map(column=>column.length?Array(t).fill(column[0]).concat(column):[]);
}

const lowerStrip=(graph,c)=>graph.map(column=>column.slice(0,c));

// The lower strip never triggers row insertion in this particular step. This
// is the row-unmodified parent-list copying rule, written independently.
function noInsertionExpand(graph,n) {
  if(!graph.length||!n||!graph.at(-1).length)return graph.slice(0,-1);
  const out=graph.slice();
  for(let b=0;b<n;b++) {
    const col=out.at(-1),h=col.length,c=col.at(-1),span=out.length-c;
    const copies=out.slice(c).map(source=>source.map(p=>p>=c?p+span:p));
    out[out.length-1]=col.slice(0,-1).concat(out[c-1].slice(h-1));
    out.push(...copies);
  }
  return out.slice(0,-1);
}

function recombine(lower,upper,c) {
  assert(lower.length-c===upper.length);
  return lower.map((column,j)=>j<c?column.slice():column.concat(upper[j-c].map(p=>p+c)));
}

function factorExpand(graph,n) {
  if(!graph.length||!graph.at(-1).length)return graph.slice(0,-1);
  const c=graph.at(-1).at(-1),u=tail(graph,c);
  return recombine(noInsertionExpand(lowerStrip(graph,c),n),rootGhostClosedForm(u,n),c);
}

module.exports={L,tail,ghostExpand,inflate,rootGhostClosedForm,values,padFirstRow,
  lowerStrip,noInsertionExpand,recombine,factorExpand};
