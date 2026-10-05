# DQDN definition · [中文版](definition.zh-CN.md)

DQDN means **Demand Query Diagram Notation**. This is the incremental typed-generator edition of 2026-10-05, not the earlier whole-certificate enumerator. Its global standard domain has a paper well-ordering argument; neither the type kernel nor that argument has a Lean certificate. See [usage](README.md), [well-ordering](../../proofs/paper/dqdn-well-ordering.md) and [comparison status](../../research/dqdn/README.md).

## Columns

An expression is a finite sequence of tagged columns. Each data column has at most three pointers to earlier data columns, or a natural-number atom. Long records are split into small DAG nodes. A variable distance is a de Bruijn index, not a column number. An active column `!p` points to a source at an earlier data column.

Ordinary program nodes are a variable `v`, numeral `n`, lambda `l`, application `a`, successor `s`, recursor `r`, and strict query `q`. Other data nodes describe kinds, types, contexts, typed judgments, type equalities, libraries and partially filled generator instructions. They do not hide an entire type tree inside one column.

The public domain is defined below by **reachability from the same TOP**, not by the validity of these tags alone. Untyped raw graphs are not admitted.

## Demand computation

The five contraction rules are

$$
(\lambda x.t)u\longrightarrow t[u/x],\qquad
S(n)\longrightarrow n+1,\qquad Q(n)\longrightarrow m\quad(m\in\mathbb N),
$$

$$
R(z,s,0)\longrightarrow z,\qquad
R(z,s,n+1)\longrightarrow s\,n\,(R(z,s,n)).
$$

The demanded contexts are

$$E::=[]\mid E\,u\mid S(E)\mid Q(E)\mid R(z,s,E).$$

Application examines its function first and contracts beta without first evaluating the argument. Successor and query force their numerical argument; a recursor first forces only its third argument. Evaluation does not go under lambda. One fundamental operation finds and contracts **one** demanded redex, not a whole normalization.

All substitutions avoid capture. Immutable DAG sharing shares syntax, not answers: different occurrences of the same `Q(0)` may receive different numbers. Contraction rebuilds the path to the selected occurrence and leaves other occurrences unchanged.

## Types and finite levels

Kinds are `*` and kind arrows, with tree height zero at `*`. Level 0 permits simple types over Nat, arrows and primitive recursion. Level k≥1 permits Fω typing rules, with every kind height strictly below k. In particular level 1 is System F with native Nat and Rec, not full Fω. No rule compares a kind level with a column index.

Type constructors are Nat, variable, arrow, universal quantifier, type lambda and type application. Term judgments include variables, numerals, lambda/application, type abstraction/instantiation, S, Q and recursion at any permitted result type. Conversion is justified by explicit finite beta/eta steps at named addresses; the implementation never runs a complete type normalizer.

Here are all 28 local construction entry points in their fixed implementation order. Changing this order would change the actual fundamental sequences.

| Index | Operation | Selected fields |
| ---: | --- | --- |
| 0 | kind_arrow | kind, kind |
| 1 | kind_context | kind context, kind |
| 2 | term_context | kind context |
| 3 | extend_context | context, type |
| 4 | lift_context | context, kind |
| 5 | nat_type | kind context |
| 6 | type_variable | kind context, number |
| 7 | type_arrow | type, type |
| 8 | type_forall | type |
| 9 | type_lambda | type |
| 10 | type_application | type, type |
| 11 | weaken_type | type, kind |
| 12 | variable | context, number |
| 13 | number | context, number |
| 14 | lambda | term |
| 15 | application | term, term |
| 16 | polymorphic | term |
| 17 | instantiate | term, type |
| 18 | successor | term |
| 19 | query | term |
| 20 | recursor | term, term, term |
| 21 | type_of | term |
| 22 | equality_refl | type |
| 23 | equality_sym | equality |
| 24 | equality_trans | equality, equality |
| 25 | type_beta | type, address number |
| 26 | type_eta | type, address number |
| 27 | convert | term, equality |

Contexts and judgments must match; application and recursion must have the required types. Generalization cannot let a variable escape its scope. Eta contraction requires the removed variable not to occur freely. The capture-avoiding index operations and negative-shift checks implement these side conditions. This is a substantial type layer: saying there are only five computation rules does **not** make the full notation as simple as RPD.

## Incremental generator

`G(k)` chooses finite fuel b and enters `B(k,b,L,pending)`. The initial library contains only the fixed basic objects: empty contexts, the basic kind, Nat and a closed zero judgment. It contains no arbitrary program supplied by neighbouring columns.

With positive fuel, one step either chooses a rule, chooses its next field, or commits a fully selected rule. Every such step consumes one fuel unit. Rule numbers are reduced modulo 28. Object fields are selected from the existing library's reachable objects of the appropriate sort, in the deterministic traversal order of [typed_builder.py](typed_builder.py), modulo that list's length; only numerical fields are unrestricted natural numbers. Failure of a local side condition, or absence of candidates, terminates that branch at zero.

At zero fuel, output the newest closed Nat term in the library, or zero if there is none. An incomplete instruction is discarded without searching for a completion. The output is then evaluated by the demand rules. Term construction cannot produce a `G` or `B` program instruction, so an ordinary program cannot refill its fuel or reenter a generator.

Every finite allowed typing derivation can be generated in dependency order. Intermediate contexts and type conversions are explicit finite objects. All objects produced by substitution actually occur in the DAG; there is no exponentially large implicit type treated as free data.

## Source choices and column expansion

One source step uses answer c(i), where

$$c(0)=0,\qquad c(2m+1)=m,\qquad c(2m+2)=c(m).$$

Each answer occurs infinitely often; for m>0 its first occurrence is at index 2m+1. This fair repetition matters for ordinal cofinality, even for a source with only finitely many distinct children.

The empty expression is zero. If the last column is data, every A[n] deletes it. If it is active, remove it and append the first n child blocks, in order. Each block contains a data marker, missing shared nodes of that child, then an active column for the child if it can step; an already stopped child contributes a second leaf-data column instead. Existing syntax is reused deterministically at its earliest position. No earlier column is changed.

Consequently A[0] deletes the last column and A[n] is a literal structural prefix of A[n+1]. At a nonzero limit other than TOP, the length is at least |A|−1+2n. Per-child processing uses finite DAG walks and local substitution; it does not perform full program or type normalization. Complexity is polynomial in the actual input bit length and the **numerical value** n, including the explicit intermediate/output graph. This is not a polynomial bound in log n for an operation emitting n blocks.

## Common root and comparison

Let

$$P_k=(G(0),!G(0),\ldots,G(k),!G(k)).$$

Add the one-column root TOP with TOP[0]=empty and TOP[n+1]=P_n. The standard lower domain consists of all finite descendants of the P_k, including their prefixes. TOP names their supremum; the extra greatest element is not counted in that lower domain's order type. TOP's n-th fundamental-sequence term has 2n columns for n>0.

In this common domain, assign count 1 to data and 2 to active columns; represent TOP itself by the one-digit word 2. Count words are injective and their ordinary lexicographic order is the notation order. This claim does not apply to unrelated hand-written source graphs with the same count word.

To decide standardness of a length-L candidate, start from P_L. Find the first structurally different column. A candidate prefix is accepted; otherwise the current column must be active and the candidate column data. Delete the later current columns and expand enough child blocks to cover L positions. Repeat. Each successful iteration fixes at least one more candidate column, so at most L+1 iterations are needed. Budget exhaustion is an exception, not a negative answer. See `is_standard`; [standard.py](standard.py) applies this check at the public raw-column boundary.

## Semantics and proof status

The [paper proof](../../proofs/paper/dqdn-well-ordering.md) first establishes well-foundedness of all-answer typed source trees, then uses source rank h. Data columns have weight 1 and an active source has weight ω^h; take the ordinal sum in column order. Fair repetition makes the fundamental sequence cofinal. The common-root prefix argument transfers strict descent to the entire standard lexicographic order, not merely consecutive expansion chains.

The paper strength claim is that the global limit is at least PTO(Zω), where Zω is the union of finite-order full-comprehension arithmetics, without adding arbitrary higher-order choice. That lower bound and the [BMS comparison](../../research/dqdn/bms-top2.md) are separate from the well-ordering argument. An exact PTO equality and an optimized axiomatic upper bound remain open.

An independent 21-column ε₀ source is not the same raw expression as the standard two-column P₀=TOP[1]=ε₀. The latter equality uses the uniform System T query-tree upper bound plus a cofinal family of finite towers; see [epsilon0](../../research/dqdn/epsilon0.md). Source rank alone cannot identify an entire standard expression when preceding sibling blocks remain.

Untyped ΔΔ gives a genuine infinite descent in the raw graph language. It is rejected by the standard-domain test. Finite differential, substitution, type and view tests support implementation fidelity, but do not constitute a general type-soundness, normalization or ordinal proof.
