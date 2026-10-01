# CTN Comprehension Table Notation · [中文版](definition.zh-CN.md)

**CTN = Comprehension Table Notation.** This is the linear-limit edition previously called CTN2 in research files, renamed CTN on 2026-10-01. The original CTN frontend is retired and is not packaged as another edition. The renaming preserves the former CTN2 domain, comparison, indexed expansions and displays.

CTN is a computable **pseudo-ordinal notation**, not a well-order. Its [paper argument](../../proofs/paper/ctn-well-founded-part.md) identifies its maximal well-founded initial segment with $\omega_1^{CK}$. This is neither whole-system well-ordering nor a computation of $\mathrm{PTO}(Z_2)$. There is no Lean formalization; bounded tests do not establish the CK theorem.

## 1. Expressions and order

Each column is 1 or 2. Expressions are finite strings, ordered by ordinary lexicographic order with $1<2$ and proper prefixes smaller. The empty string is zero. The one-column string `2` is the global maximum: **it is not an ordinal and is not CK**.

Not every binary string is legal. The finite table checker below specifies the domain. Legality does not decide membership in the well-founded part, nor whether a table has an infinite extension.

## 2. The finite logical table

Actual table values are natural numbers. The table contains membership bits $M(i,n)$, formula truth values $V(\varphi,N,S)$, existential witnesses $W(\varphi,N,S)$ and comprehension-set indices $C(\varphi,N,S)$. Number and set environments N and S are separate lists.

Five kinds of obligations are checked:

1. Compute atomic arithmetic; membership formulas read M.
2. Negation and conjunction obey their Boolean truth clauses.
3. A true existential has a witness whose instance is true.
4. Every available instance of a false existential is false, for either sort.
5. The row named by C has the membership bits prescribed by its formula.

**Check only obligations whose addresses and dependencies have appeared.** A missing field defers that obligation. There is no model search, semantic truth oracle or run-until-halting computation. Every fixed obligation and its finite dependencies eventually appears along an infinite table.

Fix Cantor pairing

$$p(a,b)=\frac{(a+b)(a+b+1)}2+b.$$

Lists use 0 for empty and $1+p(\text{head},\text{tail code})$ otherwise. A formula is $p(\text{opcode},\text{payload})$, with multiple arguments paired right-associatively and unary arguments used directly.

| Opcode | Formula | Arguments |
| --- | --- | --- |
| 0 | Number variable is zero | i |
| 1 | Equality | i,j |
| 2 | Successor | i,j: $N_i+1=N_j$ |
| 3 | Addition | i,j,k |
| 4 | Multiplication | i,j,k |
| 5 | Membership | i,j: $N_i\in S_j$ |
| 6 | Negation | Subformula |
| 7 | Conjunction | Two subformulas |
| 8 | Existential number | Subformula |
| 9 | Existential set | Subformula |

Variables use de Bruijn indices: index 0 is the environment head. Instantiation prepends a witness only to the appropriate sort. Put $q=p(\varphi,p(N,S))$.

| Address | Value / obligation |
| --- | --- |
| $p(0,p(i,n))$ | M(i,n) |
| $p(1,q)$ | V and atomic, Boolean or positive-existential check |
| $p(2,q)$ | W; nonexistential cases must be 0 |
| $p(3,q)$ | C; scope checked with one extra number variable |
| $p(4,p(q,n))$ | Store 0 and check comprehension instance n |
| $p(5,p(q,n))$ | Store 0 and check negative-existential instance n |

Reserved addresses and invalid syntax receive 0. A length-m table checks addresses $0,\ldots,m-1$; reading an address at least m defers the check, without allocating an array of that size. The complete implementation is [ctn_table.py](ctn_table.py).

Let T be the tree of accepted actual-value tables. Encode each actual value a as a+1:

$$U=\{s:(\forall i<|s|)\ s_i>0\ \land\ (s_0-1,\ldots,s_{|s|-1}-1)\in T\}.$$

The empty table belongs to U. Encoded value 0 is a terminal branch at **every** node, not a special clause inserted solely to locate ω.

## 3. The legal domain

Write $b(k)=1\,2^k1$ and $E(s)=b(s_0)\cdots b(s_{m-1})$. Powers here mean literal repetition, not ordinal exponentiation. The domain consists exactly of these five families:

| Form | Conditions / meaning |
| --- | --- |
| E(s) | s∈U; table entry |
| E(s)2 | s∈U; closing cap |
| E(s)1 2^k | s∈U, k≥0; open block |
| E(s)2 1^j | Nonempty s∈U, j≥1; successor tail after a nonroot cap |
| E(s⌢k)1^j | s∈U, s⌢k∉U, j≥0; terminal tail of a failed child |

Neither kind of successor tail continues the logical table. No tail is allowed above the global maximum `2`. The domain is closed under literal prefixes, and every legal expression is reachable from `2` by finitely many expansions.

## 4. Fundamental sequences

The empty expression remains empty. Every nonempty A has A[0] equal to deletion of its last column. Below n≥1, and P denotes the old prefix after deleting that column:

$$ (P1)[n]=P. $$

$$ (E(s)2)[n]=E(s)1\,2^{n-1}. $$

For an open-block final 2, write $A=E(s)1\,2^{k+1}=P2$ and set

$$
A[n]=\begin{cases}
P12\,1^{n-1},&s^\frown k\in U,\\
P1^n,&s^\frown k\notin U.
\end{cases}
$$

| A | A[0] | A[1] | A[2] | A[3] |
| --- | --- | --- | --- | --- |
| `2` | Empty | `1` | `12` | `122` |
| `12` | `1` | `11` | `111` | `1111` |
| `122` | `12` | `1212` | `12121` | `121211` |
| `12121` | `1212` | `1212` | `1212` | `1212` |

A legal nonempty expression has a direct predecessor **iff it ends in 1**. Ending in 2 means no direct predecessor, and denotes a limit ordinal only within the well-founded part. Every step strictly decreases lexicographic order. A[n] is a full column prefix of A[n+1]; for expressions ending in 2,

$$ |A|-1+n\le |A[n]|\le |A|+n\qquad(n\ge1). $$

After the first term, each increment of n adds exactly one column. Thus A[∞] is genuinely an infinite prefix union, not another finite legal expression. Strict order also coincides with nonempty finite expansion reachability.

## 5. NER and the two counting conventions

Import [CTN.ne-rewritten.js](CTN.ne-rewritten.js) into the custom-notation facility of [NER](https://smilelee-lyx.github.io/ne-rewritten/). Its name is **CTN**, with new ID `ctn-linear-20261001`. Disable locally installed old CTN/CTN2 scripts to avoid stale menu entries. Former CTN2 raw strings remain valid inputs; an original-CTN string must not automatically retain its former ordinal meaning.

All six views are retained: raw columns / counts, column list, grouped shorthand, finite table, consecutive 2s before each 1, and block counts (2s after each 1 plus one).

- Actual per-column clearance counts are the raw 1/2 string. Count clearance of the current position, not the entire appended suffix's descent time.
- Runs of 2s before each 1 are not those counts; retain any unfinished final run separately.
- Group a 1 and its following k twos into one block: its clearance count is k+1. Thus `1221` displays `3,1`. This is a secondary grouping, not a replacement of actual column boundaries.

Only raw-column/list views accept input. `0`, `∅` and `[]` mean empty. All three FS interfaces agree. Original browser guards are retained: 200,000 columns, 1,000,000 input characters, approximately 600 ms per operation and 3,000,000 charged operations. Exhaustion raises an error, never truncates a sequence or changes its mathematics.

The Python core [ctn.py](ctn.py) uses only its sibling checker and the standard library. It has no browser guards; callers must bound large outputs. For actual input length L, the paper gives the conservative bound $O(L\log^4(L+2)+n)$ time and $O(L+n)$ space. This is not a bound in the binary length log n of the output parameter.

## 6. Locations and reproduction

Natural m is m ones and `12=ω`. The 32-column ω², 56-column ω³ and exact sparse ω^ω expression are in [small ordinal locations](small-ordinals.md). The full ω^ω word has 69,593,927 columns and exceeds normal browser limits. ε₀ has not been explicitly located. No separate arithmetic notation branch was added to manufacture short examples.

From the repository root:

```sh
python -B -m unittest discover -s tests -p 'ctn_*.py' -v
node tests/ctn.cjs --print-reference-script | python -B - | node --max-old-space-size=256 tests/ctn.cjs --fixtures-stdin
python -B notations/CTN/locate_omega_omega.py
```

Checks need no private checkout, do not materialize the giant word and perform no unbounded descent search. See [VALIDATION](../../VALIDATION.md) and [SOURCES](../../SOURCES.md) for scope and provenance. This addition creates neither a Lean project nor PDFs and changes no existing notation proof.
