# A fixed-row BMS upper bound for the BTnSS limit

[中文](upper-bound.zh-CN.md) · [Scope and evidence](README.md)

Fix the NER **strong BT*(-1)Y-nSS v2** definition, with $n\ge2$ and $d=n-1$ numerical coordinates. Use the default BM4 short fundamental sequence for BMS. This paper uses the previously established finite block invariants of standard BTnSS terms and the BMS well-ordering theorem. It does not use the earlier I3 model interpretation of BTnSS, and it does not require the encoding to commute with equally indexed fundamental sequences.

Write

$$
B_r=(0^r)(1^r),\qquad U_r=(0^r)(1^r)(2^r)(3^r).
$$

The supremum of standard $r$-row BMS is $|B_{r+1}|$. We prove

$$
\boxed{\lim(\mathrm{BTnSS})\le |U_{n+1}|<|B_{n+2}|.}\tag{1}
$$

The intermediate bound is one standard BMS node, independent of the source seed, forest depth and term size. Strictness does not follow merely by taking the supremum of individually smaller images: it follows from the additional fixed ceiling $U_{n+1}<B_{n+2}$. This is a paper proof, not a Lean formalization.

## 1. Source invariants and their scope

A source column has $d$ numerical coordinates and a finite list of attached forests; forest columns have the same recursive type. Numerical parents $P_j$, owner-slot representatives, complete zeroth blocks $B_x$ and complete normalized forest keys $K_x$ are those of the [frozen definitions](source-finite/definitions-and-invariants.zh-CN.md).

The standard domain consists of the terms reached from diagonal seeds by finitely many actual fundamental-sequence operations. Section 3 of the collected finite-invariant paper establishes:

- **Numerical legality.** A coordinate is its parent's corresponding coordinate plus one, or zero if there is no parent. An internal zeroth coordinate exceeds its owner's; an owner with a nonempty attachment list has every numerical coordinate positive.
- **BN.** In one forest, sibling blocks with the same zeroth parent are nonincreasing.
- **HW.** The list of forests attached to one owner is nonincreasing.
- **$\mathrm{SB}_j$, $1\le j<d$.** If $g$ is a strict $P_{j-1}$ ancestor of $x$ and they have the same $P_j$ position representative, rebasing the first $j$ rows gives $\tau^j_{g,x}(B_g)\ge B_x$.
- **$G_d$.** For a non-owner ancestor $g$ in the allowed highest-numerical backtracking range, if its key does not exceed any key along the path, full numerical rebasing and replacement of the leading list give $A_{g,x}(B_g)\ge B_x$.

These are proved by induction on finite source expansions. The model interpretation, reflection and large-cardinal initialization in the old well-ordering argument are not used here.

When a comparison crosses the first leaf, apply the separate [cross-leaf extension](lemmas/cross-leaf.zh-CN.md). A nonempty key gate cannot cross a leaf. For an empty key, compose the inequalities through consecutive leaves; at each composition the leading lists being replaced agree. This extends the block inequality, not the source root-selection rule.

## 2. The encoding and local lemmas

Use the [pruned context encoder $C^-$](lemmas/context-encoder.zh-CN.md). Its first $d$ rows encode stretched source numerical-parent edges; two further rows record keys and tags. An unbound key emits a definition $D$, a guard $H$, one slot $S$ for each attached forest, and a closing actual column $P$. An existing binding emits only $P$. A temporary forest-slot environment omits its owner's own binding.

This omission does not change the output on standard inputs. The [owner-entry lemma](lemmas/owner-entry.zh-CN.md) says that a position whose direct highest numerical parent is its owner has a strictly smaller key. It therefore cannot use the omitted binding. Only the auxiliary extension to arbitrary virtual material changes; neither source nor target FS rules change.

The required local results are:

1. $C^-$ is finite, with at most $3N+F$ columns for $N$ source-column occurrences and $F$ forest slots. It is strictly order-preserving in a fixed entering context. Queried bindings come from non-owner positions on the highest numerical chain.
2. Its output is numerically legal and has the exact parent table in the encoding paper. In particular, no forest slot has a strict key-row descendant.
3. For each $1\le b<d$, source partial rebasing commutes exactly with target rebasing at the first output representative $R$ of a source position. Here $R$ is a fresh $D$ or a reused $P$. This uses [non-owner key-comparison conjugacy in the actual context](lemmas/partial-key-comparison.zh-CN.md), not preservation of every key value.
4. [Top-two-row transport](lemmas/top-row-transport.zh-CN.md) gives exact full-numerical rebasing for actual positions sharing one definition; insertion dominance for actual positions related by strict key-row ancestry; and strict definition-head comparison for a $D/D$ pair sharing the same smaller binding. It also establishes the source ancestry, non-ownership and key gates needed in these applications.

All snapshots for virtual $C^-$ material must themselves come from $C^-$; the unpruned encoder's temporary-slot snapshots cannot be substituted.

## 3. Target BN and intermediate numerical rows

The target has $r=d+2$ rows; write $p_j$ for its parents. Its same-zeroth-parent sibling blocks have only three forms:

1. First representations $R$ of source siblings in one forest.
2. A guard $H$ and the closing $P$ belonging to the same $D$.
3. Forest slots belonging to the same $H$.

The first case follows from source BN and fixed-context order preservation. In the second, the first $d+1$ coordinates agree while the guard's tag $2$ exceeds the closing tag $0$. In the third, the slot contexts agree, so source HW and fixed-context order apply. Slots separate internal zeroth-parent paths of different forests; a closed forest cannot supply an additional external sibling. This exhausts BN.

For $1\le b<d$, nontrivial target $\mathrm{SB}_b$ pairs must be two source first representations. All first $d$ parents of an auxiliary $H$ or new $P$ are its own $D$; those of a slot are its own $H$. Same-parent auxiliary positions are siblings, not the ancestor pairs in question. First representatives retain the source-parent and slot identities.

The corresponding source pair therefore satisfies the source $\mathrm{SB}_b$ hypothesis. Exact partial rebasing and fixed-context order give

$$
\tau^b_{R_g,R_x}(B_{R_g})
=C^-_{\mathrm{entry}(x)}\bigl(\tau^b_{g,x}(B_g)\bigr)
\ge C^-_{\mathrm{entry}(x)}(B_x)=B_{R_x}.
$$

When $d=1$ this collection of intermediate conditions is empty.

## 4. The target key-row condition

Target $\mathrm{SB}_d$ requires strict $p_{d-1}$ ancestry and a common $p_d$ parent. The parent table leaves three cases.

**Guard versus slot.** Rebasing the first $d$ rows makes the first $d+1$ coordinates equal; tags $2>0$ decide strict dominance.

**Definition versus definition.** They share the exact latest actual position of their greatest smaller binding. The definition-head lemma gives strict comparison before the closing $P$, independently of the later tail.

**Actual versus actual.** They share an original definition and hence the same key binding. Their source positions form a non-owner highest-numerical ancestor pair with the required key gate. Extended $G_d$, same-key exact transport and fixed-context order give the block inequality.

Slots introduce no additional same-definition descendant pair. Their owner binding is omitted; using that key later requires a fresh definition, not the old definition position. A definition's key parent is an actual position, whereas an actual column's key parent is a definition position, so a mixed $D/P$ pair cannot share that parent. The remaining auxiliary types are excluded by the table.

## 5. The target tag-row condition

Nontrivial $\mathrm{SB}_{d+1}$ pairs are actual/actual or actual/slot. For $D$ and $H$, the tag parent equals the key parent; they do not produce the required shared-tag-parent strict key ancestry. A slot has no strict key-row descendants and cannot be the left endpoint.

**Actual/actual.** Strict key-row ancestry supplies source highest-numerical ancestry and the complete intervening key gate. Insertion dominance, extended $G_d$, and fixed-context order give

$$
\tau^{d+1}_{P_g,P_x}(B_{P_g})
\ge (P_x)C^-_x\bigl(A_{g,x}(B_g)\setminus\text{leading column}\bigr)
\ge B_{P_x}.
$$

**Actual/slot.** A slot is not a source position, so $G_d$ cannot be applied directly. Instead use the [first-diagonal lemma](lemmas/first-diagonal.zh-CN.md): BN and $\mathrm{SB}_1,\ldots,\mathrm{SB}_{d-1}$ already imply that a position $g$ with a strict $p_d$ descendant has a second column in its zeroth block whose first $d+1$ coordinates equal those of $g$ plus one. This uses neither of the two highest conditions currently being proved.

After rebasing to the slot $x$, those coordinates of the left block's second column are $x+1$. If the right slot is empty, comparison ends. Otherwise its first internal column's first $d$ coordinates are lexicographically at most the slot's plus one. A strict difference settles the comparison. In the equality case, the source highest numerical parent is represented by this slot. The slot's key height is $c+2$, but its greatest stored binding has height only $c$: a reused key outputs at most $c$, and a fresh definition at most $c+1$. Both are below the slot's own key height, and hence below the left second column's height. The left block is strictly greater.

Thus BN and every target $\mathrm{SB}_j$, $1\le j<r$, hold, without circularly invoking a highest condition to prove itself.

## 6. Why the images are standard BMS terms

A row bound and a raw lexicographic upper bound are insufficient. The extra finite block conditions just proved provide the missing standardness argument.

**Finite coverage lemma.** Suppose a numerically legal $r$-row matrix $N$ satisfies BN and every $\mathrm{SB}_j$. If a same-dimensional numerically legal $H$ satisfies $N<_{\mathrm{lex}}H$, then some finite $m$ satisfies

$$
N\le_{\mathrm{lex}}H[m]<_{\mathrm{lex}}H.\tag{2}
$$

This is the pure-numerical case of [low-branch coverage](source-finite/LOW-COVERAGE.zh-CN.md). If every output lay below $N$, the first difference would occur at the last nonzero reading atom of $H$. In branch zero, BN controls the repeated root blocks. In branch $j$, the unsettled seam and the chosen root share the $j$th parent; $\mathrm{SB}_j$ controls the partially rebased block. If every finite number of copies still stayed below the target block, the [last-hole lemma](source-finite/LAST-HOLE.zh-CN.md) would force the complete rebased block to be strictly smaller than the target block, contradicting that condition. No highest forest branch or model interpretation is used.

Start with a standard $H>N$. Unless equality has been reached, choose the least $m$ satisfying (2) and repeat. This uses only computable finite-column comparison, and coverage guarantees the required $m$. Failure to reach $N$ would give an infinite standard BMS expansion chain, contradicting [Hunter's well-ordering theorem](https://arxiv.org/abs/2307.04606). Therefore $N$ is reached after finitely many steps and is standard.

Only the standard BMS order is used here. The argument does not assume that the raw lexicographic order on nonstandard matrices is well-founded.

## 7. The fixed ceiling and strictness

A standard source term is empty or starts with a zero column. Its second column's numerical vector is at most the all-ones vector. If it is a leaf, the code is already smaller than $U_{d+2}$ at the key row of the second column; a smaller numerical vector decides the comparison earlier.

If the second column is not a leaf, all its numerical coordinates must be one and its complete key is nonempty. Its code starts with

$$
0^{d+2},\quad 1^{d+2},\quad 2^{d+2},\quad(3^d,2,0).
$$

The fourth column, the first forest slot, is strictly smaller than the fourth column $3^{d+2}$ of $U_{d+2}$. Hence, uniformly over standard source terms,

$$
C^-(E)<_{\mathrm{lex}}U_{d+2}.\tag{3}
$$

The frozen short fundamental sequence directly gives $U_{d+2}=B_{d+3}[3]$, so $U_{d+2}$ is standard. It can serve as the covering start in the preceding section for every image. All images are therefore standard. Fixed-entry strict order preservation embeds the entire standard source domain into the standard BMS segment below $U_{d+2}$. Consequently

$$
\lim(\mathrm{BTnSS})\le |U_{d+2}|<|B_{d+3}|=|B_{n+2}|.
$$

The last endpoint is the standard $(n+1)$-row BMS supremum, proving (1). No claim about arbitrary nonstandard $r$-row matrices was needed.

## 8. Paper argument and finite audits

The research implementation was `encodePruned` in `btnss_guard_candidate.cjs`; its ordinary encoder gives the same columns on the finite-invariant source domain. Implementation budgets are not mathematical restrictions on $d$ or term size.

Parent tables, ordering, partial transport, same-key and inserted-key transport, definition heads and cross-leaf gates were separately audited to find errors. Passing finite samples does not prove every dimension or descendant. The universal conclusion rests on the parent-transport arguments, fixed-context induction, exhaustive finite environment cases and standard-domain source invariants above. The rejected two-boundary key reconstruction and whole-row masking shortcuts are not reused.

The [historical receipt](verification.json) records the finite-check scope; the experiment scripts are not redistributed as a runnable test suite. See the [collection guide](README.md) for frozen rule sources, provenance and the distinction between collection validation and mathematical verification.
