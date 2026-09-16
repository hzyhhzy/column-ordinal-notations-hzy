# ARD embeds below the fixed ARD2 term (1,3) · [中文版](ard-le-ard2-13.zh-CN.md)

2026-09-16. Paper comparison, **not yet Lean-formalized**. No notation rule is changed. The accompanying bounded tests check finite instances; they do not replace the universal arguments below.

## 0. Statement and versions

Let $U_A,U_2$ be the finite standard domains of ARD and ARD2, with order types $\alpha_A,\alpha_2$. Neither order type includes the external top.

In ARD2 set

$$B=\texttt{[][(0,0,1)]}=A_2[1][1].$$

Its count sequence is $(1,3)$. We construct a strict order embedding

$$\boxed{\Phi:U_A\hookrightarrow (U_2)_{<B},\qquad
\alpha_A\le |B|_{\mathrm{ARD2}}<\alpha_2.}$$

Thus the entire **ARD order type is strictly smaller than ARD2**. A reverse embedding of the entire standard domain is impossible. We do not prove $\alpha_A=|B|$, that the image is an initial segment, count preservation, or indexed fundamental-sequence commutation.

We first work with [ARD-legacy](../../notations/ARD-legacy/definition.md), whose complete-root relation permits inclusion arguments. The [skyline equivalence theorem](ard-well-ordering.md) transfers the result to current ARD; their standard order types agree.

The target uses the [current ARD2 rule](../../notations/ARD2/definition.md). In particular, a new lower-row package has maximum root equal to the **new seam itself**, not the parent-bound package of legacy ARD.

We use the previously proved standard well-orders and the characterization: one standard term is strictly smaller than another exactly when it is a nonempty finite expansion descendant. Finite tests are not substitutes for these facts. No weak object theory has been encoded in Lean for this comparison.

## 1. Triples, complete roots, and the source bound

A compressed group $(k,p,q)$ in column $j$ denotes parent $p$, row anchor $k$, and all roots $0\le u\le q$. Pair priority is lexicographic $(k,q)$; the actual controller chooses the largest parent when priorities tie.

ARD2 requires $k,q\le j$ and $p<j$. Every standard legacy ARD term satisfies the stronger condition

$$k,q\le p<j.\tag{S}$$

The source seeds satisfy (S). Simultaneous increasing address transport, root truncation, and new packages with $h<\phi(K)\le\phi(c)$ and root $\phi(c)$ preserve it. Source-column inheritance preserves it as well. Thus (S) holds throughout the source standard domain.

Write $H\succeq G$ if the widths agree and, for every source group $(k,p,q)\in C_j(G)$, the same $(k,p)$ in $C_j(H)$ has maximum root at least $q$. This is complete-root inclusion, not comparison of counts or equality of graphs.

## 2. The threshold ancestor-chain invariant

Fix $a=(k,u)$ and put $d=\max(k,u)$. Define the leftward threshold graph $E_a(H)$ by

$$j\longrightarrow p
\quad\Longleftrightarrow\quad
p\ge d\ \land\
\exists (h,p,q)\in C_j(H)\ ((h,q)\ge_{\rm lex}(k,u)).\tag{F1}$$

This is not the exact-row-$k$ graph: **all higher rows count**, subject to the parent being at least both threshold coordinates. That distinction handles the lower-row packages produced by higher controllers.

Say $H$ satisfies $F$ if the ancestors of each vertex form a chain under reachability in every $E_a(H)$. Equivalently, any two direct parents $p<c$ of a vertex are connected by a nonempty leftward path from $c$ to $p$. Write $p\prec_a c$ for this path.

We repeatedly use four finite-graph facts:

1. Raising the parent floor from $d$ to $t\ge d$ preserves chain ancestry. A leftward path between retained parents never goes below its smaller endpoint.
2. Attaching an ancestor chain to a root only extends that same chain in its descendants; it creates no branching.
3. If the attachment vertex already has ancestors, the same conclusion holds provided the attached chain contains its previous ancestor chain.
4. Deleting the rightmost column preserves the property.

These follow by induction on columns and require no ordinal comparison.

**Lemma 2.1. All standard ARD2 diagrams satisfy $F$.**

Sections 3 and 4 prove closure under the actual operations. Each seed has only adjacent-parent edges, so every threshold graph starts as a union of chains.

## 3. Fixed-width local steps preserve F

For nonempty final column, define $T(H)$ as the actual $H[1]$ followed by actual $[0]$ deletions until the old width is restored. Let the old last index be $x$ and the controller $(K,c,r)$, with priority $b=(K,r)$.

The new final column is the root-normalized union of:

1. all old final-column atoms of priority strictly below $b$;
2. $(h,c,x)$ for $h<K$;
3. $C_c$, with row SELF $c$ and root SELF $c$ rebound to $x$.

Earlier columns do not change. For fixed width there are finitely many legal final columns, and $T$ strictly decreases their column order. Hence it cannot continue forever without emptying that column. This does not iterate the whole graph's fundamental sequence to zero.

Fix $a=(k,u)$ and $d=\max(k,u)$.

- If $c<d$, neither the source column nor the new package contributes an $E_a$ edge. An old eligible edge cannot be removed at top priority: its parent would be at least $d>c$, contradicting the maximal-parent controller. Lower-priority atoms remain. This threshold graph is unchanged.
- If $c\ge d$, source SELF rebinding does not change the threshold test for source parents at least $d$. For $c>d$, SELF is already above the threshold; for $c=d$, all source parents are below the floor.
- Still with $c\ge d$, if $b\le a$, neither the retained old part nor the lower-row package contributes an $E_a$ edge. Only the ancestor chain inherited from $C_c$ remains.
- If $b>a$, $c$ was an old direct $E_a$ parent. Retained parents, the possibly added $c$, and the ancestors of $C_c$ all lie on the old final vertex's single ancestor chain. The finite-graph facts apply.

Thus $T$ preserves $F$.

## 4. The entire fundamental sequence preserves F

Only a nonempty last column and positive index require proof. Let the cut be $c$, the old last index $x$, and $L=x-c$. Block $b$ uses

$$\phi_b(i)=\begin{cases}i&i<c,\\i+bL&i\ge c.\end{cases}$$

Source columns are $C_c,\ldots,C_{x-1}$; ordinary seam records and the new lower-row package lie at $N_b=x+bL$. The next source block also places its first column at $N_b$. These must be merged, including source SELF rebinding.

Fix target threshold $a=(k,u)$ and $d=\max(k,u)$. Define

$$\lambda_b(v)=\min\{i:\phi_b(i)\ge v\}.$$

If $k$ is in the image of $\phi_b$, set

$$a_b=(\lambda_b(k),\lambda_b(u));$$

otherwise set $a_b=(\lambda_b(k),0)$. Put $t_b=\lambda_b(d)$; always $t_b\ge\max(a_b)$.

For each transported source group **before any seam root truncation**, coordinate comparison gives

$$\phi_b(p)\ge d\ \land\
(\phi_b(h),\phi_b(q))\ge a
\quad\Longleftrightarrow\quad
p\ge t_b\ \land\ (h,q)\ge a_b.\tag{F2}$$

When $k$ is outside the image, no transported row equals it, so row comparison alone suffices and the root threshold becomes zero. This branch is essential for the address gaps inserted by copying. The parent floor remains $t_b$; it must not be reset.

By $F$ and the raised-parent-floor fact, each intrinsic source-block threshold graph has chain ancestry. Ordinary seam records only lower priorities, so their parents form a subset of the old final column's parents at the threshold in (F2).

A new lower-row package contributes a threshold edge exactly when

$$k<\phi_b(K),\qquad d\le\phi_b(c).\tag{F3}$$

Then the transported controller itself was above threshold with eligible parent. Thus $c$ was an old direct parent in the graph of (F2), and the package parent $\phi_b(c)$ co-chains with the ordinary seam parents.

### 4.1 The case d≥c: no edges into the shared prefix

All shared-prefix parents $p<c\le d$ are excluded. A source block's first column comes from $C_c$, whose parents are all below $c$ and remain fixed. It is therefore an intrinsic root, regardless of SELF transport.

The seam parents' original counterparts form a chain. When the new package contributes, (F3) places its parent on the same chain. Witness paths between these parents use only old source columns, not the old last column; they have already been copied into the current block. A previous seam may have added ancestors at its first column, but this only extends the same chain through that root.

Attach the seam chain to the next source block's parentless first column. The finite-graph facts preserve chain ancestry. This works block by block even though $a_b,t_b$ may vary: each block uses its own intrinsic source threshold graph, not a falsely uniform inverse threshold.

### 4.2 The case d<c: fixed threshold and shared-prefix ancestors

Here $k,u<c$, so the threshold is fixed across all blocks. Shared-prefix columns and the source first column's prefix ancestors remain unchanged.

If an ordinary seam or package contributes at this threshold, the old controller priority is strictly above $a$. Moreover, the seam contains a threshold edge to the current block's first column $\phi_b(c)$. The controller's truncated-root predecessor supplies it when still above threshold; if the control root is zero and its row higher, the lower-row package supplies it. The maximal priority of that predecessor or package dominates every other seam record. Thus another seam edge cannot survive without a threshold edge at the control parent.

The old final column's ancestor chain contains $c$ and hence the entire old prefix ancestor chain of $C_c$. Copying preserves that chain. Earlier attachments only extend it at the current block's first column. Merging it with the next $C_c$ copy's old prefix ancestors therefore creates no fork.

If no ordinary seam or package contributes, only the copied $C_c$ prefix ancestor chain remains.

This completes induction over blocks and proves preservation under every actual fundamental sequence. Lemma 2.1 follows.

## 5. Exposing an arbitrary safe control demand

**Lemma 5.1.** Suppose a legal target $H$ satisfies $F$ and its final column contains the root-atom demand

$$e=(K,p,R),\qquad K,R\le p.$$

After finitely many $T$ steps its actual maximal controller is exactly $e$. Preparation fixes the earlier columns and preserves every original final-column atom of priority strictly below $a=(K,R)$.

**Proof.** Until exposure, maintain a nonempty $E_a$ path from the final column to $p$. Initially the demanded edge supplies it. Let the current controller be $(H,c,r)$ with priority $b$. The first edge of the maintained path reaches threshold, so $b\ge a$.

- If $c<p$, the path's first parent is at least $p>c$, and its edge priority is strictly below $b$ by maximal-parent control. That first edge survives, and the rest of the path is in the fixed prefix.
- If $c>p$, the controller is also an $E_a$ edge because $c\ge p\ge\max(a)$. By $F$, $p$ is an $E_a$ ancestor of $c$. Inheriting $C_c$ restores a path to $p$; SELF rebinding cannot lower its safe threshold tests.
- If $c=p$ and $b>a$, either $H=K$ and $r>R$, so truncation retains $e$, or $H>K$, so the row-$K$ package at parent $p$, extending to the final column, contains $e$.
- If $c=p$ and $b=a$, the exact controller has been exposed; stop.

Section 3 preserves $F$. Since every control priority is at least $a$, all original atoms strictly below $a$ survive each truncation. Finite-state strict local descent forbids infinite preparation, while the path forbids premature emptying. Exposure must occur. ∎

Inheritance of source SELF can raise the control priority during preparation. The argument does **not** assume that priority decreases; the strictly decreasing measure is the finite final-column order.

## 6. Simulating an actual ARD step by target descendants

Let $G$ satisfy (S), let $H$ satisfy $F$, and suppose $H\succeq G$.

**Lemma 6.1.** For each strict source step $G\to G[n]$, there is a nonempty actual ARD2 path

$$H\to_2^+ H',\qquad H'\succeq G[n],$$

with $H'$ still satisfying $F$. If $H$ is standard and below $B$, so is $H'$.

For a source column-deletion step, execute target $[0]$. Otherwise let the source controller be $(K,c,R)$. By (S) it is a safe demand. Lemma 5.1 exposes it as the target controller, giving $\widehat H$. Then use the **same index** $n$ in the target.

The widths, cuts, block lengths and address maps now agree. Preparation preserved the prefix, so target source copies cover all source copies. In the source column $C_c$, every row and root is strictly below $c$. The target's additional SELF rebinding therefore does not damage the covered part.

Strictly lower-priority source atoms survived preparation and undergo the same threshold truncation and transport. The lower-row packages have the same rows and parents, but the target roots extend to the new seam, covering the source package whose roots end at the transported parent.

One case needs separate treatment. The source's maximal priority may also occur at a parent $v<c$, whose direct edge could disappear during preparation. Source legality gives $K,R\le v<c$, so these coordinates are fixed by transport at the cut. That source seam edge can produce only roots $u<R$. If $R=0$, it produces none. If $R>0$, its originally lower-priority atom $(K,v,R-1)$ survived all preparation and covers the entire output. The controller parent's own truncated output comes from the exposed controller itself.

This accounts for every source output relation, including tied priorities at different parents. Section 4 preserves $F$ through the actual target expansion. Preparation and the final expansion are real strict descendant steps, proving the lemma.

## 7. Uniform seed supply below the fixed B

The target $B=A_2[1][1]$ is standard with count sequence $(1,3)$. For $m\ge1$ set

$$H_m=B[m-1].$$

Substitution in the actual ARD2 rule gives exactly $m$ columns, first column empty, and for $1\le j<m$,

$$C_j(H_m)=\{(j-1,j-1,j-1)\}
\cup\{(h,j-1,j):0\le h<j-1\}.\tag{Seed}$$

Thus $H_m\succeq A_m^{\rm ARD}$ and every $H_m<B$. Zero covers the zero seed. Sections 2-4 supply $F$ for all these targets.

Iterating Lemma 6.1 along any finite source generation history proves: **every finite standard ARD term has a standard ARD2 cover strictly below this one fixed $B$.** Seed coverage alone would not imply this; the uniform step simulation is essential.

## 8. A history-independent order embedding

Define

$$\mathcal C(G)=\{H\in U_2:H<B,\ H\succeq G\},\qquad
\Phi(G)=\min_{<_2}\mathcal C(G).$$

Section 7 makes the set nonempty. Target well-ordering supplies its minimum, and standardness supplies $F$ for every member.

For a strict source step $G\to G'$, start Lemma 6.1 from the actual minimum $\Phi(G)$. It produces $H'\in\mathcal C(G')$ with $H'<\Phi(G)$, hence

$$\Phi(G')\le H'<\Phi(G).$$

Strict source standard column order is precisely nonempty finite expansion reachability. Composing along a path gives strict order preservation, which between linear orders also gives injectivity and order reflection. All images are below $B$. Finally transfer through the new/legacy ARD standard-domain isomorphism.

If the source external top is included, map it to $B$. Even this source-with-top embeds strictly below target $A_2$, since $B<A_2$.

The target can additionally be restricted to the no-row-SELF fragment. The bound $B$ satisfies $k\le p$, and simultaneous transport, root truncation, and new rows $h<\phi(K)\le\phi(c)$ preserve it. Thus the embedding uses full-context roots, but not all the freedom of row SELF. This structural observation assigns no extra order type to the remaining fragment.

## 9. Regression evidence and scope

The [threshold-forest test](../../tests/ard_ard2_forest.py) uses the official ARD2 Python definition. The original structural run checked 1,200 arbitrary small legal graphs, 694 satisfying $F$, and all 2,776 expansions of those graphs preserved $F$. It also checked 3,500 standard graphs and 10,280 steps. A separate experimental skyline identity was checked in that research run; the present proof **does not depend on it**, and it is not part of the published forest regression.

The [simulation regression](../../tests/ard_ard2_comparison.py) starts from actual descendants of the fixed $B=(1,3)$ covering ARD seeds. An initial run passed 1,500 state pairs and 5,516 simulations, using 360 preparation steps in total and at most 4 in one simulation. It also checked the local formula against actual $[1]$ followed by actual column deletions.

A larger run, with width bound 16 and an actual-path and $F$ check at every preparation step, inspected 7,188 pairs, 25,709 simulations and 2,141 preparation steps in 25 seconds; the longest preparation had 55 steps. There were also 16,093 budget/skipped cases and 13,054 unprocessed queue entries. These are **unknown**, not successful checks.

The tests guard against transcription mistakes; they are not the basis of the universal proof in Sections 2-8. Explicit time, queue, width and preparation bounds apply. No whole-graph fixed-index descent-to-zero search is used.

**wY means omega-Y / weak magma. This paper proves no whole-domain inequality between wY and ARD or ARD2.** It settles the ARD-versus-ARD2 direction only. A common axiom upper bound, count growth, or the failure of a particular encoding does not determine the other pairs.
