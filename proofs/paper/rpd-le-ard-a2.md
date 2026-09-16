# RPD embeds below the fixed ARD term (1,2) · [中文版](rpd-le-ard-a2.zh-CN.md)

2026-09-16. Paper comparison, **not an end-to-end Lean comparison theorem**. [RPD definition](../../notations/RPD/definition.md) · [ARD-legacy definition](../../notations/ARD-legacy/definition.md) · [Skyline equivalence](ard-well-ordering.md) · [Bounded regression](../../tests/rpd_ard_comparison.py).

## 0. Statement and conventions

Let $\alpha_R$ be the order type of finite standard RPD terms, and $U_A$ the finite standard ARD domain. Set

$$B=A_2=\texttt{[][(0,0,0)]}.$$

Its count display is `1,2`. We prove a strict order embedding

$$\Phi:U_R\longrightarrow\{H\in U_A:H<B\},\qquad \alpha_R\le |B|_A.$$

Mapping the RPD external top to $B$ extends the embedding to include top, with image at most $B$. To put even that top strictly below a target term, use $A_3=\texttt{[][(0,0,0)][(1,1,1)]}$, whose count display is `1,2,6` and whose zeroth child is $B$. In particular $\alpha_R<\alpha_A$.

Sections 1–8 use **ARD-legacy's complete-root rule**, not the simplified rule. The [skyline order isomorphism](ard-well-ordering.md) fixes $B$ and transfers the resulting embedding to current ARD. Thus the title and final inequality refer to the new default ARD as well.

The [existing 1Y≤RPD paper argument (Chinese)](../../research/ordinal-comparisons-20260914/archive/ipd-upper-bounds/Y-le-RPD-proof.zh-CN.md) then gives

$$\mathrm{ARD}(1,2)\ge\alpha_{\mathrm{RPD}}\ge\alpha_{1Y}.$$

Here 1Y is the fixed upstream definition used in this repository. Identifying its relevant standard domain with Naruyoko Y follows the accepted research convention, not a new Lean equivalence certificate. Neither cross-notation inequality is claimed Lean-formalized. We use the previously proved standard well-orders and their reachability characterization; equality $|B|_A=\alpha_R$ and comparison with wY are not proved.

## 1. Atoms and priorities

In this proof, a maximum-root triple $(k,p,q)$ abbreviates all atoms $(k,p,u)$ for $0\le u\le q$. Inclusions and unions mean complete root closures. Its child is the column containing it. Control is maximal in $(k,q,p)$; write $a=(k,q)$ for the pair priority. Column lists are descending in $(p,k,q)$ and compared lexicographically.

RPD keeps rows fixed under copying. Legacy ARD moves row addresses and adds a full lower-row package at the control parent. The frozen prefix and saturation below neutralize these differences. The RPD seed

$$S_N=[\varnothing,\{(k,0,0):0\le k\le N\}]$$

and all its descendants have row numbers at most $N$.

## 2. Uniform capture below B

For $t\ge0$, write $B[t]=(D_0,\ldots,D_t)$. Direct expansion gives $D_0=D_1=\varnothing$ (the latter exists only if $t\ge1$), and for $j\ge2$, in maximum-root notation,

$$D_j=\{(j-1,j-1,j-2)\}\cup\{(h,j-1,j-1):0\le h<j-1\}.$$

Thus the fixed two-column term already produces arbitrarily high finite row addresses.

Fix $N$ and put $d=N+1$. The last column of $B[N+2]$ is at $d+1$, with control $(d,d,d-1)$, so its source block has length one. Execute $[1]$ exactly $N+1$ times:

$$H_N=B[N+2][1]^{N+1}=(D_0,\ldots,D_d,L_N\cup D_d),\qquad
L_N=\{(h,d,d):0\le h\le N\}.$$

Each step lowers the control root until row $d$ disappears; the already present lower-row package remains. All $H_N$ are strict standard descendants of $B$. Freeze the prefix

$$P_N=(D_0,\ldots,D_{d-1})=B[N].$$

Translate source column and root addresses by $i\mapsto d+i$, but leave source row $k$ unchanged. The final two columns of $H_N$ cover $S_N$. Column $d$ need not be empty; its extra relations have roots below $d$. They cannot simply be ignored, and the preparatory descent below handles them.

## 3. Coverage and admissibility

For a structurally valid RPD graph $G$ with rows at most $N$, write $H\succeq_d G$ if

$$\operatorname{width}(H)=d+\operatorname{width}(G),\qquad
(k,p,q)\in C_j(G)\Rightarrow(k,d+p,d+q)\in C_{d+j}(H).$$

Extra target edges and the frozen prefix are allowed, but no extra columns inside the data region.

Call $H$ **$N$-admissible** if it is structurally valid, has width at least $d$, and:

1. Its first $d$ columns are $P_N$, and all row addresses are at most $N$.
2. **$V_d$:** an edge at parent $p\ge d$ and row $K$ entails all edges at that parent with row $h<K$ and root $u\le p$.
3. **$F_d$:** for every pair $a=(k,u)$ with $u\ge d$, each vertex's ancestors in the directed graph of $a$-edges form a chain under reachability.

Write $p\prec_a j$ for a nonempty $a$-path from $j$ to $p$. Since edges point left, $F_d$ is equivalent to: whenever $p<c$ are direct $a$-parents of one column, $p\prec_a c$. Induction on column number proves both directions of this equivalence.

$H_N$ is standard and admissible. The only active-parent requirements are in the full package $L_N$, and each nonempty large-root graph has just the final edge to column $d$. Hence $H_N\succeq_d S_N$.

## 4. Fixed-width preparatory descent

For a nonempty last column of $H$, let $T(H)$ be actual $H[1]$ followed by actual $[0]$ deletions restoring the original width. This is a nonempty expansion path, not an additional rewrite rule. With control $(K,c,r)$ its last-column formula is

$$C_x(T(H))=C_c(H)\cup\{(k,p,q)\in C_x(H):(k,q)<(K,r)\}
\cup\{(h,c,u):h<K,\ u\le c\}.$$

The earlier columns are unchanged: movement at the zeroth seam is the identity and every address in $C_c$ lies below $c$.

### 4.1 Termination

At fixed width and row bound there are only finitely many possible last-column atoms. $T$ preserves these bounds and strictly lowers the last-column order: parents above $c$ are unchanged, the control at $c$ disappears, generated rows there are smaller, and source records have smaller parents. Therefore repeated $T$ reaches the empty last column in finitely many steps. No global slow descent needs to be executed for this argument.

### 4.2 Preservation

When the changed column is after the frozen prefix, $T$ preserves the prefix and row bound. It preserves $V_d$: lower rows of retained records pass the same filter, source requirements were already saturated, and the new package is saturated.

Fix $a=(k,u)$ with $u\ge d$, and let $b=(K,r)$.

- If $c<d$, neither the source column nor the new package contains root $u$. The old $a$-parent set is retained as a whole or deleted as a whole.
- If $c\ge d$, saturation makes the new package redundant after filtering. For $a\ge b$ all old $a$-parents disappear, leaving only those of $C_c$, already a chain.
- If $c\ge d$ and $a<b$, the new parents are the union of the old final parents and the parents of $c$. For $u>c$, the latter are empty. For $u\le c$, saturation or control-root closure already made $c$ an old final $a$-parent. All ancestors of $c$ therefore belonged to the old final ancestor chain.

Thus $F_d$ is preserved. Intermediate copied terms implementing $T$ may temporarily have larger row addresses; the bound is asserted only at the restored-width endpoint, whose formula was just proved.

## 5. Copying at an active parent

Suppose the actual control parent satisfies $c\ge d$. Every row $k\le N<d\le c$ is fixed by relocation $\phi_b$. Also $V_d$ puts the full lower-row package at $c$ in the input already. Its lower rows survive the seam filter; moving their maximum root and closing downward gives all roots through $\phi_b(c)$. Therefore the additional ARD package is redundant. The finite formula is now exactly the fixed-row RPD copy formula.

The row bound, prefix and $V_d$ are preserved by inspection. For $F_d$ we need more than formula similarity.

### 5.1 Chain attachment fact

In a finite left-directed graph with chained ancestors, attaching an ancestor chain to a formerly parentless vertex and its descendants preserves chained ancestors. The same holds if the vertex's former ancestors already lie in the attached chain. Induct on vertices from left to right: new ancestors propagate only through that vertex along an existing ancestor chain; every affected chain is extended by the same compatible chain. Inclusion here means path inclusion, not necessarily direct edges.

### 5.2 Fixed-root analysis

Fix $a=(k,u)$ with $u\ge d$ and build output blocks left to right.

If $u<c$, relocation fixes $u$ and each block copies the old $a$-graph. A seam has either no $a$-edges or all moved old-final $a$-parents. In the latter case $k<K$, or $k=K,u<r$, so saturation or root closure ensures $c$ was an old final $a$-parent. The old chain contains $c$, its copied part contains the current block start, and any shared-prefix ancestors belong to the ancestors of $c$. Ancestors already attached to this block start extend that same chain. When attached to the next block start, its inherited prefix ancestors are already included. Apply Section 5.1.

If $u\ge c$, for block $b$ set

$$q_b=\min\{q:\phi_b(q)\ge u\}.$$

Then $q_b\ge c\ge d$. Root closure identifies the source relations with a copy of the old $(k,q_b)$-graph. Its parents are all at least $q_b$, so there are no shared-prefix incoming edges and the source block start is a root. If the seam filter passes, the seam parents are precisely the copied old-final parents at $(k,q_b)$. Their witnessing ancestor paths use only old columns at least $q_b$, never the old last column, and have already been copied into this block. They form a chain. Previously attached ancestors propagate only if this chain passes through the block start, in which case they extend it. Attach the resulting chain to the next source root, using Section 5.1. If the filter fails, no such seam is added. Changes in $q_b$ between blocks, and empty graphs when it is too large, cause no exception.

This proves active-parent copying preserves admissibility for every index.

## 6. Exposing a specified controller

Suppose an admissible $H$ has final edge $e=(K,p,r)$ with $r\ge d$, and put $a=(K,r)$. Repeat $T$ until the actual control is $e$. Before stopping, maintain:

1. A nonempty $a$-path from the last column $x$ to $p$.
2. Every original last-column edge with priority strictly below $a$.
3. Admissibility and the unchanged earlier columns.

If the current control priority is greater than $a$, the filter preserves all these edges and the path. If it equals $a$, let its greatest parent be $c$. By $F_d$, $p$ lies on its ancestor chain, so $p\le c$. For $p=c$ we stop. Otherwise $p\prec_a c$; inheriting $C_c$ preserves a path to $p$, while strictly lower edges survive. The control priority cannot fall below $a$ while this path exists. Section 4 prohibits infinitely many preparatory steps, and the path prohibits the last column becoming empty before exposure. Hence exposure occurs in finitely many steps.

The designated direct edge can temporarily disappear. The invariant is its ancestor path, which is why $F_d$ is essential.

## 7. Simulation of every strict source step

Let $G$ have rows at most $N$, and let admissible standard $H\succeq_d G$. For each strict RPD step $G\to G[n]$, there is a nonempty actual ARD path to an admissible standard $H'\succeq_d G[n]$. Being below $B$ is preserved. The source graph need not be standard for this lemma.

For a zero index or an empty source last column, apply target $[0]$. Coverage, width and the prefix remain correct even if the target last column was not empty.

Otherwise write source control as $(K,c,r)$ and source last position as $x$. Expose its encoded edge

$$e=(K,d+c,d+r)$$

by Section 6, obtaining $\widehat H$. Earlier columns and strictly lower source priorities are still covered. The source may have several parents at its greatest pair priority; do not assume the entire old source column is still covered after exposure.

The target control parent is at least $d$, so Section 5 applies. Both block lengths are $L=x-c$. For source and target movements $\phi_b,\psi_b$,

$$\psi_b(d+i)=d+\phi_b(i),\qquad \psi_b(k)=k\quad(k\le N).$$

Take actual target index $n$ to obtain $H'$, of width $(d+x)+nL=d+\operatorname{width}(G[n])$. Check every type of source output edge:

- **Copied earlier columns:** exposure did not change them; the relocation identity and root closure cover every copy.
- **Strictly lower source priorities:** their encoded edges survived exposure. A lower row retains all moved roots; the same row with lower old root uses the corresponding control-root filter. Every source output root $v$ maps to the allowed target root $d+v$.
- **The source controller:** the exposed target edge produces all required roots $d+v<\psi_b(d+r)=d+\phi_b(r)$, at matching parents and child positions.
- **Other parents at the greatest pair priority:** such an edge is $(K,v,r)$ with $v<c$. Validity gives $r\le v<c$, so movement fixes $r$ and it produces only roots below $r$. If $r=0$ it produces none. If $r>0$, root closure already supplied the strictly lower edge $(K,v,r-1)$, which survived exposure and covers every required output. If $r=c$ there can be no such other parent. No tied parent exceeds $c$, by the definition of control.

This exhausts the source output. Extra target edges do not harm inclusion. Section 5 gives admissibility; all operations used were actual strict target expansions, proving the simulation lemma.

## 8. A history-independent order embedding

For each standard RPD graph define

$$\mathcal C(G)=\{H\in U_A:H<B,\ \exists N\ (H\text{ is }N\text{-admissible and }H\succeq_{N+1}G)\}.$$

This is nonempty: start with $H_N$ covering a seed $S_N$ that generates $G$, and simulate its finite generating path. All endpoints remain standard and below $B$.

The standard ARD order is already a well-order, so set $\Phi(G)=\min\mathcal C(G)$. For a strict source step $G\to G'$, choose an admissibility witness $N$ for $\Phi(G)$. Coverage and the target row bound imply the source row bound needed in Section 7. Simulation gives $H'\in\mathcal C(G')$ with

$$\Phi(G')\le H'<\Phi(G).$$

Distinct standard RPD terms are comparable by nonempty expansion reachability, in exactly their column-order direction. Iterating this inequality along the finite path proves strict order preservation. Linearity gives injectivity and order reflection. All images lie strictly below $B$, proving the theorem.

Given a seed and a generating path, the covering construction is effective, though preparatory descent can be slow. The least-cover definition is a mathematical, history-independent map; this publication does not claim to supply an efficient or computed least-cover translator.

## 9. What the conclusion does not say

It does not prove equality with $B$, an identical count-word translation, index-by-index commutation of $\Phi$ with fundamental sequences, or a wY comparison. Extra edges alone do not prove greater order type: actual strict simulation and minimization inside the known **standard** well-order are indispensable. No raw graph order is presumed well-founded.

## 10. Bounded implementation check

[rpd_ard_comparison.py](../../tests/rpd_ard_comparison.py) directly imports the published RPD and preserved ARD-legacy Python rules. It implements $T$ by actual $[1]$ followed by actual $[0]$, checking strict descent, prefix preservation, full-root coverage, $V_d$ and $F_d$. The run has a 25-second deadline, 2,000 preparatory steps per call, source width at most 10, intermediate target width at most 32, and at most 80 queued states per seed.

The original bounded run checked levels $0,1,2,3$, 275 generated states, 949 standard-source steps and four specially constructed raw exposure cases: 953 simulations, 15,866 preparatory steps, maximum 966 in one preparation, 291 nonunique source-top priorities and seven same-priority/larger-parent detours. Current rerun results are recorded in [VALIDATION](../../VALIDATION.md). These finite checks are regression evidence, not the universal proof in Sections 2–8.

Run from the repository root:

```sh
python -B tests/rpd_ard_comparison.py
```

The ancestor-chain and preparation method is inspired by the earlier 1Y≤RPD argument. The new ingredients here are uniform capture below a **single** ARD term, frozen-prefix closure for moving row addresses, and treatment of nonunique greatest source priorities. The mathematical rules of RPD and ARD-legacy have not been changed.
