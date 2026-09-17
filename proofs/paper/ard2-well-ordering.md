# ARD2 skyline: well-ordering and exact legacy equivalence · [中文版](ard2-well-ordering.zh-CN.md)

2026-09-17. [PDF](ard2-well-ordering.pdf) · [Definition](../../notations/ARD2/definition.md) · [Full legacy proof](ard2-legacy-well-ordering.md) · [New Lean project](../../lean/ARD2/README.md).

Default ARD2 and preserved ARD2-legacy have the same standard order type, indexed fundamental sequences and local counts, not merely the same axiom upper bound. The isomorphism is a paper theorem. Lean independently proves the new rule well-ordered through the subdiagram route in Section 6; it does not yet formalize the whole isomorphism.

## 1. Objects and axioms

Work in $KP_\omega+$“there exists an uncountable ordinal”, with full set induction and the conventions of the [legacy paper](ard2-legacy-well-ordering.md). Use its proved well-foundedness of actual expansion on legal graphs, standard column well-order, and reachability comparability. No power set, choice or new reflection principle is added.

Legacy maximum-root entries satisfy $k,q\le j$, $p<j$, with the maximum root retained per $(k,p)$. Write $E_n$ for old expansion and $F_n$ for the new rule. Let $S$ take a column skyline and $Q$ apply $S$ columnwise, preserving empty columns. Both standard domains are generated from the same singleton-column seeds using their respective rules.

The legacy Lean backend uses complete root atoms. Applying $Q$ directly to those finite atom lists gives the same result as first taking maximum roots per $(k,p)$ and then the skyline.

## 2. Finite skyline algebra

Entry $a$ dominates $e$ when its parent and priority $(k,q)$ are both at least those of $e$, with different entries. The maximal elements of this finite partial order are precisely the skyline records. Every deleted entry is dominated by a retained maximal one, and domination is transitive. Hence

$$ S(S(C))=S(C),\qquad S(S(C)\cup D)=S(C\cup D). $$

A strictly increasing uniform address relabelling preserves both comparisons and therefore commutes with $S$. The old maximum controller under $(k,q,p)$ is retained as the final skyline entry. Thus $G$ and $QG$ have identical controllers, cuts, block lengths and output widths.

These are finite combinatorial facts, not assumptions about the semantic value of arbitrary deleted raw relations.

## 3. Exact seam compression

Fix the old last position $x$, controller $(K,c,R)$, block length $L=x-c$ and block number $b$. First move by $\phi_b$ and denote the moved controller by $(K',c',R')$. The new seam position is $N=x+bL$. Every moved row and root is at most $N$. The old rule consists of truncated old last-column entries together with the entire lower-row package

$$ \{(h,c',N):0\le h<K'\}. $$

**Parents greater than $c'$.** Their old priorities are strictly below the controller, since a tie would select the larger parent. Their roots are unchanged by truncation. Mutual domination persists, so their lower redundant entries remain dominated inside this part. Their skyline is the portion before the controller.

**Parent equal to $c'$.** The greatest surviving priority after truncation and generation is exactly

$$ d=\begin{cases}
(K',R'-1),&R'>0,\\
(K'-1,N),&R'=0<K',\\
\text{absent},&K'=R'=0.
\end{cases} $$

When the root is positive the controller itself supplies the first case, whose row dominates the generated package. When the root is zero the control row disappears and the maximum generated lower row supplies the second case. All other same-parent entries are dominated by this entry.

**Parents smaller than $c'$.** Old priorities are at most the controller's. A surviving same-row entry has root at most $R'-1$. A lower-row entry has row at most $K'-1$ and root at most $N$. Thus whenever $d$ exists, it dominates all these survivors at parent $c'$. If $K'=R'=0$, the old last-column contribution vanishes entirely. This argument uses the common **child bound $N$**, not ARD's stronger bound $q\le p$.

Consequently the old seam skyline is obtained by retaining the moved skyline prefix before the controller, inserting $\delta_N(K',c',R')$, and taking a skyline. If a greater-parent record dominates this predecessor, the final normalization removes it too.

The source cut column is $\phi_{b+1}(C_c)$, not $\phi_b(C_c)$ or unchanged $C_c$. Both its SELF coordinates become $N$. Section 2's union and relabelling identities allow this source to be compressed before merging. Internal source columns use the same relabelling identity. Column by column, therefore,

$$ \boxed{Q(E_nG)=F_n(QG)}\qquad(n\in\mathbb N).\tag{1} $$

Zero indices, empty last columns and the empty graph follow immediately from preserved width and empty columns. Thus (1) holds for **every structurally legal legacy graph**, not merely standard graphs or tested examples. The root-zero test and predecessor must be applied after moving in every block.

## 4. Strict decrease, well-foundedness and standard isomorphism

Every new step strictly lowers skyline column order. The first changed position is the old final column: the controller is removed, and new entries have either its parent and a smaller priority or a strictly smaller source parent. The skyline prefix above the control parent remains unchanged. Further skyline deletion cannot restore the controller. Zero-index and successor steps are proper prefix deletion.

A legal skyline input $H$ can also be read as a legal legacy graph with $QH=H$. If there were an infinite nonzero new expansion path, apply exactly the same indices to legacy $H$. By (1) its compression is the proposed new path, and equal widths prevent premature arrival at zero. This contradicts legacy expansion well-foundedness. Thus expansion on all legal skyline inputs is well-founded.

For standard graphs, (1) and unchanged seeds give

$$ U_{\mathrm{new}}=Q(U_{\mathrm{legacy}}). $$

Any two legacy standard terms are comparable by actual finite reachability, with the direction fixed by column order. If $a<b$, a nonempty path from $b$ to $a$ maps under $Q$ to a nonempty strictly descending new path. Hence $Q(a)<Q(b)$. Compression is injective and strictly order preserving on the standard domain; with the displayed surjectivity, it is an order isomorphism. New standard column order is therefore a well-order.

Outside these domains $Q$ can be many-to-one. This does not assert a well-order on arbitrary legal column lists or identify new raw lists with legacy standard terms. Setting $Q(\mathsf{Top})=\mathsf{Top}$ extends the isomorphism to the two adjoined-top notations.

## 5. Indices, counts and the existing lower bound

Equation (1) preserves the **same index $n$**, without reparameterization. Compression preserves width, full-column prefixes and emptiness, and commutes with truncation. A local step is a positive expansion truncated to the old width, so it also commutes with $Q$. Both local traces first delete the final position at exactly the same step; their local counts agree.

The original paper [ARD below ARD2(1,3)](ard-le-ard2-13.md) uses complete legacy relation packages. Compose that embedding with $Q$ to obtain the same result for the new edition, since

$$ B=\texttt{[][(0,0,1)]}=A_2[1][1],\qquad Q(B)=B. $$

Thus the previous comparison chain survives, but no new whole-system comparison with wY or CWY2 follows.

## 6. Direct semantic route in Lean

The seven new modules define their own predecessor, skyline expansion, seeds, reachable standard domain and column order. They explicitly depend on the old semantic construction in [ARD2-legacy](../../lean/ARD2-legacy/README.md).

On the same valid input, retain strictly lower $(k,q)$ entries from the old last column, add one moved-controller predecessor, merge the source and normalize every appended column. On skyline inputs this filter is exactly removal of the last entry. Each retained record belongs to the corresponding legacy output's complete root set; the single predecessor comes from old ordinary truncation or lower-row generation. Skyline normalization only removes relations. Lean proves equal output widths and columnwise inclusion, then restricts the legacy bounded semantic representation along this inclusion.

This gives strict semantic descent for the actual new expansion. Together with its proved validity, column decrease, fundamental-sequence prefixes and nested seeds, the final results are

```text
OrdinalFormal.ARD2Skyline.valid_step_wellFounded
OrdinalFormal.ARD2Skyline.standard_with_top_strictWellOrder
```

The isomorphism, reflection, accessibility and well-ordering are not unproved caller assumptions. Current certification is recorded in the [project guide](../../lean/ARD2/README.md) and [validation report](../../VALIDATION.md). This is ordinary Lean mathematics, not an internal weak-KP derivation or virtual-machine verification.

## 7. Axiom accounting and regression

The new work uses finite lists, comparisons and finite paths, plus well-founded induction already available from the legacy theorem; it does not increase the paper axiom upper bound. Section 3's universal argument, not test volume, proves the equivalence.

The [Python audit](../../tests/test_ard2.py) compares legacy execution and an independent full-root oracle; the [JS audit](../../tests/ard2_ner.cjs) uses independent atomic rules and accepts Python vectors; the [display audit](../../tests/ard2_display.cjs) checks complete relations, both SELF coordinates and isolated resource failures. Experiments have explicit time, width, state and memory bounds. Unexplored cases are neither passes nor counterexamples.
