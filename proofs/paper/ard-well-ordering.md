# ARD skyline: well-ordering and exact legacy equivalence · [中文版](ard-well-ordering.zh-CN.md)

2026-09-16. [Definition](../../notations/ARD/definition.md) · [Legacy proof](ard-legacy-well-ordering.md) · [New Lean project](../../lean/ARD/README.md) · [RPD lower bound](rpd-le-ard-a2.md).

This paper replaces the default ARD proof entry. The former paper and all its implementation/proof sources are retained under **ARD-legacy**. The new notation has the same standard order type, not merely the same known upper bound. Sections 1–5 give a direct proof of the new rule's well-ordering using the legacy finite-demand semantics. Sections 6–8 give the paper-only exact correspondence. The new Lean proof follows the first route; it does not assume the correspondence.

## 1. Theory, domain and notation

Work in $KP_\omega+$ “there exists an uncountable ordinal”, with full set induction and the conventions of the [legacy paper](ard-legacy-well-ordering.md). No stronger reflection, choice or power-set principle is added. Its finite-demand relation, initial representations and bounded-splice theorem are used as proved lemmas, not new axioms.

Write $F_n$ for the new expansion, $E_n$ for legacy expansion and $S$ for skyline normalization. A triple is $(k,p,q)$; all standard inputs have $k,q\le p<j$ in column $j$. The indexed control priority is $(k,q,p)$; the column comparison key is $(p,k,q)$. In a skyline column, decreasing parents and strictly increasing pairs $(k,q)$ make its last record the control. The strict lower-priority filter is exactly deletion of that last record.

The finite standard domain is generated from the singleton-column seeds $A_n$ by finitely many $F_n$ operations, as in the definition. The external top has children $A_n$. No accessibility assumption occurs in this definition. We never assert that the column order on all structurally legal graphs is well-founded.

## 2. A finite subdiagram lemma

For every input satisfying legacy validity $k<j$, $q\le p<j$, use the equivalent general small rule: choose the maximum controller, retain strictly lower $(k,q)$ records at a seam, add the single predecessor of the moved controller, and take skylines of appended columns. This agrees with the definition on skyline inputs.

**Lemma.** $F_n(G)$ and $E_n(G)$ have the same number of columns, and every triple of the former occurs at the same column in the full-root representation of the latter.

Both rules use the same controller, cut $c$, length $L=x-c$, and $n$ appended blocks. The untouched prefixes coincide. A moved source triple is included in legacy source normalization. Skyline normalization only removes supplied records.

For a seam, let the moved control be $(K',c',R')$.

- A retained old record has $k<K$, or $k=K$ and $q<R$. Strictly increasing relocation preserves this inequality. Its moved maximum root satisfies the legacy ordinary-seam filter.
- If $R'>0$, the predecessor $(K',c',R'-1)$ is among the controller's own ordinary-seam roots.
- If $R'=0<K'$, the predecessor $(K'-1,c',c')$ is in the legacy generated lower-row package.
- If $R'=K'=0$, nothing is added.

Taking a skyline cannot invalidate inclusion. This proves the lemma column by column, including index zero and empty-last-column cases. It does **not** say that a new standard graph is literally a legacy standard graph.

## 3. Transfer of bounded representations

The legacy representation gives increasing labels $f(0),\ldots,f(m-1)$ in its domain and a finite-demand relation for every stored triple. It is downward closed under deleting triples at fixed column positions: the same labels still satisfy every remaining requirement.

The legacy bounded-splice theorem applies to **every legacy-valid graph**, not just root-closed or legacy-standard ones. Given a representation of nonempty $G$, it represents $E_n(G)$ by labels strictly below the former last label $f(m-1)$. By Section 2, restricting those relations represents $F_n(G)$ with the same bound. New validity is likewise inherited from validity of $E_n(G)$.

The legacy initial-supply theorem gives a representation of each finite valid graph. Induct on its last ordinal label, treating the empty graph separately. Every strict $F_n$ successor is accessible because its new last label is smaller. Thus every valid input has well-founded strict expansion. The identity $0[n]=0$ is excluded from the strict step relation.

This argument uses exactly the legacy semantic construction inside the stated weak theory. The extra operations—finite lists, domination tests, filtering, aligned inclusion and finite recursion—need no additional set-theoretic principle.

## 4. Strict column decrease

At index zero or an empty last column, the output is a proper column prefix. Otherwise examine the first new column, at the old final position; the relocation there is the identity. It consists of a skyline of:

1. old last-column records of strictly lower control priority;
2. the controller's single predecessor;
3. records of the cut column, whose parents are strictly below the control parent.

The controller is absent. Every record new to the old last column has smaller column key $(p,k,q)$ than the controller: this follows from its smaller parent in case 3, and smaller row or root at the same parent in case 2. Old retained records need not all lie below the controller in column order; that is not required.

For two strictly descending finite lists, deleting a pivot while adding only new elements smaller than that pivot strictly lowers their lexicographic comparison. Proof: cancel the common initial segment; if the first difference is above the pivot it is a deletion, and otherwise the pivot is missing on the new side while all possible new first elements are smaller. Apply this finite lemma after skyline sorting. Thus every strict expansion lowers the actual column comparator. Normalization preserves sortedness; seeds are sorted.

## 5. From expansion to the standard well-order

The first $n$ appended blocks of $F_{n+1}(G)$ are exactly $F_n(G)$, so fundamental-sequence children form a complete-column prefix chain. Any prefix is reachable by repeated index-zero deletion. Hence any two children are comparable by actual reachability (the child-join property). Also $A_{n+1}[0]=A_n$.

Well-founded induction on strict expansion, using child-join, makes every seed's descendant cone linearly ordered by reachability. Strict column decrease identifies its direction with column comparison. The nested seeds therefore give a total standard order. An infinite descending standard column chain, starting below some $A_n$, would stay inside that seed cone and yield an infinite strict expansion descent, contradicting Section 3. Equivalently apply the legacy/shared prefix-order lemma, whose hypotheses have all just been proved for $F$.

Adjoining the one external maximum preserves well-ordering. This proves the stated result for both finite standard diagrams and standard terms with top.

## 6. Strong guard and skyline algebra

Every legacy standard graph satisfies $k\le p$. The seeds do; deletion preserves it; simultaneous monotone relocation of row and parent preserves it; lowering roots does not affect it; a generated row $h<\phi(K)\le\phi(c)$ is also no later than its parent. Normalization only adds smaller roots or removes duplicates.

On this stronger raw domain define $Q(G)$ by applying $S$ to each column. Domination means another record has no smaller parent and no smaller pair $(k,q)$, with at least one strict comparison. Finite domination is transitive, and each deleted record is dominated by a retained maximal record. Consequently

$$
S(S(C))=S(C),\qquad S(S(C)\cup D)=S(C\cup D).
$$

Strictly increasing simultaneous relocation commutes with $S$, since it preserves both parent comparison and pair comparison. The control survives $S$ and is its last record. These are finite combinatorial facts, not assertions about ordinal values of arbitrary raw graphs.

## 7. Exact indexed commutation

**Theorem.** On all strongly guarded legacy raw graphs,

$$Q(E_n(G))=F_n(Q(G)).$$

Deletion is immediate. In a nonempty-last-column case, fix a seam and write its moved controller as $(K',c',R')$. The old controller was $(K,c,R)$.

Parents larger than $c$ have pair strictly smaller than $(K,R)$ (a tied larger parent would have been chosen). Their maximum records survive the old filter unchanged; domination among them survives too.

At parent $c'$, the greatest surviving pair is precisely the rectangular predecessor of $(K',R')$: if $R'>0$ its row wins over every generated lower row; if $R'=0<K'$ the largest generated row wins; if both vanish no record remains at that parent. All lower records there are dominated by this predecessor.

An old parent smaller than $c$ is fixed by relocation. If its row equals the control row, all retained roots are smaller than $R'$; if its row is lower, its root is at most its parent, hence below $c'$. Its surviving records are therefore dominated by the control predecessor whenever that exists. If no predecessor exists, all old last-column records are removed. Old dominated records at larger parents also remain dominated by a surviving larger-parent record or by this predecessor. This accounts for the full old last column, not just its skyline.

Thus the old seam's skyline is the skyline of the moved noncontrol skyline records plus the single predecessor. Merge the source cut column and use the union identity of Section 6. The interior copied columns use relocation commutation. Every output position agrees, proving the theorem.

The test $R'>0$ must be made **after** movement: an old zero root can become positive when the cut is zero. Moving an already decremented controller is a different, incorrect rule.

## 8. Standard isomorphism, counts and scope

The image of the legacy standard domain under $Q$ is exactly the new standard domain, by indexed commutation and the equal skyline seeds. Any two distinct legacy standard terms are joined, in the decreasing direction, by a nonempty actual expansion path (the prefix-order theorem). Its $Q$-image is a strictly decreasing new path by Section 4. The two images cannot coincide, and the direction is preserved. Surjectivity was already proved. Thus $Q$ is a standard order isomorphism, including the adjoined top.

It also preserves width and truncation, and commutes with fixed-width local reduction. Local column counts and every indexed fundamental sequence agree. It is not injective on arbitrary raw inputs, and equality of numerical counts alone was not used to prove the isomorphism.

The [new Lean final theorem](../../lean/ARD/src/ARDSkylineFinal.lean) proves Sections 2–5 for the executable finite small rule, with ordinary Lean axioms only. The full $Q$ isomorphism and the [RPD comparison](rpd-le-ard-a2.md) are **paper proofs**, not end-to-end Lean comparison certificates. The formal proof does not encode derivability in KP, and it does not verify a JS/Python compiler. Bounded implementation tests are documented separately in [VALIDATION](../../VALIDATION.md). No comparison with wY is established here.
