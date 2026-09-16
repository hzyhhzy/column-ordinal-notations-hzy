# CWY: compact columns, root stretching and an internal bound · [中文版](definition.zh-CN.md)

Mathematical version: 2026-09-14. Repository edition: 2026-09-17. CWY means *Compact wY*. The source system is **omega-Y weak magma**, not weak-omega-Y. This document packages the existing definition and paper arguments; it does not add a new well-ordering proof.

## 0. Which implementation is included?

The [NER file](wY-CWY.ne-rewritten.js) registers `ω-Y (weak magma) · CWY视图`, ID `omega-y-weak-cwy`. It is the original wY implementation with an additional **CWY compact-list view**, including `[S]`. Select `CWY 紧凑列表` in the equivalent-display menu.

**Its input, comparison, FS, FS_alter and FS_short remain the original wY rules.** In particular, the adapter does not implement the pure-seed index shift of Section 4. It displays the original external top as `[][S]`, but does not thereby give that button the new fundamental sequence of the finite bound B below. For example, the original `(1,3)[0]=(1)` is displayed as `[]`; the mathematical CWY term `[][][S][S]` instead has zeroth term `[][][S]`.

The accompanying [compact_wy.py](compact_wy.py) implements the highest-profile core, and [compact_wy_bound.py](compact_wy_bound.py) implements the **full mathematical version with B and the shifted pure seeds**. They use only the Python standard library and arbitrary-precision integers. The JS snapshot is unchanged. Do not identify these two executable interfaces term by term. The current direct, marker-free successor design is documented separately as [CWY2](../CWY2/definition.md).

## Main conclusions and scope

Let $\alpha$ be the lexicographic order type of the standard wY domain. The mathematical domain $T$ below has

$$\operatorname{otp}(T)=\alpha+1.$$

There is a finite expression B such that wY maps exactly onto the proper initial segment below B. B represents $\alpha$, whereas the order type of the whole domain is $\alpha+1$. This is not a claim of a substantial strength increase.

For each fixed limit expression A, the full canonical string satisfies

$$|\operatorname{str}(A[n])|=O_A(n\log(n+2)).$$

Its zeroth term deletes the last column; consecutive fundamental-sequence terms are whole-column prefixes. Successors also have their predecessor obtained by deletion. Comparison is computable column lexicographic comparison.

The paper transfer assumes the stated finite and well-ordering results of manuscript [W]. Its axiomatic upper bound remains $KP_\omega+\text{there exists an uncountable ordinal}$. This is not a Lean certificate or a fresh independent audit of all of [W].

## 1. Columns and order

An ordinary column is a finite list

```text
[p:(r,u,...);q:(v,...)]
```

A record `(p,W)` consists of a parent-column address and a nondecreasing word of natural-number addresses. Retain just one copy of a repeated initial letter: `(0,0,0,2,2,5)` normalizes to `(0,2,2,5)`. There is at most one record per parent, stored in decreasing parent order. Write the empty ordinary column as `[]`, or O. There is one additional column symbol `[S]`, or S.

The lists are the entire expression: no original integer sequence, history, hidden tree or precomputed descendants are stored. The canonical string writes all columns and decimal addresses explicitly. A displayed `*`, where provided, is merely the current column address.

Words compare by first letter, length, then lexicographically. Records compare by parent address and then word. Parent comparison uses the usual natural-number order, **not its reverse**, despite the decreasing storage order. Ordinary columns compare lexicographically; every ordinary column is below S. Expressions compare lexicographically by columns, with a proper prefix smaller. No expansion or reachability search is used for comparison.

## 2. Highest-profile compression $\Phi$

For an original positive-integer string s starting with 1, draw its canonical wY mountain $M(s)$. Heights are finite Cantor coefficient lists below $\omega^\omega$. For a non-bottom cell e, let j be its column, p its left-foot column, d its least jump dimension, and $P(e)$ the immediate cap of its left foot. Definition 5.4 of [W] gives the normalized profile word

$$I(e)=\begin{cases}
T^*_{d,j}(I(P(e))),&P(e)\text{ exists},\\
T^*_{d,j}((p)),&P(e)\text{ does not exist}.
\end{cases}$$

To compute $T^*$, left-pad by the first letter to at least $d+1$ positions, replace the rightmost d positions by j, then normalize. This recurses strictly leftwards; it does not assume expansion well-foundedness.

In each column retain only the largest profile for each parent p, ordered by decreasing p. The resulting column sequence is $\Phi(s)$:

```text
(1)     -> []
(1,1)   -> [][]
(1,2)   -> [][0:(0)]
(1,3)   -> [][0:(0,1)]
(1,4)   -> [][0:(0,1,1)]
```

### Faithfulness and strict order preservation

Fix a left prefix and decrease the last value a greater than 1 by one. By Lemma 2.3 of [W], delete the last top cell t, keep its lower geometry, and graft the upper tail of its left-foot column. If t has parent p, every newly grafted cell has parent strictly below p. Existing lower profile words stay unchanged; Theorem 5.5 says t's word is strictly greatest in its column.

Consequently the first changed record in decreasing parent order is p: its maximum word decreases, or the record disappears. New records with smaller parents cannot reverse that first difference. Finite induction on the last value, and the fact that drawing a column uses only its left context, give

$$s<_{\rm lex}t\quad\Longleftrightarrow\quad
\Phi(s)<_{\rm collex}\Phi(t).$$

Thus $\Phi$ is injective and preserves complete-column prefixes. These statements concern the canonical image; they do not assert that all freely written profile tables are valid wY encodings.

## 3. A fundamental-sequence algorithm without the original expander

### 3.1 Recover the fixed source geometry

Moving upward in a column, parent addresses do not increase. Each parent therefore occupies one consecutive group, whose last word is the saved maximum. Starting with a bottom point of height 1, process each saved `(p,W)`:

1. If the current top height is H, choose the highest point q in the completed parent column p with height at most H.
2. Find the least d with $h(q)+\omega^d>H$; create a cap of height $H+\omega^d$.
3. Compute its word using the parent-cap recurrence above.
4. Continue in that parent group until the word equals W, then move to the next group.

The parent-cap bound in [W], $h(q)\le H<h(c(q))$, identifies the actual left foot uniquely. On the canonical image, induction on columns, groups and cells reconstructs exactly the source geometry. **No huge bottom values need be recovered.** Only the fixed input mountain is reconstructed, not the whole expanded mountain.

### 3.2 Decrease the last column

Let t be the recovered last top, q its left foot, x the last column and c the column of q. Keep the cells below t, delete t, and graft the complete tail strictly above q in its parent column. In grafted words replace that column's SELF address c by x, keeping the other ROOT addresses fixed. Retain the greatest word per parent to obtain the lowered last column D.

This is the geometric decrement from Lemma 2.3. It is not the earlier, refuted quick word-clipping candidate. The standard regression input `(1,4,15,51)` distinguishes those algorithms.

### 3.3 Copy fixed blocks and relocate addresses

For $G=C_0\cdots C_x$, zero stays zero and an empty last column is deleted. Otherwise c is the parent of the final record and $w=x-c>0$. Compute D and keep the prefix $C_0\cdots C_{x-1}$. For $b=0,\ldots,n-1$, append

$$\tau_b(D),\quad\tau_{b+1}(C_{c+1}),\ldots,\tau_{b+1}(C_{x-1}),$$

where

$$\tau_b(i)=\begin{cases}i,&i<c,\\i+bw,&i\ge c.\end{cases}$$

Move both parent addresses and all word addresses. Each block has w columns; for $w=1$ the internal source list is empty. Call this core operation $H_n$. For $n=0$ it simply deletes the last column.

Proposition 3.6(ii) of [W] identifies both feet of each ordinary copy with the effective images of the source feet. Applying it to the source parent cap gives exact parent-cap correspondence; the root case uses Lemma 6.1. Dimensions are unchanged, so ordinary profile words relocate exactly. Filler cells lie below an ordinary cell with the same parent, and cannot increase that parent's maximum word. Reconstruction Theorem 4.8 then gives

$$H_n(\Phi(s))=\Phi(F_n(s)).$$

The missing-cap and root-spine cases are detailed in [Section 6 of the CWY2 equivalence paper](../../proofs/paper/cwy2-equivalence.md). The conclusion is not inferred from tests or from replacing an inequality by equality.

## 4. Stretch the root and add a finite internal bound

The same-width seed encodings do not form a cofinal prefix chain. Change the representation of the second source entry instead. For $s=(1,m,a_2,\ldots,a_x)$ with compact columns $C_0,\ldots,C_x$, define

$$f(s)=OO\,S^{m-1}\,\phi_m(C_2)\cdots\phi_m(C_x),$$

$$\phi_m(i)=\begin{cases}0,&i=0,\\m+i-1,&i\ge1.\end{cases}$$

Here the power of S means actual repeated columns, not a macro allowed in canonical strings. Set $f(\varnothing)=\varnothing$ and $f((1))=O$.

```text
f(1,1) = [][]
f(1,2) = [][][S]
f(1,3) = [][][S][S]
f(1,4) = [][][S][S][S]
B      = [][S]
```

The number of S columns immediately after OO uniquely recovers $m-1$. Restore the omitted source column $C_1$ from m and invert the address map to recover $\Phi(s)$. Actual tail references must lie in $\{0\}\cup\{m,m+1,\ldots\}$: intermediate synthetic markers are not new source parent columns.

If $m<m'$, after their common root prefix the smaller encoding ends or has an ordinary column, while the larger one still has S. It is therefore smaller. Equal second entries use the same strictly increasing address relabeling, preserving all remaining comparisons. Thus f is injective and strictly order preserving.

The final domain is

$$T=f(\mathrm{Std}_{wY})\cup\{B\}.$$

Its rules are:

- Zero is empty. A nonzero term ending in O is a successor; delete O for its predecessor.
- Every other legal nonzero term is a limit, and every nonzero A has $A[0]$ equal to deletion of its last column.
- $B[n]=f(1,n)=OO S^{n-1}$ for $n\ge1$; $B[0]=O$.
- If f(s) has an actual ordinary tail column, use $f(s)[n]=f(F_n(s))$, calculated via $H_n$.
- For a pure seed $f(1,m)$ with $m>1$, use $f(1,m)[n]=f(F_{n+1}(1,m))$.

The last clause discards the original first fundamental-sequence term; it does not change the represented ordinal. A two-column source has width 1, so $F_{n+1}=L_n$, the long expansion. Its zeroth term is $f(1,m-1)$, exactly deletion of the last S.

Ordinary-tail steps keep the second source entry fixed. Pure-seed expansions all have second entry $m-1$. Each case therefore gives an increasing prefix chain. The new seed steps are old positive-index steps; the omitted old zeroth term `(1)` is still reached by deleting root markers, then the last empty column. Hence the generated standard domain is unchanged up to f.

All nontrivial f-images have O in their second column, while B has S. Thus

$$T_{<B}=f(\mathrm{Std}_{wY}).$$

The sequence of B is `[]`, `[][]`, `[][][S]`, `[][][S][S]`, and so on. It is cofinal because the original two-column seed family is cofinal. B is a finite expression obeying the same prefix requirements, not an exempt external-top symbol.

**Implementation caution.** Root stretching changes physical positions, not the source width. When c is zero, do not replace $w=x-c$ by the stretched physical distance. Unpack to source addresses, expand, then repack. Implicit source column 1 is copied as its ordinary profile column, not as the whole S prefix. This is exactly the convention used by the Python wrapper.

## 5. Full-string length

For fixed G, the source columns, D, maximum number of records K, and maximum word length L are fixed. The output has $x+nw$ columns, and addresses at most $x+nw$. Therefore explicit decimal writing gives

$$|\operatorname{str}(H_n(G))|\le C_G(1+n)\log(n+2).$$

For a fixed tail input the S prefix and extra address offset are constant; for a pure seed all output terms have the fixed second entry $m-1$. Root stretching therefore preserves the bound. B[n] has exactly $n+1$ columns and length $\Theta(n)$.

For example, the original $(1,3)[4]=(1,2,4,8,16)$ has compact core

```text
[][0:(0)][1:(1)][2:(2)][3:(3)]
```

The original nth string requires $\Theta(n^2)$ characters, whereas this complete column list uses $O(n\log n)$. No repetitions are hidden in powers or ellipses. Constants may be large; neither runtime, geometry reconstruction nor a sequence of many expansions is claimed to be soft-linear. Successors have fixed output and do not satisfy a linear-growth lower bound.

## 6. Logical interpretation and well-ordering transfer

The core graph is a finite table of reflection requirements. For each `(p,W)` under a strictly increasing labeling a, require the relation $R(W[a],a(p),a(j))$ of [W]. Its weakening Lemma 5.7 makes the greatest word for a given parent imply every smaller word of that parent; conversely the greatest word is realized by an actual cell. Thus the core and the original mountain have **the same representation sets**, and the same minimum last labels, not merely an inequality of ranks.

The main theorem of [W] supplies a set-valued rank $\rho:E\to\chi$ in $KP_\omega$ with an uncountable ordinal. Assign f(s) the rank $\rho(s)$ using its unpacked finite table, and assign B the rank $\chi$. Ordinary steps descend by Theorem 6.4; shifted seed steps are still original steps; all terms below B have rank below $\chi$.

Expansion descent alone does not prove that arbitrary table lexicographic order is a well-order. Use in addition the proved order embedding f and the standard-domain lexicographic well-ordering result of [W, Section 6.1]. This proves the well-ordering of the **specified domain T**, not all parsed tables.

On that standard domain, [W] identifies smaller terms with finite nonempty descent. Together with its fundamental-sequence covering result, this supplies cofinality below limits and the actual immediate predecessor at an empty last column. The original seeds supply cofinality below B. The exact denoted ordinal is the order type of the initial segment; the auxiliary minimum-label rank is not asserted to equal that ordinal.

The standard domain is effectively enumerable and has computable comparison. Its infinite, duplicate-free effective enumeration yields a recursive presentation of the well-order. Each term therefore denotes a recursive ordinal. The parser in this release checks only finite structural conditions: it is not a standard-membership decision procedure.

All extra coding and constructions are finite recursions and set definitions. No new axiom beyond the paper's upper bound is required for the transfer. No optimal-strength or proof-theoretic ordinal equality is asserted.

## 7. Implementation status and safeguards

The Python core reconstructs source geometry and grafts the real upper tail. The earlier fast `compressed_core` decrement failed on the standard input `(1,4,15,51)` and is not shipped as a formal expander. Time, node, output and word-length limits must raise an explicit resource error, not return a truncated term or decide nontermination. Successful parsing is not a certificate of canonical or standard membership.

Historical cross-checks recorded 450 core FS operations, 189 bounded-wrapper FS operations, 84 decrements, 512 prefixes, 360 comparisons, 254 format round trips and 7 guard checks without skips. A further 426 conservative JS versus BigInt-source transitions passed. These are historical implementation diagnostics, not the proof and not a claim that this packaging run reran those exact tests. Current release checks are recorded in [VALIDATION](../../VALIDATION.md).

There is **no CWY Lean certificate**. The original seven-system Lean audit is not enlarged by adding this directory.

## 8. Usage and references

The NER compact view is display-only: paste original wY numeric strings into that adapter, not compact tables. Its numeric core retains JavaScript Number semantics; published comparisons are restricted to safe-integer cases. The Python core uses exact arbitrary-precision integers.

Python example, run in this directory:

```python
import compact_wy_bound as cwy
a = cwy.boundary()
print(cwy.format_expr(a))
print(cwy.format_expr(cwy.fs(a, 3)))
```

[W] is the user-supplied manuscript *Well-foundedness of the Weak-Magma omega-Y System in KP with an Uncountable Ordinal*, supplied as `omega-Y-Weak-Magma-KP.pdf`. This release uses its finite geometry, reconstruction, profile-word and standard-domain well-ordering results; the private source PDF is not redistributed. See [SOURCES](../../SOURCES.md) for code provenance and licensing boundaries.

The [CWY2 equivalence paper](../../proofs/paper/cwy2-equivalence.md) contains the detailed profile-order and exact-copy arguments shared with this representation. The transfer above remains a paper result dependent on [W], not a new full audit or machine formalization of that manuscript.
