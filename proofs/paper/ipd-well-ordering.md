# IPD well-ordering in KP with an uncountable ordinal · [中文版](ipd-well-ordering.zh-CN.md)

2026-09-14. Complete paper proof for the current zero-start IPD, with an ordinary-Lean correspondence. The actual standard-column-order theorem has passed Lean. The weak axiom bound below is a paper metatheoretic argument, not an internally encoded Lean derivation in KP.

Work in the theory

$$
S=KP_\omega+\exists\nu\,\bigl(\nu>\omega\text{ is an ordinal and}
\text{ no set function }\omega\twoheadrightarrow\nu\text{ exists}\bigr).
$$

KP includes full set induction, literal $\Delta_0$-Separation and $\Delta_0$-Collection. We add no power set, full separation, general choice, general collapse of internal well-orders, or large cardinal. The tree-rank construction uses KP alone; the uncountable ordinal is used for diagram representations.

## 1. Fixed definition and main theorem

The objects are those of the zero-start [Python](../../notations/IPD/ipd.py) and [NER](../../notations/IPD/IPD.ne-rewritten.js) implementations, not an earlier candidate. A finite term is a list of finite backward-edge columns. An edge in column j is $(p,(d,t))$, with $p<j$ and natural d. Its alphabet is

$$
X_{p,j}=\{0,\ldots,p\}\cup\{j\},
$$

where j is SELF and the others are ROOTs. At each parent retain only the maximum profile. Define the finite tree levels by

$$
\begin{aligned}
K_0(X)&=X,\\
K_{d+1}(X)&=\{Z\}\cup\{h(t_0,\ldots,t_{k-1}):
h\in K_d(X)\cup\{\mathrm{CAP}\},\ t_i\in K_{d+1}(X)\}.
\end{aligned}
$$

CAP is the greatest head of its level, not a greatest tree. The order at each positive level is LPO with (head, arity) precedence; profiles have the disjoint-sum order $\mathcal P(X)=\sum_{d<\omega}K_d(X)$. Children stay at their level; entering a non-CAP head lowers it.

Columns list parents in decreasing order and compare lexicographically by (parent, profile). Diagrams compare by columns from left to right, with proper prefixes smaller. In contrast, the controller is maximal by **(profile, parent)**.

Let $A_n$ have two columns and just one edge, to parent zero, carrying the minimum of $K_n$. The standard domain Std is the union of the finite expansion-descendant cones of all $A_n$, including seeds and zero. Adjoin an optional greatest TOP with $\mathrm{TOP}[n]=A_n$.

**Theorem.** S proves that an ordinal $\chi$ and a set function $\mu$ on all structurally valid finite IPD diagrams exist such that

$$
\mu(0)=0,\qquad G\ne0\Longrightarrow\mu(G[n])<\mu(G)
\quad(n<\omega). \tag{1}
$$

Consequently strict expansion is well-founded. Every standard descendant cone, Std with its actual column order, and Std with TOP adjoined are well-ordered. Column-order statements use canonical columns, as specified below.

We do not assert global column-order well-ordering on all hand-written valid auxiliary graphs. Expansion well-foundedness there is a different assertion. No comparison with wY, TPD or another notation is proved here.

## 2. Actual ordinal ranks for profiles in KP

[Appendix A](#appendix-a-direct-kp-ranks-for-tree-path-order) proves the following directly: a set signature with a given set ordinal rank has a set ordinal rank for its fixed-arity ground LPO.

We do not first assume LPO well-founded and recurse along it. Let G(t) mean that the whole closed initial segment through t has a canonical ordinal collapse. This is $\Sigma_1$. Induct on the already given ordinal precedence of heads and on finite lexicographic vectors of already existing argument ranks, then on the finite size of a smaller term, to show constructor closure of G. $\Sigma_1$-Collection joins compatible initial-segment ranks. No separation of the class of all G-terms is used.

Treat each actual symbol as (h,k), ranked by $\omega\cdot r(h)+k$, placing CAP after all ordinary heads. Iterate the lemma, collecting canonical finite construction histories, and take the ordinal sum of the levels. For every already ranked alphabet X, KP thus constructs a set map

$$
\rho_X:\mathcal P(X)\longrightarrow\Xi_X,
\qquad u<v\iff\rho_X(u)<\rho_X(v). \tag{2}
$$

All subsequent recursion is on this already constructed ordinal. Neither general internal well-order collapse nor Kruskal as an additional axiom is needed.

### 2.1 Relabelling and finite templates

A strictly increasing alphabet map $\phi$ acts recursively on every ROOT/SELF, preserving Z, CAP, levels, arities and child order. Finite comparison induction gives

$$
u<v\iff\phi(u)<\phi(v). \tag{3}
$$

Each template contains finitely many ROOT variables, a SELF placeholder, Z, CAP and finite-level data. Templates have natural-number codes. Comparing two fixed templates expands into a finite Boolean combination of comparisons of their base variables: recursion either enters a lower-level head or a proper subtree.

When SELF is a common upper endpoint b and all ROOT parameters are below b, those inequalities already determine every ROOT/SELF comparison. Thus b need not be a domain parameter of the model-theoretic structure below.

## 3. Actual lowering is strictly decreasing

Only strict decrease is needed here, not cofinality, index monotonicity, or simulation of another notation.

The internal seeds are

$$
q_{0,b}(p,j)=\begin{cases}p&b=0,\\j&b>0,\end{cases}\qquad
q_{d,b}(p,j)=\begin{cases}Z&b=0,\\\mathrm{CAP}(Z^{b-1})&b>0\end{cases}
\quad(d>0).
$$

At level zero, $\ell_{d,b}$ takes the finite alphabet predecessor, with none below ROOT0. At a positive level Z also returns none. For a nonzero $t=h(a_0,\ldots,a_{k-1})$:

- If h is CAP, the smaller head is $h'=q_{d-1,b}$; otherwise recursively lower the original h, possibly obtaining none.
- For $k>0$, initialize $M=\max(h(),a_0,\ldots,a_{k-1})$; for $k=0$, use Z.
- Smaller symbols are (h,k−1) when $k>0$, and (h',b) if h' exists.
- Recursively lower each nonzero original child, obtaining $u_i$.
- For exactly b+1 rounds, take the maximum of M, the smaller symbols applied to their respective numbers of M copies, and $h(a_0,\ldots,a_{i-1},u_i,M,\ldots,M)$ for every available position.

Recursion enters only original children or the original head, never newly generated terms. Finite induction constructs a single operation in KP.

**Lemma 3.** Whenever internal lowering returns a value, it is strictly below t. At positive levels every nonzero tree returns a same-level value. Whole-profile lowering $L_b$ is likewise strictly decreasing whenever it returns a profile.

**Proof.** Induct on level and original tree structure. Level zero is finite predecessor. Initially $M<t$: children are below their tree, the same-head leaf has smaller arity, and Z is least. If $M<t$ at a round's start, every argument of a smaller-symbol candidate is below t, so the smaller-symbol LPO branch applies. A same-head candidate strictly decreases its first changed argument, while every argument remains below t, so the lexicographic LPO branch applies. A finite maximum preserves the strict bound.

The replacement for CAP is a legal ordinary head and hence below CAP. A lowered ordinary head is smaller by induction. If internal lowering fails at a positive level, $L_b$ uses $(d-1,q_{d-1,b})$, decreasing the level. Only lowering (0,ROOT0) deletes the edge.

The JS pruning retains a subset of these candidates, so decrease also holds directly for it. Exact equality with the all-position algorithm is proved in section 10, not inferred from tests.

## 4. Constructing the finite-demand relation in S + V=L

### 4.1 The uncountable endpoint and uniform enumeration

Take the least uncountable ordinal $\kappa$. Full set induction supplies class minimization for the formula defining uncountability; unrestricted separation on an ordinal is not assumed.

Each $0<\alpha<\kappa$ has a set surjection from $\omega$. $\Delta_0$-Collection collects a set C containing the required witnesses. In V=L, well-order C constructibly and choose its least appropriate witness by bounded selection. This yields an actual set function

$$
\begin{aligned}
e&:\kappa\times\omega\longrightarrow\kappa,\\
e(\alpha,\cdot)&:\omega\twoheadrightarrow\alpha\quad(0<\alpha<\kappa),
\qquad e(0,n)=0. \tag{4}
\end{aligned}
$$

No ambient choice axiom is used. The constructible hierarchy and its well-order are the usual KP constructions; section 9 removes V=L.

Apply section 2 to $X=\kappa+1$, obtaining the set rank $\rho:\mathcal P(X)\to\Xi$. The guard V(t,a,b) says that every base letter of t lies in $(a+1)\cup\{b\}$, with $a<b\le\kappa$. The first part supplies ROOTs and b supplies SELF, even inside nested heads.

### 4.2 Finite requests

Let G be a valid graph of width m, and N a finite endpoint-template family. Each template is (p,$\tau$), with ROOT addresses at most $p<m$. For increasing finite labels f, write $\tau[f,b]$ for ROOT i evaluated as f(i), SELF as b. Set

$$
\operatorname{Inc}_b(f)\iff\omega<f(0)<\cdots<f(m-1)<b,
$$

$$
\operatorname{Rep}(G,f)\iff\operatorname{Inc}_\kappa(f)\land
\bigwedge_{(p,\tau)\in C_j}R(\tau[f,f(j)],f(p),f(j)),
$$

$$
\operatorname{End}_b(N,f)\iff
\bigwedge_{(p,\tau)\in N}R(\tau[f,b],f(p),b),
$$

$$
\operatorname{Adm}_{t,a,b}(N,f)\iff
\bigwedge_{(p,\tau)\in N}(\tau[f,b],f(p))<_{\mathrm{lex}}(t,a). \tag{5}
$$

The comparison is **(profile, parent)**, allowing an equal profile with a smaller parent. Profiles of internal edges of G have no controller upper bound.

Define R(t,a,b) as the guard $\omega<a<b\le\kappa$, V(t,a,b), and the following condition. For every finite G,N, cut $c<m$ and labels f satisfying

$$
\begin{gathered}
\operatorname{Rep}(G,f),\quad\operatorname{Inc}_b(f),\quad f(c)=a,\\
\operatorname{Adm}_{t,a,b}(N,f),\quad\operatorname{End}_b(N,f),
\end{gathered}
$$

there are labels g with

$$
\begin{gathered}
\operatorname{Rep}(G,g),\quad\operatorname{Inc}_a(g),\\
g\restriction c=f\restriction c,\quad\operatorname{End}_a(N,g).
\end{gathered} \tag{FR}
$$

### 4.3 Genuine bounded recursion, not a circular axiom

Recurse lexicographically on $(b,\rho(t),a)$. Put $H=(\kappa+1)\cdot\Xi$ and encode the stage by

$$
H\cdot b+(\kappa+1)\cdot\rho(t)+a<H\cdot(\kappa+1).
$$

The finite-label source $B=(\kappa+1)^{<\omega}$, graph/template codes and profile evaluation graphs are already sets. Given a history, all quantifiers are bounded by these sets, and the next truth value has a bounded definition.

Every query is earlier: internal input edges end below b; output queries end at most at $a<b$; same-endpoint input templates have smaller (profile, parent) by (5). Guards and admissibility are tested before endpoint-history lookup, so an inadmissible request never reads a future entry.

Valid-history checking is bounded. Induction on the given stage ordinal proves uniqueness on overlapping initial segments. Successor stages use $\Delta_0$-Separation; limit stages collect shorter unique compatible histories by $\Sigma_1$-Collection and take their union. This constructs the set relation R, not a power set of all potential histories.

The definition yields FR and **same-parent profile weakening**:

$$
t'\le t,\quad V(t',a,b),\quad R(t,a,b)
\Longrightarrow R(t',a,b). \tag{6}
$$

Every request admissible for t' is admissible for t and has the same required output. There is no cross-parent monotonicity assertion: changing a changes the output bound.

## 5. A countable template structure and elementary heights

For each finite template $\tau$ introduce predicates

$$
\begin{aligned}
R_\tau(\vec q,a,b)&\iff R(\tau[\vec q,\mathrm{SELF}=b],a,b),\\
P_\tau(\vec q,a)&\iff R(\tau[\vec q,\mathrm{SELF}=\kappa],a,\kappa).
\end{aligned}
$$

This is a countable family of finitary predicates. Extend e to a total function by assigning zero at invalid second arguments. Form the set structure

$$
\mathfrak A=(\kappa;<,\omega,e,(R_\tau)_\tau,(P_\tau)_\tau).
$$

**Neither whole trees containing $\kappa$, nor $\Xi$, nor $\rho(t)$ are treated as elements of its domain.**

KP constructs satisfaction for this set structure: formulas and finite assignments have set sources, satisfaction is $\Delta_1$, and $\Delta_1$-Separation gives its graph. Each existential formula then has a least ordinal witness operation with a boundedly defined set graph.

For any $\gamma<\kappa$, close all natural numbers, $\omega$ and $\gamma$ under these witness operations and e. The closure is the range of finite closed-term evaluation in a countable language, with an actual set surjection $\omega\to H_\gamma$. If $0<\alpha\in H_\gamma$, enumeration by e gives $\alpha\subseteq H_\gamma$. Thus the closure is an ordinal $\delta\le\kappa$. Its enumeration excludes $\delta=\kappa$. The witness criterion gives

$$
\max(\omega,\gamma)<\delta<\kappa,\qquad
\mathfrak A\restriction\delta\prec\mathfrak A. \tag{7}
$$

This is an elementary initial segment of one fixed set structure, not universe reflection, a regular-cardinal theorem, general collapse, or countable choice. Section 12 replaces full elementary-substructure machinery with the smaller explicit closure used in Lean.

## 6. Endpoint agreement and initial representations

### 6.1 Endpoint agreement

For $\delta$ as in (7), with ROOT parameters $\vec q\le a<\delta$,

$$
P_\tau(\vec q,a)\iff R_\tau(\vec q,a,\delta). \tag{8}
$$

Induct simultaneously on $(\rho(\tau[\vec q,\delta]),a)$ in the already ranked ordinal product. Replacing SELF=$\delta$ by $\kappa$ while fixing all lower ROOTs is increasing alphabet relabelling; (3) preserves all profile comparisons. Templates representing the same tree remain equal after lifting.

Forward direction: take a request for the right side. Its endpoint profile/parent pairs are smaller. The induction hypothesis changes their endpoint facts to P facts, and lifting preserves admissibility. FR for the left side provides labels below a. Their internal and output-endpoint queries end at most at a and do not change, so the output works for the right side.

Reverse direction: suppose the right side holds and the left side fails. Fix the finite shape G,N,c of a failed request on the left. Existence of the input and absence of an output below a form one finite first-order formula in $\mathfrak A$. The controller-template shape is fixed; its ROOT parameters, a and $\omega$ lie below $\delta$. Admissibility expands into finitely many base comparisons by section 2.1. Neither external $\kappa$ nor the whole controller tree is a parameter. Elementarity gives a counterexample whose labels all lie below $\delta$. By the smaller profile/parent induction hypothesis, its endpoint facts transfer to $\delta$. All candidate outputs were already below $a<\delta$ and query endpoints at most a, so output nonexistence is unchanged. This contradicts FR at $\delta$.

When $a\le\omega$, both sides fail their guards.

### 6.2 Strong supply

For every height $\delta$ satisfying (7),

$$
V(t,\delta,\kappa)\Longrightarrow R(t,\delta,\kappa). \tag{9}
$$

Take an admissible request f with $f(c)=\delta$. Retain only the prefix $u=f\restriction c$ and reflect the existential assertion: G has a representation g with prefix u, and all endpoint P templates hold. The original f is a witness. This assertion **does not fix the new cut to $\delta$, take t or the old post-cut ROOT values as parameters, or impose the old admissibility condition on the output**.

Elementarity supplies g with all labels below $\delta$. Equation (8) changes its P endpoints to $\operatorname{End}_\delta$, yielding FR. The proof permits ROOT=$\delta$ inside the controller tree.

### 6.3 Every finite graph is represented

If $\alpha<\beta$ are elementary heights, first apply (9) at $\alpha$, then (8) at $\beta$. Every legal template with ROOTs at most $\alpha$ and SELF=$\beta$ has the required R fact.

For width m, apply (7) finitely many times to choose increasing heights $\delta_0<\cdots<\delta_{m-1}$. Setting $f(i)=\delta_i$ represents any valid graph of that width. This is finite choice of heights, not collection of an infinite sequence of arbitrarily complex witnesses.

## 7. Connecting the actual block expansion

Let the last column of G be x, the controller parent c, and $L=x-c>0$. Put

$$
\phi_b(i)=\begin{cases}i&i<c,\\i+bL&i\ge c,\end{cases}\qquad
N_b=x+bL,\quad c_b=c+bL.
$$

The actual output $G[n]$ has $N_n$ columns. Seam $b<n$ is at $N_b$; source blocks are relocated copies of $C_c,\ldots,C_{x-1}$. The seam relocates all old last-column edges, lowers the moved controller by $L_b$, then merges with the next source-cut column and normalizes.

Given a representation F of G, put $\beta=F(x)$. At stage b maintain a representation f of the current width-$N_b$ diagram $D_b$, all labels below $\beta$, and these source facts:

1. Every original prefix edge remains represented after relocation by $\phi_b$ and evaluation by f.
2. Every original last-column template remains represented when ROOTs use $\phi_b$ and f, while SELF stays at the **virtual endpoint $\beta$**.

At b=0, $D_0$ is G with its last column deleted, and F supplies both facts.

Let $a=f(c_b)$ and let T be the moved controller profile under these labels. Then R(T,a,$\beta$). The new controller template is first lowered in its destination finite alphabet and only then evaluated by f and SELF=$\beta$. Section 3 and (3) make its semantic value strictly below T; (6) supplies its fact.

All other original last-column templates have smaller (profile, parent) pairs by controller maximality, preserved under relabelling. Their facts are part of the invariant. A deleted controller adds no endpoint template. Hence all actual seam templates are admissible requests under (5). For unnormalized auxiliary graphs, several edges can have the controller parent; the rule lowers all of them. Their old profiles are at most the controller, so the same argument works. Standard notation columns have no such duplicate parents.

Apply FR to **the entire current diagram $D_b$**. It gives g below a, with $g\restriction c_b=f\restriction c_b$. Define

$$
h=g\mathbin{\frown}f[c_b,N_b).
$$

This is increasing and below $\beta$, of length $N_b+L=N_{b+1}$, and

$$
\begin{aligned}
h(\phi_{b+1}(i))&=f(\phi_b(i))\quad(i<x),\\
h(N_b)&=a. \tag{10}
\end{aligned}
$$

Check all new edges:

- Old $D_b$ edges hold under g by FR.
- New source edges have ROOT, SELF, parent and child labels governed by (10), so the source-prefix facts apply. This recursively covers all references inside head trees.
- New seam edges replace virtual SELF=$\beta$ by their real child label a, precisely the $\operatorname{End}_a$ supplied by FR.
- At the overlapping cut column, merging puts together two valid edge families. Maximum-per-parent normalization selects an existing edge; it creates no new profile.
- Next-stage original last-column templates still use virtual SELF=$\beta$. Their ROOT values are preserved by (10), maintaining both source invariants.

Thus every real seam and its following source block are represented below $\beta$. Finite induction on b represents the whole $G[n]$, not merely the local modification to the old last column.

For n=0 or an empty last column, restrict the old representation to the proper prefix. The empty result has rank zero.

## 8. Actual descent rank and the standard column order

Valid finite graph codes form a definable subset E of the natural numbers. One FS evaluation and a finite path have deterministic finite computation records. E, finite paths, reachability and Std are actual sets in KP; no prior termination of infinite expansion is assumed.

In S+V=L put

$$
\mu(0)=0,\qquad
\mu(G)=\min\{f(x):f\in B,\ \operatorname{Rep}(G,f)\}\quad(G\ne0).
$$

Section 6 makes the candidate set nonempty. Its definition is bounded in the already constructed R, B and other set parameters. Bounded separation on $E\times\kappa$ gives the entire graph of $\mu$. Section 7 proves (1).

### 8.1 Three finite column properties

1. $G[0]$ deletes the last column; any column prefix is reachable by finitely many zeroth steps.
2. $G[n]$ is a full-column prefix of $G[n+1]$. The newly added seam starts exactly at $N_n$, and earlier blocks depend on their own b, not the final n.
3. For canonical nonzero G, $G[n]<G$. The first x columns agree. At the first difference, parents greater than c are unchanged, the controller at c is lowered or deleted, and the new source-cut edges have parents below c. A direct last-column deletion is proper-prefix decrease. Canonical means strictly decreasing parents with at most one edge per parent. Seeds and all their descendants satisfy this invariant; the statement is not extended to arbitrary unnormalized edge lists.

Direct calculation also gives $A_{n+1}[1]=A_n$.

### 8.2 From expansion rank to column well-ordering

Induct on $\mu(G)$ to show that any two descendants of G are comparable by reachability. If one is G there is nothing to prove. Otherwise their first steps are $G[i]$ and $G[j]$, say $i\le j$. By the prefix property and zeroth deletion, $G[i]$ is reachable from $G[j]$. Both descendants therefore lie in the smaller-rank cone of $G[j]$, where the induction hypothesis applies.

For canonical cones, nontrivial reachability strictly lowers the actual column order. Since reachability is total there, it agrees with that strict order; $\mu$ is strictly order-preserving on the cone. Seed nesting gives any two standard terms a common seed ancestor, so the same holds on all Std.

The $\mu$-image of a nonempty set subset has a least ordinal; any term attaining it is a column-order least element. We never use dependent choice to manufacture an infinite descending chain. Adjoining one greatest element preserves well-ordering.

## 9. Removing V=L by transferring the rank

Ordinary KP has the constructible inner class L, with the same ordinals and natural numbers, satisfying KP+V=L. For the hierarchy and $\Delta_1$ background see [McKenzie, Theorem 2.8](https://arxiv.org/html/1806.08500v4#S2); for the ordinary-KP inner-model fact, contrasted with Power KP, see [Rathjen's introduction](https://arxiv.org/html/1801.01897v1).

An ordinal $\nu$ uncountable in the ambient universe is also uncountable in L: an L-surjection would still be a surjection outside L. Choose L's least uncountable $\chi\le\nu$ and carry out the construction there, producing an **actual set function $\mu\in L$**.

Finite IPD syntax, normalization, comparison and computation are absolute. The two universes have the same natural numbers, so E and the standard reachable domain agree code by code. The set $\mu$ belongs to the ambient universe too. The statement that the two rank values of an actual step are ordinals, with the first smaller, is absolute. Hence (1) holds in the ambient universe.

Minimize $\mu$ on arbitrary nonempty ambient subsets and reuse section 8. This proves the conclusion in S itself. It is unnecessary for $\chi$ to remain uncountable outside L. We have not transferred merely the assertion that L sees no descending chain.

## 10. Python and NER correspondence

The fixed source SHA-256 values are:

- `ipd.py`: `12D3F08FD38FC51AA78B9972BAE2D5E02FC8EFC09DE085A9B1752880948EBAB1`.
- `IPD.ne-rewritten.js`: `ACC1A1C2AE260DA9BE7D13E14AC17D84A92679F82EFE97AA85CD0E3B072F6011`.

Python considers every nonzero child position. NER retains only the rightmost nonzero non-final position and the final position if nonzero. Here is the exact pruning argument. At each round M bounds every original child. A non-final candidate contains M as a later child. For $i<j<k-1$, the right candidate retains the original $a_i>u_i$ at the first difference. Because it contains M, it is greater than M and hence greater than every child of the left candidate. The same-head lexicographic branch makes the right candidate strictly greater. Thus among non-final candidates only the rightmost is needed. A final-position candidate need not contain M and must be compared separately.

Induction on level, original tree and closure-round number now proves identical maxima at each round. Shared nodes, caches and input run-length abbreviations do not change the tree value. Relocation enters heads and children exactly as in (3) and (10). Maximum-per-parent normalization is covered by sections 7 and 8.

On budget failure NER rejects the evaluation, rather than returning a truncated mathematical term. The theorem concerns the natural-number rule, not hardware guards as extra notation rules. In this IPD script `FS`, `FS_alter` and `FS_short` point to the same FS implementation; no wY conventions are being conflated.

## 11. Axiom ledger and scope

| Construction | What is used | What is not used |
| --- | --- | --- |
| Finite trees, comparison, lowering, copying | Finite sequences, natural induction, $\Delta_1$ computation graphs | Infinite descent search |
| LPO initial-segment ranks and finite levels | Given ordinal induction, full set induction, $\Sigma_1$-Collection | General collapse, separation of bad trees, Kruskal as an extra axiom |
| Finite-demand R | Constructed ordinal stages, $\Delta_0$ rows, compatible history collection | Self-referential reflection axioms, a power set of histories |
| Uniform enumeration | Bounded least selection in V=L, $\Delta_0$-Collection | Ambient choice |
| Elementary heights | Set satisfaction, least witnesses, finite-term closure with enumeration | Universe truth, large-cardinal reflection, regularity assumptions |
| Endpoint agreement and supply | Actual profile-rank induction, finite-formula elementarity | Treating external SELF or the whole controller as a domain parameter |
| Whole-diagram splice | Finite block induction, same-parent weakening, relabelling | Cross-parent monotonicity, checking only the final column |
| Least final labels and standard domain | Bounded separation, ordinal minimization, finite reachability | Assuming all raw graph lexicographic order is well-founded |
| Removing V=L | Inner-class relativization, absoluteness of an actual rank | Transferring only internal absence of descending chains |

The chain runs from trees to the real standard domain. It gives no optimal axiom bound, PTO theorem or strength comparison. Ordinary Lean checks `IPD.standard_wellFounded`, `IPD.standard_total`, and `IPD.term_wellFounded` in [IPDStandardOrder.lean](../../lean/src/IPDStandardOrder.lean). The broader expansion result `IPD.Semantics.valid_step_wellFounded` concerns all structurally valid auxiliary graphs, not their global column order.

The final axiom reports contain only `propext`, `Classical.choice` and `Quot.sound`. They report host-Lean dependencies, **not** an internal certification of the KP upper bound. See the [correspondence audit](ipd-fidelity.md) and [Lean release instructions](../../lean/README.md).

The finite-demand and elementary-height method is inspired by the supplied manuscript *A Short Proof of 1-Y Well-Ordering in KP with omega_1*, identified in the [joint paper's bibliography](well-ordering.md). That private manuscript is not redistributed. This paper reconstructs moving tree templates, (profile, parent) recursion, the actual IPD seam and the direct KP tree rank; it does not assume the manuscript's Y theorem as IPD well-ordering.

## 12. Explicit witness closure matching Lean

Replace the full elementary substructure of sections 5–6 by the following smaller closure. It adds no axioms and requires no full first-order satisfaction relation. This is the construction in `IPDWitnesses`, `IPDEndpointAgreement` and `IPDClosedSupply`.

### 12.1 Two actual families of operations

Fix the set R and finite-label source B from section 4. An input packet is a finite request shape (G,N,c) with its finite label vector. Injectively encode shapes by natural numbers; compare shape codes first, then fixed-length vectors lexicographically. This order has an explicit ordinal rank: an ordinal sum over shape codes, with the corresponding finite powers of $\kappa$ as summands. Every nonempty packet set therefore has a unique least member, without invoking arbitrary internal well-order collapse.

For each coded controller template $\tau$, ROOT parameter vector $\vec q$ and parent a, a Bad packet is an admissible input to $R(\tau[\vec q,\kappa],a,\kappa)$ with no FR output. If such packets exist, take the least one and define $\operatorname{Bad}_{\tau,i}(\vec q,a)$ as its ith label; use zero when no packet exists or i is out of range. Every nonzero value comes from a valid input below $\kappa$.

For a shape (G,N,c) and fixed prefix u of length c, an Ext packet is a representation f of G below $\kappa$ with that prefix and $\operatorname{End}_\kappa(N,f)$. **Do not fix a cut label, controller profile, or admissibility condition.** Select the least such vector and define $\operatorname{Ext}_{G,N,c,i}(u)$ as its ith coordinate, with zero defaults.

These are bounded set definitions in R, B and the finite-syntax sets. The preceding explicit ordinal ranks justify minimization. All operation graphs are obtained by bounded separation on (finite operation codes) × (finite parameter source) × $\kappa$. Semantic profiles are parameters, not an uncountable family of operation symbols.

### 12.2 Closure heights

The operators are the Bad coordinates, Ext coordinates and, for each natural n, $\alpha\mapsto e(\alpha,n)$. This is a countable set. Evaluate finite operation terms with constants $0,\omega,\gamma$, obtaining an actually countable range H. Since H contains $\omega$ and is closed under e, it contains all naturals. Since e enumerates every nonzero $\alpha<\kappa$, H is downward closed.

Every output lies below $\kappa$, so H is an ordinal $\delta\le\kappa$. Its actual enumeration and the uncountability of $\kappa$ give $\delta<\kappa$; the constants give $\omega,\gamma<\delta$. Only finite terms, finite evaluation histories, collection and section 4.1's enumeration are needed, not regularity of $\kappa$.

Thus Bad coordinates lie below $\delta$ whenever their ROOT parameters and a do; Ext coordinates lie below $\delta$ whenever the retained prefix does.

### 12.3 Endpoint agreement and strong supply

Induct again on $(\rho(\tau[\vec q,\delta]),a)$. The forward direction of section 6.1 is unchanged. For the reverse direction, if the $\kappa$ endpoint fails, choose the actual least Bad packet. Closure places all its labels below $\delta$, and the smaller profile/parent induction hypothesis changes its endpoint facts to $\delta$. This contradicts FR at $\delta$, replacing first-order reflection of a counterexample.

For strong supply choose the actual least Ext packet. The old request witnesses existence, and its retained prefix is below the old cut $\delta$. Ext closure yields a representation entirely below $\delta$; endpoint agreement changes $\operatorname{End}_\kappa$ to $\operatorname{End}_\delta$. This replaces existential reflection and still permits ROOT=$\delta$ in the original controller.

Sections 6.3–9 now apply unchanged. The resulting route inside S is: actual bounded R recursion, actual finite witness operations, countable downward closure, endpoint agreement, initial supply, whole-diagram splice, and actual ordinal descent with standard-column well-ordering.

### 12.4 The bounded paper relation and Lean's global relation

For convenience Lean defines R on the same-universe type of all ordinals and finite ordinal profiles, then chooses actual $\omega_1$. The paper fixes $\kappa$ first and recurses in the set $\mathcal P(\kappa+1)$. The two relations agree below $\kappa$: valid input labels are below $b\le\kappa$, output labels below $a<b$, all evaluated ROOT/SELF values stay in $\kappa+1$, and admissible same-endpoint queries are earlier. Recursion uniqueness gives agreement on this restriction.

Lean's global types and ordinary choice therefore do not introduce global truth, an uncountable operation language or stronger universes into the paper. The weak-theory route uses section 4's bounded set histories, section 12.1's bounded operation graphs and section 9's transfer of an actual rank.

## Appendix A. Direct KP ranks for tree path order

This is the independent paper lemma used in section 2. Ordinary Lean checks the corresponding all-tree well-foundedness in `IPDTreeWellFounded.lean`; the KP set-rank construction here is a metatheoretic paper argument, not an encoding of KP itself.

### A.1 Why a direct construction is needed

An earlier approach first used Kruskal for tree well-ordering and then took the order type in ZFC. Those two sentences cannot simply be imported into KP: arbitrary internal well-orders need not have available ordinal collapses there.

Instead we construct a rank for this particular path order. We use full set induction and the $\Sigma_1$-Collection derivable in KP, not a general collapse axiom, $\Sigma_1$-Separation, power set or an uncountable ordinal. KP throughout means $KP_\omega$ with full set induction, not merely set-form Foundation.

### A.2 Finite syntax assumptions

Let F be a set signature with a fixed finite arity ar(f) for each symbol. Suppose a set strictly increasing injection

$$
\lambda:F\longrightarrow\Theta
$$

into an existing ordinal $\Theta$ is given. The signature order is the strict total order induced by $\lambda$. Let T be the set of finite ground terms; an independent least constant Z is allowed.

Use the usual LPO. For $t=f(a_0,\ldots,a_{k-1})$ and $s=g(b_0,\ldots,b_{m-1})$, $t>s$ holds if:

1. Some $a_i\ge s$; or
2. All $b_j<t$ and $\lambda(g)<\lambda(f)$; or
3. All $b_j<t$, g=f, and b is lexicographically smaller than a.

Fixed arity makes the two vectors in the third branch equally long. Z is independently least.

Initially use only finite algebraic facts: strict totality, transitivity, the subterm property and this decomposition. They follow by natural-number induction on sizes of term pairs/triples, without path-order well-foundedness. For standard definitions and finite transitivity arguments see [Schwichtenberg, Rewrite Systems, section 5.4.6](https://www.mathematik.uni-muenchen.de/~schwicht/lectures/rewrite/rw_dump.pdf). Its termination theorem is not a premise of the following rank construction.

Code T by finite shapes with finite F-label lists. KP constructs finite sequences and the set graph of comparison via finite computation records. Comparison and membership tests below are bounded queries to these set parameters.

### A.3 Having a rank is a Sigma-one property

For $t\in T$, put $I_t=\{s\in T:s\le t\}$. Let G(t) assert that there exists a set function $c_t$ with domain exactly $I_t$, ordinal values, and

$$
c_t(u)=\{c_t(v):v\in I_t,\ v<u\}\qquad(u\in I_t). \tag{A1}
$$

Checking a supplied $c_t$ uses only bounded quantifiers: functionality, domain, ordinal values and both inclusions in (A1). Thus G is $\Sigma_1$. **Never first form the set $\{t:G(t)\}$.**

Equation (A1) makes $c_t$ strictly order-preserving. If $c_t$ and $c_s$ both exist, they agree on their common domain: induct on one function's ordinal values; agreement on predecessors gives equality by (A1). The common domain is an initial segment, so no predecessors are omitted.

When G(t) holds, write unambiguously $r(t)=c_t(t)$. Restriction gives G(s) for every $s\le t$. If G(s), G(t) and $s<t$, compatibility gives $r(s)<r(t)$. At this point r is a unique $\Sigma_1$ class function, not a collected global set function.

### A.4 Joining initial-segment ranks

**Lemma A1.** If G(s) holds for every $s<t$, then G(t).

**Proof.** The strict initial segment below t is a set by bounded separation. Apply $\Sigma_1$-Collection to collect witnesses $c_s$ for its members. The collected set may contain extraneous objects; bounded checking retains only genuine (A1) witnesses without losing witnesses for any s.

They agree on overlaps, so their union C is a function on the whole strict initial segment. Its range is a transitive set of ordinals: if $\gamma<C(s)$, (A1) supplies $v<s$ with $C(v)=\gamma$. Thus $\beta=\operatorname{ran}(C)$ is itself an ordinal. Extend C by $t\mapsto\beta$ to obtain $c_t$. With no predecessors the same construction has $C=\varnothing$ and $\beta=0$.

This is not a global well-founded recursion theorem. It joins a term's rank only after its predecessors have ranks. We must still prove that condition for all actual trees.

### A.5 Constructor closure without induction on the target tree order

**Lemma A2.** For each $f\in F$, ranked arguments $a_i$ imply G($f(a_0,\ldots,a_{k-1})$).

First induct on the **given** ordinal $\lambda(f)$, simultaneously over all smaller symbols and their ranked argument tuples. Fix f and $k=\operatorname{ar}(f)$. Then induct lexicographically on

$$
(r(a_0),\ldots,r(a_{k-1})).
$$

For fixed finite k this is k nested full ordinal inductions. Later coordinates may be arbitrarily large; no common set bound on the vector class is required. There is no second induction when k=0.

The rule is uniform in finite k, not merely a metalinguistic repetition. For a definable nonempty class of length-k ordinal vectors, use full set induction's class-minimization consequence to choose the least first coordinate that extends to a member. Retain it and choose the least extendible next coordinate, and so on. Natural induction on the selected prefix length yields a lexicographically least complete vector. Each extendibility formula may have arbitrary quantifiers, permitted by full set induction. There is no infinite collection of these selections and no set of all vectors in that class. Apply this to a counterexample class to obtain uniform finite lexicographic induction.

Fix ranked a and $t=f(a)$. To apply Lemma A1, show G(s) for every $s<t$. **Induct on the finite size of s, not its position in the path order.**

- If s=Z its closed initial segment is a singleton.
- If some $a_i\ge s$, restrict the already existing $c_{a_i}$.
- Otherwise write $s=g(b)$. LPO decomposition gives each $b_j<t$ and either $g<f$, or g=f with b lexicographically below a. Each $b_j$ is a proper subtree of s, so finite-size induction first gives G($b_j$).
  - For $g<f$, apply the outer symbol induction.
  - For g=f, let i be the first differing position. Then $b_j=a_j$ for j<i and $b_i<a_i$. Compatibility of existing ranks gives equality in earlier coordinates and $r(b_i)<r(a_i)$. Later $b_j$ already have ranks too. The entire rank vector decreases lexicographically, so the second induction applies.

All $s<t$ now have ranks; Lemma A1 gives G(t), completing both inductions.

The noncircular points are important. The smaller symbol's arguments are ranked by finite-size induction, not by assuming t ranked. Decrease of an argument's rank uses its already available initial-segment collapse, not a global tree rank. Only at the end is the still-unranked t handled by Collection. No least bad tree or set of all bad trees is assumed.

### A.6 A set rank for all terms

Finite structural induction, using Z and Lemma A2, gives G(t) for every $t\in T$. Apply $\Sigma_1$-Collection over all T, collect the compatible $c_t$, and take their union r. Its range is an ordinal $\Xi$, and

$$
s<t\iff r(s)<r(t).
$$

**Theorem A.** $KP_\omega$ proves that a set signature with an explicit ordinal rank has a set ordinal rank for its fixed-arity ground LPO.

Every nonempty set subset therefore has a least member. Subsequent recursion can first encode into this already constructed ordinal and then use KP ordinal recursion.

### A.7 Applying the theorem to all finite IPD levels

Start with an alphabet X carrying a set ordinal rank and put $K_0(X)=X$. Given $r_d:K_d\to\Xi_d$, add a greatest head CAP. Actual function symbols are (h,k), each with fixed arity k and precedence

$$
\lambda(h,k)=\omega\cdot\widehat r_d(h)+k,
\qquad\widehat r_d(\mathrm{CAP})=\Xi_d.
$$

This is exactly the program's head-then-arity order. Add the independent least Z. Theorem A supplies a set rank for $K_{d+1}(X)$; we have not treated all arities as one unbounded-arity symbol.

Canonical initial-segment collapses are unique. Finite layer constructions and ranks have $\Sigma_1$ finite-history witnesses. Natural induction and $\Sigma_1$-Collection collect all finite histories, giving the sequence $(K_d,\Xi_d,r_d)_{d<\omega}$. The $\Delta_1$ finite-syntax construction graphs and their computation witnesses can be included in these histories; neither full replacement nor unrestricted separation is required.

Ordinal recursion on $\omega$ constructs $S_d=\sum_{i<d}\Xi_i$ and $\Xi=\sum_{d<\omega}\Xi_d$. Then

$$
\mathcal P(X)=\sum_{d<\omega}K_d(X),\qquad
\rho(d,t)=S_d+r_d(t)<\Xi
$$

is a set strictly increasing rank. Different-level zero and leaf terms are not identified. In particular X may be $\kappa+1$: ROOT and SELF become elements of X, while CAP is an extra head at each level. No larger uncountable cardinal is needed.

### A.8 Scope and references

This lemma supplies profile ranks, not whole-IPD well-ordering by itself. The main paper connects finite demands, closure supply, actual seams and the standard order. The final ordinary-Lean theorem is [IPDStandardOrder.lean](../../lean/src/IPDStandardOrder.lean).

For KP's $\Sigma_1$-Collection, $\Delta_1$-Separation and bounded-quantifier closure facts see [McKenzie, Lemmas 2.2–2.3](https://arxiv.org/html/1806.08500v4#S2). We use the version with full set induction. The paper rank lemma has been reviewed within the whole argument; the analogous ordinary-Lean tree well-foundedness is complete, but the weak-theory rank construction is not internally formalized. No IPD definition or expander change was made for this proof.
