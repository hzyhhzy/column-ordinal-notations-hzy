# ARD2-legacy: well-ordering of full-context anchored diagrams · [中文版](ard2-legacy-well-ordering.zh-CN.md)

2026-09-14. [PDF](ard2-legacy-well-ordering.pdf) · [definition](../../notations/ARD2-legacy/definition.md) · [Python](../../notations/ARD2-legacy/ard2.py) · [NER](../../notations/ARD2-legacy/ARD2-legacy.ne-rewritten.js) · [ordinary Lean](../../lean/ARD2-legacy/src/ARD2Final.lean).

ARD2 is the full-context variant of ARD: both row anchors and roots may refer to their own column, while parents remain strictly earlier. This paper proves the actual finite expansion rule, not that ARD2 exceeds ARD or is at least as strong as IPD. Software resource guards are not mathematical rules. The weak-theory paper argument and ordinary Lean kernel verification are separate deliverables.

## 1. Axioms, syntax and theorem

Use the classical set theory

$$
S=KP_\omega+\text{“there exists an uncountable ordinal”}.
$$

KP includes Extensionality, Empty Set, Pairing, Union, Infinity, $\Delta_0$-Separation, $\Delta_0$-Collection and full Set Induction. Uncountable means greater than $\omega$ with no set-function surjection from $\omega$ onto the ordinal. No Power Set, full Separation or Collection, Choice, universe-reflection or large-cardinal axiom is added.

Column $j$ of a finite graph $G=(C_0,\ldots,C_{m-1})$ contains compressed entries

$$
(k,p,q),\qquad k\le j,\quad q\le j,\quad p<j.
\tag{1}
$$

All coordinates are natural numbers. An entry denotes every root atom $(k,t,p,j)$ with $t\le q$. For each $(k,p)$ retain only the maximum root; ignore duplicate relations but retain empty columns. Sort entries decreasingly by $(p,k,q)$, and compare both columns and column strings lexicographically, with a proper prefix smaller. The same comparison results from explicitly listing root atoms in decreasing $(p,k,t)$ order.

The seed $A_n$ has $n$ columns: $C_0=\varnothing$ and $C_j=\{(j,j-1,j)\}$ for $j>0$. Let $D(H)$ contain $H$ and its finite-expansion descendants, ignoring the $0\to0$ self-loop. The standard domain and top are

$$
U=\bigcup_{n<\omega}D(A_n),\qquad \mathsf{Top}[n]=A_n.
\tag{2}
$$

**Theorem.** In $S$, there is an actual ordinal-valued set function $\mu$ on all structurally legal finite graphs, strictly decreasing at every expansion of a nonempty graph, including index zero. The specified column order is a well-order on $U$, and remains one after adjoining the greatest external top.

Well-ordering includes a least element for every nonempty set subset, not just the absence of computable descending chains. Column order on all legal graphs is not a well-order; for example,

$$
[\varnothing]^{r+1}[(0,0,0)]>
[\varnothing]^{r+2}[(0,0,0)]>\cdots.
$$

This is not an expansion chain. Constructors check (1), not standardness of arbitrary inputs.

## 2. Actual expansion and finite structural lemmas

Set $0[n]=0$. A nonempty graph loses its last column at index zero or whenever that column is empty. Otherwise let $x=m-1$, select the largest last-column entry $(k,c,r)$ by $(k,q,p)$, and put

$$
\ell=x-c>0,\qquad N_b=x+b\ell,\qquad c_b=c+b\ell,
\qquad
\phi_b(i)=\begin{cases}i&i<c,\\ i+b\ell&i\ge c.\end{cases}
\tag{3}
$$

For $n>0$, the output has $x+n\ell$ columns. Form the following union, take root closure and normalize:

1. For $b=0,\ldots,n$, copy $G\restriction x$, moving the row, maximum root, parent and child by $\phi_b$.
2. For $b<n$, form a seam at $N_b$. An old last-column entry $(h,p,q)$ with $h<k$ keeps its moved root; at $h=k$ its maximum root becomes $\min(\phi_b(q),\phi_b(r)-1)$, with negative roots omitted; higher rows are omitted.
3. In that seam also insert every $(h,c_b,N_b)$ with $h<\phi_b(k)$.

Copies overlap before the cut, and the first column of the new source block merges with the seam. The maximum root in the third clause is the seam itself, not the control parent. The definition never calls expansion on its output.

**Lemma 2.1.** Expansion preserves legality, leaves all columns before the old last one unchanged, and makes $G[n]$ a complete-column prefix of $G[n+1]$.

Strict increase of $\phi_b$ preserves (1), including relocation of SELF with its child. A generated row is strictly below the seam, its maximum root equals the seam, and its parent is earlier. References in a column before the cut do not exceed that column, so they are fixed. Increasing the index starts the additional seam and source block immediately after the previous output; no existing column is rewritten. Deletion and zero cases are immediate.

**Lemma 2.2.** If $G\ne0$, then $G[n]<G$.

It suffices to inspect the old last position $x$. Old entries with parent greater than $c$ are unchanged: at the same row, control maximality forces their roots below $r$. The maximum root $r$ at parent $c$ and row $k$ decreases or disappears. Generated entries have lower rows, and every parent of source column $C_c$ is below $c$. Even when that source column has both a SELF row and a SELF root, rebinding them to $x$ leaves its parent below $c$, so it cannot restore the first difference. Parent-first column order therefore decreases strictly.

These structural properties alone do not prove well-ordering. We next construct an independent expansion rank.

## 3. Weak-set-theoretic preliminaries

Work temporarily in $S+V=L$, with $\kappa$ the least uncountable ordinal. Use the set constructions in [Sections 3, 5.1 and 8 of the ARD paper](ard-well-ordering.md), whose relevant content is made explicit here:

- For each $0<\alpha<\kappa$, select the first surjection in the constructible well-order of a collected witness set, obtaining a uniform set function $e(\alpha,\cdot):\omega\twoheadrightarrow\alpha$. Totalize it by zero on other inputs.
- Every actual set function $v:\omega\to\kappa$ has a common strict bound below $\kappa$. Otherwise $e$ and natural-number pairing give a surjection $\omega\twoheadrightarrow\kappa$.
- For a fixed set structure with domain $\kappa$ in a finite or countable language, satisfaction and the finitary Skolem operations selecting the least ordinal witnesses form sets. Closing $\omega\cup\{\omega,\gamma\}$ under these operations and $e$ produces a countable ordinal $\delta$ with $\max(\omega,\gamma)<\delta<\kappa$, and an elementary initial segment of the structure.

The last clause reflects a set structure, not the set-theoretic universe. Countability comes from an actual enumeration of finite closed terms, not countable Choice. The $\Sigma_1$-Collection, $\Delta_1$-Separation and ordinal recursion available in ordinary KP suffice for these constructions. First obtain natural-number decoding tables for finite graphs, templates, paths and coordinate operations. Bounded formulas below query these existing tables; arbitrary untreated arithmetic formulas are not simply called $\Delta_0$ in the pure set language.

## 4. Finite demands with two SELF coordinates

Let $B=(\kappa+1)^{<\omega}$ be the set of finite label tuples. A representation of a width-$m$ graph uses a strictly increasing tuple $f$, all of whose labels exceed $\omega$ and are below $\kappa$, with

$$
\operatorname{Rep}(G,f)\iff
\operatorname{Inc}(f)\land
\bigwedge_{(h,t,p,j)\in G}R(f(h),f(t),f(p),f(j)).
\tag{4}
$$

SELF in internal column $j$ is the ordinary index $j$, evaluated at $f(j)$. This is distinct from the virtual-endpoint marker defined next.

A width-$m$ endpoint template $N$ is a finite list of triples $(h,t,p)$ satisfying $h,t\le m$ and $p<m$. Index $m$ marks template SELF. For $f$ entirely below endpoint $b$, define

$$
\widehat f_b(i)=\begin{cases}f(i)&i<m,\\ b&i=m,\end{cases}
\qquad
\operatorname{End}_b(N,f)=
\bigwedge_N R(\widehat f_b(h),\widehat f_b(t),f(p),b).
\tag{5}
$$

Admissibility uses only the row and root pair. It has neither an extra parent stage nor ARD's former requirement that the root precede the cut:

$$
\operatorname{Adm}^{b}_{K,\theta}(N,f)\iff
\bigwedge_N(\widehat f_b(h),\widehat f_b(t))<_{\rm lex}(K,\theta).
\tag{6}
$$

The assertion $FR_{K,\theta}(a,b)$ says: for every legal finite graph $G$, template $N$, cut $c<m$ and tuple $f\in B$, if $\operatorname{Rep}(G,f)$, $f[m]\subset b$, $f(c)=a$, (6) and $\operatorname{End}_b(N,f)$ hold, then some $g\in B$ satisfies

$$
\operatorname{Rep}(G,g),\quad g[m]\subset a,\quad
g\restriction c=f\restriction c,\quad \operatorname{End}_a(N,g).
\tag{7}
$$

The output need not satisfy the old admissibility test again. Ordinary rows and roots read the new labels $g$, whereas template SELF rebinds to $a$. An ordinary input address whose value happens to equal $a$ must not thereby be reclassified as SELF.

Define

$$
R(K,\theta,a,b)\iff
K\le b\le\kappa\ \land\ \theta\le b\ \land\ \omega<a<b
\ \land\ FR_{K,\theta}(a,b).
\tag{8}
$$

### 4.1 Causal recursion and set existence

Recurse lexicographically on $(b,K,\theta)$. Internal input relations have right endpoint below $b$. Output graphs and templates have right endpoint at most $a<b$. Input endpoint templates only read earlier pairs $(K,\theta)$ by (6). Reject invalid guards and inadmissible inputs before querying endpoint relations, so no same-stage query occurs.

For instance, put $M=\kappa+1$ and encode stages by $M^2b+MK+\theta<M^3$. Obtain stage-code and projection tables as sets first. Given a history, bounded Separation on $\kappa+1$ supplies all parent parameters $a$ at the current stage; other quantifiers are bounded by $\omega$, $B$ or existing finite decoding tables. History validity is bounded and uniqueness follows by induction. At limits collect the already existing shorter histories and take their union, rather than forming a power set of possible histories. Thus (8) defines a set relation.

### 4.2 Two weakening properties

Inclusion of admissible demands directly gives

$$
\eta\le\theta,\ R(K,\theta,a,b)\Longrightarrow R(K,\eta,a,b),
\tag{9}
$$

$$
H<K,\ \eta\le b,\ R(K,\theta,a,b)\Longrightarrow R(H,\eta,a,b).
\tag{10}
$$

The root in (10) may reset to the whole endpoint $b$, not just parent $a$. Every demand allowed by a lower-row control has row at most $H<K$, so the original control permits it regardless of its root. This makes no assertion of monotonicity across different parents.

## 5. Four top slices, agreement and initial representations

Complete the recursion defining $R$ first, then define four set predicates:

$$
P_{00}(K,T,a)=R(K,T,a,\kappa),\qquad
P_{10}(T,a)=R(\kappa,T,a,\kappa),
$$

$$
P_{01}(K,a)=R(K,\kappa,a,\kappa),\qquad
P_{11}(a)=R(\kappa,\kappa,a,\kappa).
\tag{11}
$$

Parameters not marked SELF are below $\kappa$. Take the fixed structure

$$
\mathcal A=(\kappa;<,R\restriction\kappa,P_{00},P_{10},P_{01},P_{11},e,\omega).
$$

This does not add an out-of-domain constant $\kappa$: the four $P$ predicates are actual relations of different arities. Section 3 supplies arbitrarily high $\delta<\kappa$ with $\mathcal A\restriction\delta\prec\mathcal A$.

### 5.1 Pointed endpoint agreement

Let $\iota_\delta:\delta+1\to\kappa+1$ fix every $u<\delta$ and send $\delta$ to $\kappa$. For $u,v\le\delta$ and $a<\delta$, prove

$$
R(\iota_\delta(u),\iota_\delta(v),a,\kappa)
\quad\Longleftrightarrow\quad R(u,v,a,\delta).
\tag{12}
$$

Induct on the actual lexicographic well-order $(\delta+1)^2$, considering all $a$ simultaneously. If $a\le\omega$, both sides are false. One cannot finish all ordinary-coordinate cases before processing SELF: a higher ordinary row can already permit a lower row's SELF root.

Forwards, take an admissible input below $\delta$. Every endpoint demand has a pointed row-root pair strictly below $(u,v)$, so the induction hypothesis changes its endpoint from $\delta$ to $\kappa$. Since $\iota_\delta$ is strictly increasing and ordinary labels are below $\delta$, admissibility is preserved. Apply the left-hand $FR$ to obtain (7). Outputs are entirely below $a$ and read the same relation $R$, giving the required right-hand output.

Conversely, suppose the right side holds and the left fails. Fix the graph, template and cut of a finite bad request. Expand label tuples into finitely many variables, expressing input endpoint relations by the appropriate predicate in (11), selected by the two SELF flags. Controls are likewise ordinary parameters or SELF flags; admissibility splits into ordinary ordinal comparisons, truth or falsity, without an out-of-domain parameter $\kappa$. Candidate outputs in the no-output assertion are all below $a$, and query only the common $R$ with right endpoint at most $a$.

The bad input tuple is existentially quantified, not held as parameters. All ordinary parameters of this finite bad-request formula lie below $\delta$. Elementarity therefore gives a bad input entirely in $\delta$. Its admissible endpoint pairs are still strictly earlier. The induction hypothesis changes them to relations aimed at $\delta$, contradicting the right-hand $FR$. This proves all four SELF cases of (12).

### 5.2 Strong endpoint supply

For the same $\delta$,

$$
R(K,\theta,\delta,\kappa)\qquad(K,\theta\le\kappa).
\tag{13}
$$

Take any admissible input $G,N,c,f$ with $f(c)=\delta$. Fix only the prefix $f\restriction c$. Reflect the finite existential assertion that strictly increasing labels $z$ represent the internal graph $G$, retain that prefix, and satisfy all endpoint templates aimed at $\kappa$. Express endpoint relations using the four $P$ predicates. The old tuple $f$ witnesses its truth.

The formula does not fix control parameters $K,\theta$, does not require $z_c=\delta$, and does not ask the output to satisfy old admissibility. Elementarity supplies $z$ entirely below $\delta$. Apply (12) to each template, evaluating ordinary coordinates by the new $z$ and SELF by $\delta$, to obtain $\operatorname{End}_\delta(N,z)$. This is exactly the required output. In particular, (13) allows ordinary controls above the parent height.

### 5.3 Representing every legal graph

Choose increasing elementary heights $\delta_0<\cdots<\delta_{m-1}$ and set $f(j)=\delta_j$. For an atom $(h,t,p,j)$, select the top slice in (11) according to the flags $h=j$ and $t=j$. Use strong supply at parent height $\delta_p$, then (12) at child height $\delta_j$, to obtain

$$
R(\delta_h,\delta_t,\delta_p,\delta_j).
\tag{14}
$$

For example, a double-SELF atom first uses $P_{11}(\delta_p)$, then gives $R(\delta_j,\delta_j,\delta_p,\delta_j)$. Ordinary-coordinate agreement cannot be substituted at the equality boundary. A root after its parent causes no problem because (13) does not require $\theta\le\delta_p$. Thus every legal finite graph has a representation; the empty tuple handles zero.

## 6. Staged splicing with two kinds of SELF

**Lemma.** If a nonempty graph $G$ has a representation with last label $\beta$, every $G[n]$ has a representation whose labels are all strictly below $\beta$.

Deletion restricts the old representation. Otherwise use (3). Set $D_0=G\restriction x$; obtain $D_{b+1}$ from $D_b$ by appending one length-$\ell$ source block and merging seam $b$ into its first column. Then $D_n=G[n]$.

Inductively maintain a width-$N_b$ labeling $f$: it represents $D_b$ entirely below $\beta$, preserves the four-coordinate source relation for each original source maximum-root entry, and preserves a relation aimed at the fixed virtual endpoint $\beta$ for every original last-column maximum-root entry. Define

$$
v_b(i)=\begin{cases}f(\phi_b(i))&i<x,\\ \beta&i=x.\end{cases}
$$

The virtual last-column relation is $R(v_b(h),v_b(q),v_b(p),\beta)$. Both original last-column SELF coordinates read $\beta$, not the nonexistent array element $f(N_b)$. Put $K=v_b(k)$, $\theta=v_b(r)$ and $a=f(c_b)$. The control supplies $R(K,\theta,a,\beta)$.

### 6.1 The actual seam is an admissible demand

Make all seam root atoms into a width-$N_b$ endpoint template, where index $N_b$ marks SELF:

- Retained lower-row entries follow from the virtual relations and root weakening. Their row is strictly below $K$; their root may be SELF.
- Roots at the control row are truncated strictly below $\phi_b(r)$, so their labels are below $\theta$. If the control root is SELF, all truncated roots are ordinary addresses; otherwise truncation still gives the strict inequality. Roots need not precede the cut.
- A generated entry has $h<\phi_b(k)$ and maximum root $N_b$. By (10) its virtual maximum-root relation is $R(f(h),\beta,a,\beta)$; root weakening supplies the smaller roots. All these requests are admissible because their row is lower.

Parents remain ordinary addresses. Apply the control's $FR$ to the entire graph $D_b$, obtaining $g$ with

$$
\operatorname{Rep}(D_b,g),\quad g[N_b]\subset a,\quad
g\restriction c_b=f\restriction c_b,\quad \operatorname{End}_a(N,g).
\tag{15}
$$

### 6.2 Reattaching the source block

Define the label string

$$
h=g\mathbin{\frown}f[c_b,N_b).
\tag{16}
$$

It is strictly increasing, entirely below $\beta$, and satisfies $h(N_b)=a$. For every $i<x$ the key identity is

$$
h(\phi_{b+1}(i))=f(\phi_b(i)).
\tag{17}
$$

For $i<c$ use the fixed prefix; for $i\ge c$ use the appended tail. The identity covers rows, roots, parents and source children, not merely ordinary parent pointers.

Now exhaust the output relations. Every old graph coordinate is at most its child, hence is evaluated by $g$ and justified by (15). New source maximum-root entries are transported by (17). Equation (9) fills the new intermediate roots skipped by the moving map. Actual seam entries come from $\operatorname{End}_a$, with both template SELF coordinates evaluated at $a=h(N_b)$.

Source column $C_c$ can also have two SELF coordinates. Its next copy makes them the new first column itself, again labeled $a=f(c_b)$; its parent remains in the fixed prefix. Thus source relations and the merged seam are compatible. Keeping a source SELF bound to the old cut index would be incorrect.

Virtual original last-column SELF continues to read the fixed $\beta$. Its ordinary coordinates are preserved by (17), so all virtual and source relations remain available at the next stage. These are different uses from rebinding the actual seam to $a$, not conflicting assignments. Induction to $b=n$ proves the splice lemma.

## 7. An actual descent rank and the standard well-order

Let $Q\subseteq\omega$ be the uniquely normalized legal finite graph codes. Once decoding tables, $R$ and $B$ are fixed, existence of a representation is bounded over existing sets. Define

$$
\mu(0)=0,\qquad
\mu(G)=\min\{\beta<\kappa:\exists f\in B\,
 [\operatorname{Rep}(G,f)\land f(|G|-1)=\beta]\}\quad(G\ne0).
\tag{18}
$$

Initial representation makes the candidate set nonempty. A single bounded Separation on $Q\times\kappa$ gives the whole function graph; there is no extra unbounded selection of a representation for each graph. Nonempty representations have labels greater than $\omega$. Applying Section 6 to a representation attaining the minimum last label gives

$$
G\ne0\Longrightarrow\mu(G[n])<\mu(G).
\tag{19}
$$

Only now connect rank with column order. By induction on $\mu(H)$, any two members of $D(H)$ are comparable by finite reachability. If their paths start at $H[i]$ and $H[j]$, both first steps are prefixes of $H[\max(i,j)]$, hence obtainable from it by index-zero deletions. The two graphs lie in this lower-rank descendant cone, where the induction hypothesis applies.

Every step also strictly decreases column order by Lemma 2.2. Thus within a common cone,

$$
V<W\Longrightarrow V\in D(W)\setminus\{W\}
\Longrightarrow\mu(V)<\mu(W).
\tag{20}
$$

Since $A_{n+1}[0]=A_n$, any two standard graphs share a seed ancestor. Hence $\mu\restriction U$ is strictly order-preserving. The rank image of every nonempty set subset $X\subseteq U$ exists by bounded Separation; its least value and preimage give the least element of $X$. Mapping the external top to $\kappa$ preserves strict order as well.

Neither accessibility nor representability is hidden in the standard-domain definition. The argument does not use the false unconditional assertion that every increasing union of well-orders is a well-order.

## 8. Removing V=L and the formal verification boundary

The constructible inner class $L$ of ordinary KP satisfies the same KP and has the same ordinals and natural numbers. For the level-construction and Collection ledger see [Section 8 of the ARD paper](ard-well-ordering.md). An ordinal uncountable in the ambient universe remains uncountable in $L$, because an $L$-surjection would also be an ambient surjection. The internal construction therefore gives an ordinal $\chi$ and an actual set function $\mu:Q\to\chi$.

Finite syntax, normalization, expansion and finite paths agree code by code between the ambient universe and $L$. Ordinal comparison is absolute, so the same function still satisfies (19) externally. Redo Section 7 in the ambient universe to obtain least elements even for standard-domain subsets not belonging to $L$. What transfers is an actual rank, not just the assertion that $L$ regards the order as well-founded. There is no requirement that $\chi$ remain uncountable externally.

Ordinary Lean constructs unconditional initial representations, staged descent and standard column well-ordering for the actual finite rule. The semantic backend uses mathlib's $\omega_1$ and classical choice, together with actual least-bad-request and least-extension witness closures. It does not encode the syntax, proof system or a complete derivation of $S$ inside Lean. In particular, the KP satisfaction and constructible-universe arguments above are paper arguments, not object-theory Lean modules. The final theorems and reproducible verification status are recorded in the [Lean instructions](../../lean/README.md) and [validation record](../../VALIDATION.md).

Finite program tests do not replace this proof, and ordinary Lean is not line-by-line verification of a Python or JavaScript virtual machine. This paper proves neither that ARD is an initial segment of ARD2, nor that ARD2 embeds into IPD, nor any relative order-type inequality or optimality of the axiom bound.
