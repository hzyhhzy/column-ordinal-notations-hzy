# ARD: Well-Ordering in Weak Set Theory · [中文版](ard-well-ordering.zh-CN.md)

2026-09-13. ARD means Anchored Row Diagrams.

[PDF](ard-well-ordering.pdf) · [definition](../../notations/ARD/definition.md) · [NER arc-diagram expander](../../notations/ARD/ARD-arcs.ne-rewritten.js) · [Python](../../notations/ARD/ard.py) · [ordinary Lean entry point](../../lean/ARD/src/ARDFinal.lean)

This paper proves the finite rules in the linked definition and the two expanders. Time, memory and drawing guards in the implementations are not mathematical rules. This is a paper argument in a weak axiom system; the ordinary Lean code is a separate deliverable, not an encoding of a derivation in that weak formal theory. We do not prove ARD stronger than Y, RPD, LRD or Ω-LRD3.

## 1. Theorem and domain

We use the classical set theory

$$
S=KP_\omega+\text{“there exists an uncountable ordinal”}.
$$

Here KP has Extensionality, Empty Set, Pairing, Union, Infinity, literal $\Delta_0$-Separation, $\Delta_0$-Collection and **full Set Induction**. An uncountable ordinal is an ordinal greater than $\omega$ with no set-function surjection from $\omega$ onto it. Power Set, full Separation, full Collection and the Axiom of Choice are not assumed.

**Theorem.** In $S$:

1. There is an ordinal-valued set function $\mu$ on all structurally legal finite ARD graphs such that $G\ne0\Longrightarrow\mu(G[n])<\mu(G)$. Consequently, no infinite chain of nonzero expansions exists, even if the fundamental-sequence index changes arbitrarily at every step.
2. The graphs reachable from the standard seeds by finite expansion paths form a well-order under the implemented column lexicographic comparison.
3. Adjoining an external greatest element, whose fundamental sequence consists of the standard seeds, preserves well-ordering.

In this paper a well-order is a strict linear order in which every nonempty **set subset** has a least element. It is not merely the absence of some restricted class of computable descending sequences.

The restriction to the standard domain in the second assertion cannot be dropped. Column order on the set of all structurally legal graphs is not a well-order:

$$
[\varnothing]^{m+1}[(0,0,0)]>
[\varnothing]^{m+2}[(0,0,0)]>\cdots.
$$

This does not contradict the first assertion: a decrease in column order need not be an expansion step. The NER input validator checks structural legality, not membership in the standard domain.

### 1.1 Finite graphs, root closure and comparison

A graph is $G=(C_0,\ldots,C_{m-1})$. Column $j$ consists of compressed entries

$$
(k,p,q),\qquad k<j,\qquad q\le p<j,
$$

with natural-number coordinates; no condition $k\le p$ is imposed. Such an entry denotes all atoms $(k,t,p,j)$ for $0\le t\le q$. Among entries with the same $(k,p)$, retain only the largest $q$. An “atom of the graph” below always means an atom of this complete root closure.

Sort entries in decreasing order of $(p,k,q)$. Both columns and column strings are compared lexicographically, with a proper prefix smaller. This is the same as listing all atoms of each column in decreasing order of $(p,k,t)$: roots belonging to the same parent and anchor form a contiguous segment, and the first different maximum root already determines the result.

### 1.2 Expansion

Set $0[n]=0$. For a nonempty graph, index zero deletes its last column; if that column is empty, every index deletes it. In the remaining case put $x=m-1$, select the largest last-column entry by $(k,q,p)$, write it $(k,c,r)$, and set

$$
\ell=x-c>0,\qquad
\phi_b(i)=\begin{cases}i&i<c,\\i+b\ell&i\ge c.\end{cases}
$$

The graph $G[n]$ has $x+n\ell$ columns. Take the following union, then apply root closure and normalization:

- For $b=0,\ldots,n$, copy $G\restriction x$, moving its anchor, parent, maximum root and child by $\phi_b$.
- For $b=0,\ldots,n-1$, form a seam in column $x+b\ell$. For an old last-column entry $(h,p,q)$: if $h<k$, insert $(\phi_b(h),\phi_b(p),\phi_b(q))$; if $h=k$, replace the maximum root by $\min(\phi_b(q),\phi_b(r)-1)$ and insert it only if this is nonnegative; if $h>k$, insert nothing.
- In that seam also insert every $(h,\phi_b(c),\phi_b(c))$ with $0\le h<\phi_b(k)$.

The cut is the control parent $c$, not $\max(k,c)$. Copies overlap before the cut; overlapping insertion does not multiply relations. This definition consists of finite loops and does not call expansion on any newly produced graph.

The standard seeds and domain are

$$
A_0=0,\quad A_1=[\varnothing],\quad
A_{n+1}=A_n\frown[(n-1,n-1,n-1)]\quad(n\ge1),
\qquad U=\bigcup_{n<\omega}D(A_n),
$$

where $D(H)$ includes $H$ and all of its finite-expansion descendants. Paths ignore the $0\to0$ self-loop. The external symbol $\mathsf{Top}$ is greater than all finite standard expressions, with $\mathsf{Top}[n]=A_n$.

## 2. Finite structural lemmas

**Lemma 2.1.** Expansion preserves structural legality, and $G[n]$ is a complete-column prefix of $G[n+1]$.

The map $\phi_b$ is strictly increasing, so copying preserves all references to earlier columns. A generated entry satisfies $h<\phi_b(k)<x+b\ell$, and its parent and root satisfy $\phi_b(c)<x+b\ell$. Every reference from a column before the cut also lies before the cut, so all copies agree on that prefix. On increasing the index from $n$ to $n+1$, the additional seam and source block begin at $x+n\ell$; the old output is unchanged. Empty-last-column and zero cases are immediate. ∎

**Lemma 2.2.** If $G\ne0$, then $G[n]<G$.

Deletion is immediate. Otherwise the first $x$ columns remain unchanged. Column $x$ is the union of seam zero and the next copy's source column $C_c$. Every parent in that source column is below $c$ and hence is not moved. Maximality of the control also implies that the old last column has no anchor greater than $k$. Every entry with parent greater than $c$ is retained: lower-anchor entries are not truncated, and a same-anchor entry must have maximum root below $r$, or it would contradict the control's maximality in $(k,r,c)$ order. At parent $c$ and anchor $k$, the old maximum root $r$ is decreased to $r-1$, or the group disappears. Generated entries have anchor below $k$, and source entries have parent below $c$, so neither can restore that difference. The first difference in $(p,k,q)$ order is therefore strictly smaller. ∎

Every finite prefix can be obtained by repeated index-zero deletion. These lemmas do not yet prove well-ordering; we first construct an independent rank decreasing under expansion.

## 3. Set constructions required in KP

Work temporarily in $S+V=L$. Obtain the least uncountable ordinal $\kappa$ by full Set Induction below a given uncountable ordinal, not by full Separation on the predicate “uncountable.” The ordinal $\kappa$ is a limit, and each $0<\alpha<\kappa$ admits a natural-number surjection.

Apply $\Delta_0$-Collection to these surjections to obtain a set $C$ containing suitable witnesses. In $V=L$, this set has a constructed set well-order. For each $\alpha$, select the first valid witness in $C$, obtaining

$$
e:\kappa\times\omega\longrightarrow\kappa,
\qquad e(\alpha,\cdot):\omega\twoheadrightarrow\alpha\quad(0<\alpha<\kappa),
\quad e(0,n)=0.
$$

When used as a function symbol in the first-order structure below, extend it to a total binary function by giving value zero when its second argument is outside $\omega$.

This uses the constructible well-order of one existing set, not Choice for an arbitrary family of sets. The order can be constructed recursively in sufficiently high levels of $L$, using defining formulas and finite tuples of parameters.

**Countable boundedness.** For each set function $v:\omega\to\kappa$,

$$
\sup_n(v(n)+1)<\kappa.
$$

Otherwise enumerate each $v(n)+1$ with $e$ and code pairs of natural numbers, obtaining a surjection from $\omega$ onto $\kappa$, a contradiction.

Ordinary KP provides $\Sigma_1$-Collection, $\Delta_1$-Separation, sets of finite tuples, bounded-definition recursion along a given ordinal, and satisfaction for set structures. For background, see [McKenzie, Section 2, Lemmas 2.2, 2.3, 2.6 and Theorem 2.8](https://arxiv.org/html/1806.08500v4#S2). These are background tools only; the dynamic relation and splice below still require their own proofs.

Finite graphs, finite templates and finite paths are coded by natural numbers. Their primitive-recursive decoding and computation relations are available as sets. When a literally bounded formula is required, first obtain these decoding tables and use them as fixed set parameters. One must not simply call an arbitrary arithmetic formula $\Delta_0$ in the pure language of set theory.

## 4. The dynamic finite-demand relation

Let $B=(\kappa+1)^{<\omega}$, the set of all finite tuples with entries in $\kappa+1$. For a graph of width $m$, define

$$
\operatorname{Inc}(f)\iff |f|=m\ \land\
\omega<f(0)<\cdots<f(m-1)<\kappa,
$$

$$
\operatorname{Rep}(G,f)\iff
\operatorname{Inc}(f)\land
\bigwedge_{(h,t,p,j)\in G}R(f(h),f(t),f(p),f(j)).
\tag{4.1}
$$

The empty tuple satisfies the corresponding empty conditions. Strict increase and the lower bound $\omega$ are formal parts of representation, not conventions that may be omitted while retaining only the edge conjunction.

A template $N$ consists of finitely many triples $(h,t,p)$ with $h<m$ and $t\le p<m$. Define

$$
\operatorname{End}_b(N,f)=\bigwedge_N R(f(h),f(t),f(p),b),
$$

$$
\operatorname{Adm}_{K,\theta}(N,f,c)=
\bigwedge_N\bigl[f(h)<K\ \lor\
(f(h)=K\land t<c\land f(t)<\theta)\bigr].
$$

The assertion $FR_{K,\theta}(a,b)$ says that for every finite legal $G,N$, cut $c<m$ and $f\in B$, if

$$
\operatorname{Rep}(G,f),\quad f[m]\subset b,\quad f(c)=a,\quad
\operatorname{Adm}_{K,\theta}(N,f,c),\quad\operatorname{End}_b(N,f),
$$

then some $g\in B$ satisfies

$$
\operatorname{Rep}(G,g),\quad g[m]\subset a,\quad
g\restriction c=f\restriction c,\quad\operatorname{End}_a(N,g).
\tag{4.2}
$$

Here $f[m]\subset b$ means that every coordinate is below $b$. In particular, the output template's row value is $g(h)$, not the frozen old value $f(h)$. The output need not satisfy the original admissibility condition again.

Define

$$
R(K,\theta,a,b)\iff
K<b\le\kappa\ \land\ \theta\le a<b\ \land\ \omega<a
\ \land\ FR_{K,\theta}(a,b).
\tag{4.3}
$$

### 4.1 The recursion really produces a set

All $K<\kappa$ are allowed; no countable upper bound for a fixed row domain is chosen beforehand. Recurse lexicographically on $(b,K,\theta)$:

- Internal relations of the input graph have right endpoint below $b$.
- Internal relations and endpoint templates of the output have right endpoint at most $a<b$.
- By admissibility, input endpoint templates have a smaller row parameter, or the same row parameter and a smaller root parameter.

When defining the recursive operator, reject inadmissible inputs before reading their endpoint templates; do not unconditionally query a relation that has not yet been defined. If the guard is false, give value false without any recursive query.

For example, put $T=(\kappa+1)\cdot\kappa$ and $\Gamma=T\cdot(\kappa+1)$, and encode valid stages $K<\kappa$, $\theta<b\le\kappa$ by

$$
\iota(b,K,\theta)=T\cdot b+(\kappa+1)\cdot K+\theta.
$$

Each stage code is below $\Gamma$ and strictly respects the required ordering. Stage coding and coordinate projections are themselves made into set tables beforehand: apply Collection and Separation to the KP-available $\Delta_1$ ordinal operations on a fixed bounded product domain. Checking a history then only reads these tables.

Given a history, the set of $a\le\kappa$ satisfying the current stage is obtained by bounded Separation on $\kappa+1$. Graph codes, template codes and cuts range over fixed coding sets, and all label tuples range over $B$. Validity of a history is checked by bounded conditions, and uniqueness follows by induction. Recurse along $\Gamma$; at limit stages use $\Sigma_1$-Collection of the already existing shorter histories and take their union. There is no Power Set step collecting all possible histories. Thus $R$ is a set relation.

### 4.2 Three immediate properties

1. **Strict guard:** $R(K,\theta,a,b)$ implies all the inequalities in (4.3).
2. **Root weakening:** if $\eta\le\theta$ and $R(K,\theta,a,b)$, then $R(K,\eta,a,b)$. Every $(K,\eta)$-admissible demand is $(K,\theta)$-admissible.
3. **Lower rows:** if $H<K$, $\eta\le a$ and $R(K,\theta,a,b)$, then $R(H,\eta,a,b)$. The row value of every $H$-admissible template is at most $H$, hence strictly below $K$; the other input and output conditions are unchanged. **There is no requirement $H\le a$.** Later we must allow anchors after the cut.

## 5. Initial representations of arbitrary finite graphs

Put $P(K,\theta,a)=R(K,\theta,a,\kappa)$ and consider the fixed set structure

$$
\mathcal A=(\kappa;<,R\restriction\kappa,P,e,\omega).
$$

Here $R\restriction\kappa$ restricts all four coordinates to values below $\kappa$. The structure has neither an out-of-domain constant $\kappa$ nor a constant for a frozen row-domain bound.

### 5.1 Sufficiently many elementary initial segments

For every $\gamma<\kappa$, some $\delta$ satisfies

$$
\max(\omega,\gamma)<\delta<\kappa,
\qquad\mathcal A\restriction\delta\prec\mathcal A.
\tag{5.1}
$$

Using set satisfaction, select the least ordinal witness for each existential formula, with value zero if no witness exists. These are countably many finitary Skolem operations obtainable as a set. Close $\omega\cup\{\omega,\gamma\}$ under them and under $e$ to obtain a set $H$. Finite closed terms can actually be enumerated by natural numbers, so $H$ is countable; this is not a selection of countably many arbitrary witnesses. If $\alpha\in H$, closure under $e$, together with all natural numbers belonging to $H$, gives $\alpha\subseteq H$. Thus $H$ is an ordinal $\delta$. Uncountability gives $\delta<\kappa$, while inclusion of $\omega,\gamma$ gives the strict lower bounds. The witness criterion proves elementarity. We reflect only this set structure, not the set-theoretic universe.

### 5.2 Endpoint agreement

For each such $\delta$,

$$
P(K,\theta,a)\iff R(K,\theta,a,\delta)
\quad(K<\delta,\ \theta\le a<\delta).
\tag{5.2}
$$

Induct lexicographically on $(K,\theta)$, considering all $a$ simultaneously. If $a\le\omega$, both guards are false.

For the forward direction, take an admissible input below $\delta$. By admissibility its endpoint templates only query earlier pairs $(K,\theta)$. Use the induction hypothesis to replace them with $P$-templates, and apply $FR$ at $\kappa$. All output labels lie below $a$; its internal and endpoint relations read the same $R$, so this is the required output.

Conversely, suppose the right side holds but $P$ does not. The guard is already satisfied, so there are a fixed finite shape $G,N,c$ and a counterexample input. Its counterexample property is a finite formula in $\mathcal A$:

> There is a label tuple $f$ satisfying internal representation, $f(c)=a$, $(K,\theta)$-admissibility and the $P$ endpoint templates, but there is no representation output entirely below $a$ preserving the cut prefix and satisfying the templates aimed at $a$.

Expand each fixed finite tuple into finitely many variables. The formula's parameters are only $K,\theta,a,\omega$ and finite shape information, all below $\delta$; the parameter $K$ must not be overlooked. Elementarity yields a counterexample input entirely in $\delta$. Use the induction hypothesis to replace its $P$-templates by templates aimed at $\delta$. The statement “no output exists” agrees in the two structures: candidate output coordinates are all below $a<\delta$, and queried right endpoints are at most $a$. This contradicts $FR$ on the right side.

### 5.3 Strong endpoint supply

For the same $\delta$,

$$
P(K,\theta,\delta)\quad(K<\kappa,\ \theta\le\delta).
\tag{5.3}
$$

The case $K\ge\delta$ is deliberately included. Take any admissible demand $G,N,c,f$ at $\kappa$ with cut label $\delta$. Fix only the prefix $u=f\restriction c$, whose coordinates lie below $\delta$. Reflect the finite existential formula

$$
\exists(z_i)_{i<m}\left[
\operatorname{Inc}(z)\land z\restriction c=u\land
\bigwedge_G R(z_h,z_t,z_p,z_j)\land
\bigwedge_N P(z_h,z_t,z_p)\right].
\tag{5.4}
$$

The old input $f$ witnesses its truth. This formula does not contain the control parameters $K,\theta$, does not fix $z_c=\delta$, does not freeze any old row value at or after the cut, and does not require the output to satisfy the old admissibility condition again. When expanding $\operatorname{Inc}$ into a formula of the structure, write only $\omega<z_0<\cdots<z_{m-1}$: the final bound below $\kappa$ is supplied by the quantifier domain, not by an additional out-of-domain parameter.

Elementarity gives $z$ entirely within $\delta$. Every new row value $z_h$ is below $\delta$, so (5.2) turns each $P$-template into a template aimed at $\delta$. This is precisely an $FR$ output.

### 5.4 Initial representation lemma

For an arbitrary structurally legal graph of width $m$, apply (5.1) finitely many times to obtain elementary heights $\delta_0<\cdots<\delta_{m-1}$ and put $f(i)=\delta_i$. For an atom $(h,t,p,j)$, (5.3) at $\delta_p$ gives $P(\delta_h,\delta_t,\delta_p)$, including when $h\ge p$. Then apply (5.2) at $\delta_j$, using $h<j$, to obtain

$$
R(\delta_h,\delta_t,\delta_p,\delta_j).
$$

Thus $\operatorname{Rep}(G,f)$ holds. Use the empty tuple for the empty graph. Only finitely many heights are selected here; no additional unbounded choice is required.

## 6. The dynamic four-coordinate splice lemma

**Lemma.** If a nonempty graph $G$ has a representation with last label $\beta$, then for every $n$, the graph $G[n]$ has a representation with all labels strictly below $\beta$.

An empty last column or index zero is handled by restricting the old representation. For the nonempty-last-column case, retain $x,k,c,r,\ell,\phi_b$ and put

$$
N_b=x+b\ell,\qquad c_b=c+b\ell.
$$

### 6.1 Decomposing the output into blocks

Let $D_0=G\restriction x$. To pass from $D_b$ to $D_{b+1}$, append exactly $\ell$ columns. New column $N_b+i$ is the four-coordinate $\phi_{b+1}$ copy of source column $C_{c+i}$, with seam $b$ merged into it when $i=0$; normalize afterward.

Since $\phi_{b+1}(c)=N_b$, this exactly decomposes the union in Section 1.2, so $D_n=G[n]$. The source is still the original graph $G$, not a fresh expansion of the current $D_b$.

Let the original representation be $F$, with $F(x)=\beta$. Inductively construct a labeling $f$ of width $N_b$ satisfying:

1. $\operatorname{Rep}(D_b,f)$, with all labels below $\beta$.
2. For every original prefix entry $(h,p,q)\in C_j$, $j<x$, the source fact
   $$
   R(f(\phi_b(h)),f(\phi_b(q)),f(\phi_b(p)),f(\phi_b(j))).
   \tag{6.1}
   $$
3. For every original last-column entry $(h,p,q)$, the fixed virtual-endpoint template
   $$
   R(f(\phi_b(h)),f(\phi_b(q)),f(\phi_b(p)),\beta).
   \tag{6.2}
   $$

Stage zero is given by $F\restriction x$, since $\phi_0$ is the identity.

### 6.2 A seam is an admissible finite demand

At stage $b$ put

$$
K=f(\phi_b(k)),\qquad\theta=f(\phi_b(r)),\qquad a=f(c_b).
$$

The control instance of (6.2) gives $R(K,\theta,a,\beta)$. Let $N$ contain the three-coordinate templates of every root atom of seam $b$, interpreted as addresses in the current graph $D_b$. Every address is below $N_b$.

The maximum-root relations of ordinary seam entries come from (6.2), and root weakening supplies their smaller roots. If the row comes from $h<k$, strict increase makes its label smaller than $K$. For $h=k$, truncation ensures that every root $t<\phi_b(r)\le c_b$, so $t<c_b$ and $f(t)<\theta$. All ordinary seam templates are therefore admissible.

A generated entry corresponds to arbitrary $h<\phi_b(k)$ and $t\le c_b$. Since $f(h)<K$ and $f(t)\le a$, the lower-rows property applied to the control relation gives

$$
R(f(h),f(t),a,\beta).
$$

This is also an admissible template. Here $h$ may be at or above $c_b$; one must not impose the additional condition that its row label lie below $a$.

Apply $FR_{K,\theta}(a,\beta)$ to the whole graph $D_b$, obtaining $g$ such that

$$
\operatorname{Rep}(D_b,g),\quad g[N_b]\subset a,\quad
g\restriction c_b=f\restriction c_b,\quad\operatorname{End}_a(N,g).
\tag{6.3}
$$

### 6.3 Splicing and checking every source

Put

$$
h=g\frown f[c_b,N_b).
\tag{6.4}
$$

Its length is $N_b+\ell=N_{b+1}$. All of $g$ lies below $a=f(c_b)$, so $h$ is strictly increasing, entirely below $\beta$, with $h(N_b)=a$. The key identity is

$$
h(\phi_{b+1}(i))=f(\phi_b(i))\qquad(i<x).
\tag{6.5}
$$

If $i<c$, this is in the fixed prefix and (6.3) gives the identity. If $i\ge c$, then $\phi_{b+1}(i)\ge N_b$; the concatenation selects $f(\phi_{b+1}(i)-\ell)=f(\phi_b(i))$.

This identity applies to the anchor, root, parent and child simultaneously, not just the latter three. It immediately gives the next stage's source facts (6.1) and virtual templates (6.2). Check all actual atoms of $D_{b+1}$:

- **Old graph atoms:** the child and all its references are below $N_b$, so all four labels come from $g$ and the relation follows from $\operatorname{Rep}(D_b,g)$.
- **New source entries:** transport (6.1) at the maximum root using all four instances of (6.5). Root closure may also fill coordinates skipped by $\phi_{b+1}$. For any $t\le\phi_{b+1}(q)$, strict increase gives $h(t)\le h(\phi_{b+1}(q))$, so root weakening applies. A new root need not be the exact image of an old root.
- **New seam atoms:** the child is $N_b$ and all other coordinates are below $N_b$. Those coordinates take their values from $g$ in (6.3), while the child label is $a=h(N_b)$, exactly as required.

A maximum root produced by normalization comes from an inserted entry; normalization creates no new anchor or parent. These three cases and their root weakenings therefore exhaust all output atoms, proving $\operatorname{Rep}(D_{b+1},h)$. Induction and $b=n$ finish the proof. ∎

## 7. One global descent rank and standard-domain well-ordering

### 7.1 The rank is a single actual set function

Let $Q\subseteq\omega$ be the set of unique canonical graph codes; different input strings are not different graphs. Totalize finite decoding by returning an error marker for an invalid code. Its total $\Delta_1$ definition and $\Sigma_1$-Collection first supply all outputs; $\Delta_1$-Separation then supplies the decoding function table. Alternatively obtain length and atom-incidence tables directly. All subsequent syntactic queries only read these existing sets.

Define

$$
\mu(G)=\begin{cases}
0,&G=0,\\
\min\{\beta<\kappa:\exists f\in B\,
[\operatorname{Rep}(G,f)\land f(|G|-1)=\beta]\},&G\ne0.
\end{cases}
\tag{7.1}
$$

The initial representation lemma guarantees a candidate for each nonempty graph. With the decoding tables, $R$ and $B$ fixed, being a candidate is a bounded formula; adding that every smaller $\gamma<\beta$ fails to be a candidate is still bounded. Thus one application of Separation on $Q\times\kappa$ obtains the entire function graph. No additional collection of representations, one for each graph, is needed. In particular, this does not smuggle in $\Sigma_1$-Separation for a partial $\Sigma_1$ decoding function.

Every label of a nonempty representation exceeds $\omega$, so $\mu(G)>\omega>0$. Apply the splice lemma to a representation realizing the least last label to obtain

$$
G\ne0\quad\Longrightarrow\quad\mu(G[n])<\mu(G).
\tag{7.2}
$$

The empty output has rank zero. A nonempty output has a representation whose last label is smaller than the old minimum. Since ordinals admit no infinite strict descent, nonzero expansion is well founded.

### 7.2 Descendant cones are linearly ordered by reachability

Induct on $\mu(H)$ to prove that any $V,W\in D(H)$ are comparable by expansion reachability. For $H=0$ there is only one graph. If either equals $H$, comparability is immediate. Otherwise the first steps of the two finite paths are $H[i]$ and $H[j]$. Put $t=\max(i,j)$. By the complete-prefix property and repeated index-zero deletion, both belong to $D(H[t])$, and hence so do $V,W$. By (7.2), $\mu(H[t])<\mu(H)$, so the induction hypothesis applies.

For distinct $V,W$ in a common cone, Lemma 2.2 shows that reachability agrees with strict decrease in column order. Consequently,

$$
V<W\quad\Longrightarrow\quad V\in D(W)\setminus\{W\}
\quad\Longrightarrow\quad\mu(V)<\mu(W).
\tag{7.3}
$$

The logical order matters: first obtain an expansion-decreasing rank independently, next prove linearity of reachability, and only then deduce order preservation of the rank. The prefix property alone does not justify declaring each descendant cone an initial segment.

### 7.3 The standard domain and external top

Since $A_{n+1}[0]=A_n$, any two standard graphs have a common seed ancestor. Formula (7.3) makes the same set function $\mu\restriction U$ strictly order-preserving throughout $U$. For any nonempty set $W\subseteq U$, its rank image is a set subset of $\kappa$. Choose the least ordinal in that image and a preimage; the latter is the least element of $W$.

This proves that column order on $U$ is a well-order. It does not rely on the false unconditional assertion that every increasing union of well-orders is well-ordered. It also shows that each $D(A_n)$ is an initial segment of $U$: if $V<W\in D(A_n)$ and $V\in U$, comparability in a common seed cone gives $V\in D(W)\subseteq D(A_n)$.

Assign rank $\kappa$ to the external top. This strictly embeds $U\cup\{\mathsf{Top}\}$ into $\kappa+1$, and every top-to-$A_n$ expansion decreases rank. The top is not involved in the index-zero deletion induction; it is adjoined only after the finite standard-domain theorem has been established.

## 8. Removing the auxiliary assumption V=L

In ordinary KP, the constructible inner class $L$ satisfies the same KP and has the same ordinals and natural numbers. This uses the ordinary KP inner-class construction, not power-set KP or an additional large-cardinal hypothesis. See [Rathjen, the introduction on ordinary KP and V=L and the KP axioms in Section 2](https://arxiv.org/html/1801.01897v1) for background.

More explicitly, the levels $L_\alpha$ and their recursion can be constructed in KP, and bounded formulas are absolute between transitive levels. To verify bounded Collection in $L$, collect ambient witnesses together with indices of levels containing them and then cover them by a common level; this uses the available ambient $\Sigma_1$-Collection. Full Set Induction can also be relativized. No assertion that KP proves the existence of a transitive set model of itself is being made.

If $\nu$ is uncountable in the ambient universe, $L$ also has no surjection from $\omega$ onto $\nu$: any such function in $L$ would be an ambient function. Thus the preceding construction can be carried out inside $L$, giving an ordinal $\chi$ and an actual set function

$$
\mu:Q\longrightarrow\chi
$$

with strict rank decrease for nonzero expansion. Here $\chi$ is the least uncountable ordinal of $L$; it need not remain uncountable in the ambient universe.

Canonical graph codes, expansion computations, finite paths and seeds are determined by finite computation and agree code by code in $L$ and the ambient universe. The function $\mu$ and its ordinal values are actual sets, and strict ordinal comparison is absolute. The same function therefore still satisfies (7.2) externally. Reapply Sections 7.2 and 7.3 in the ambient universe to prove well-ordering of standard column order, assigning rank $\chi$ to the top.

In particular, the ambient universe may have subsets $W\subseteq U$ not belonging to $L$. Nonetheless,

$$
\{\beta\in\chi:\exists G\in W\ (\mu(G)=\beta)\}
$$

is obtained by bounded Separation and has a least element. What transfers is the actual rank function, not merely the assertion that $L$ regards the order as well-ordered. The conclusion therefore holds in the original theory $S$. ∎

## 9. Scope and ordinary Lean verification

This paper proves well-foundedness of nonzero expansion on all structurally legal finite ARD graphs, well-ordering of the standard column order, and preservation of well-ordering when an external greatest element is added. The column order on all raw graphs is not well-ordered, as Section 1 shows.

Anchors change together with the other three coordinates. The strong endpoint supply allowing $K\ge\delta$ in Section 5.3 and the four-coordinate identity in Section 6 are necessary additions to the fixed-row argument; one cannot obtain them merely by renaming the old Lean theorems.

The independent ordinary Lean entry point is [ARDFinal.lean](../../lean/ARD/src/ARDFinal.lean). Its finite geometry uses explicit root closure. The dynamic semantic relation is actually constructed by recursion on $(b,K,\theta)$; neither reflection nor initial representation is postulated as an extra axiom. The semantic backend constructs endpoint agreement, strong supply and initial representations from least bad witnesses, least prefix-extension witnesses and countable finitary closure. Operator codes consist only of finite shapes and natural numbers. The variable ordinal $K$ is an operator input; no countability of the entire ordinal type is assumed.

There are several precise differences between the ordinary Lean construction and the weak-theory account in Sections 3–8:

- Lean first defines its relation by well-founded recursion on the ordinal type, with the guard $K<b$, and then works below the selected ambient $\kappa$. The paper obtains one bounded set table below $\kappa$ directly. The recursive dependencies are the same; the ordinary type-theoretic construction does not itself certify the paper's KP set-existence bookkeeping.
- Lean closes under the actual least Bad and Ext witness-coordinate operations rather than building full elementary initial segments of $\mathcal A$. Closure for Bad requires $K,\theta,a<\delta$; strong supply still allows $K\ge\delta$, because the reflected new row values are below $\delta$. This realizes the specific endpoint argument needed in Sections 5.2–5.4 without assuming an elementary-substructure oracle.
- The ordinary `HostAmbient` implementation uses mathlib's actual first uncountable ordinal and classical choice to choose enumerations. This is not an encoding of the paper's $S+V=L$ construction or its transfer back to $S$. In particular, `Classical.choice` in a Lean axiom report does not mean that Choice was added to the paper's object theory.
- Lean's raw `Valid` predicate checks coordinate inequalities and need not demand sortedness or root closure. The standard expressions are canonical. The paper's compressed graphs denote their complete root closures. The release also has independent finite-union definitions `PaperEdge` and `PaperFs`: the concrete Lean expansion agrees with these definitions atom by atom and, on canonical inputs, as a unique normalized graph. Their generated standard domains agree. Compression preserves graph comparison and the selected control entry.

The final ordinary-Lean module has compiled with only `propext`, `Classical.choice` and `Quot.sound` in its axiom reports, without `sorry` or new axioms. In namespace `OrdinalFormal.ARD`, its public conclusions include:

```text
valid_accessible
valid_step_wellFounded
standard_wellFounded
standard_strictWellOrder
standard_with_top_strictWellOrder
paper_standard_with_top_strictWellOrder
```

The last theorem directly uses the standard terms generated by the independent finite-union paper definition. For the separate clean release-directory rebuild and verification manifest, see the [Lean project](../../lean/README.md); incremental module compilation is not a substitute for that release check.

The paper does not use Power Set, Choice, full Separation, full Collection or an additional reflection axiom. The released ordinary Lean code does not encode the syntax and proof system of $S$ or verify a coded $S$-derivation. Bounded program tests check implementations, not mathematical well-ordering, and ordinary Lean verification does not automatically give line-by-line formal verification of the Python/JavaScript parsers or drawing code.

Finally, this paper does not turn the existence of $\kappa$ or $\chi$ into an unproved concrete PTO comparison. It asserts neither optimality of the axiom bound nor that ARD is equally strong or stronger than earlier notations merely because a common upper bound is available.
