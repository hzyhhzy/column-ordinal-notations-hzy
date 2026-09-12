# Y, RPD, LRD, and Ω-LRD3: Well-Ordering in Weak Set Theory · [中文版](well-ordering.zh-CN.md)

2026-09-13. The paper proof and the ordinary Lean formalization are distinct deliverables.

[PDF edition](well-ordering.pdf) · [Lean project](../../lean/README.md)

Companion definitions: [RPD](../../notations/RPD/definition.md), [LRD](../../notations/LRD/definition.md), and [Ω-LRD3](../../notations/Omega-LRD3/definition.md).

The base theory used in this paper is

$$
S=KP_\omega+\exists\nu\,[\nu>\omega\text{ is an ordinal and there is no set function }\omega\twoheadrightarrow\nu].
$$

Here KP includes classical logic, Extensionality, Empty Set, Pairing, Union, Infinity, literal $\Delta_0$-Separation and Collection, and **full Set Induction**. We do not add Power Set, full Separation, full Collection, Choice, an axiomatic reflection principle, or a large-cardinal assumption. This paper is not a Lean encoding of a proof system for those object-theoretic axioms.

We start from the finite-demand route in the simplified manuscript *A Short Proof of 1-Y Well-Ordering in KP with ω₁*. We supply countable ordinal row labels, explicit ranks for finite row pools, the depth induction for Ω-LRD3, and the passage to the four actual standard domains. The finite mountain/column-copying lemmas refer to verified concrete proofs; the exact interfaces are identified in Sections 3 and 10. Well-ordering of none of the notations is assumed in the semantic construction.

## 1. Objects and conclusion

Throughout, a “well-order” means that the specified comparison is a strict linear order and every nonempty **set subset** has a least element. This is stronger than merely ruling out a particular kind of computable descending chain. Strict expansion excludes the self-loop of the empty expression; the convention remains $0[n]=0$.

The four objects are fixed as follows.

| Object | Fixed rules and standard domain |
| --- | --- |
| Y | The inherited-ancestry Y definition at upstream commit `1689b21131b488ec2ba2515bd630360371a2389d`; seeds `(1,m)`, `m≥2`, and their finite-expansion descendants; sequence lexicographic order |
| RPD | The current column-graph version; natural-number rows and empty generation packages; two-column seeds whose second column has parent/root-`0` edges on rows `0,...,n`; all seed descendants and an external top |
| LRD | Rows are normalized polynomials below $\omega^\omega$, together with $\omega^\omega$; the descendants of the seed $[\varnothing][(\omega^\omega,0,0)]$, including that seed itself |
| Ω-LRD3 | Rows are finite graphs of the same notation; generation packages run through index $b$; single-column nested seeds $A_0=0,A_1=1$, and $A_{n+1}=A_n\mathbin{\frown}[(A_n,n-1,n-1)]$ for $n\ge1$; seed descendants and an external top |

Equivalence between the original Naruyoko Y JavaScript and the upstream Lean algorithm on their entire intended legal domain is **not** a new conclusion of this paper. That equivalence question is left separate and is not asserted here. The pinned upstream source is [1Y-Well-Ordering-Lean, commit `1689b21131b488ec2ba2515bd630360371a2389d`](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean/tree/1689b21131b488ec2ba2515bd630360371a2389d). The Y theorem concerns precisely the inherited-ancestry definition in the table; randomized program comparisons do not replace a proof of rule equivalence. The correspondence between compressed triples and explicit root expansion for the other three notations is explained in Section 9.

**Theorem.** $S$ proves that these four standard domains are well-ordered. Adjoining the external greatest element to RPD or Ω-LRD3 preserves well-ordering. If a separate symbol is used for the limit of the entire Y standard domain, adjoining that greatest element also preserves well-ordering. The two-column LRD seed specified above is already the greatest element of its domain; we do not replace it with a newly invented top.

The proof does not compare the four order types, nor infer equal strength from a common axiomatic upper bound.

## 2. Basic constructions in KP and a uniform enumeration

### 2.1 Available derived principles

KP proves $\Sigma_1$-Collection, $\Delta_1$-Separation, existence of sets of finite sequences, and functional recursion along ordinals. Satisfaction for a set structure is $\Delta_1$: first form the set of all finite assignments, then separate the complete satisfaction set. The constructible hierarchy $\alpha\mapsto L_\alpha$ is a total $\Delta_1$ function. Precise references for these standard facts are [McKenzie, Lemmas 2.2, 2.3, 2.6 and Theorem 2.8](https://arxiv.org/html/1806.08500v4#S2). The weaker induction requirements of that source are covered by the full Set Induction used here.

Every recursion below proceeds along an **already given ordinal** or along the natural numbers. We do not invoke a principle saying that every internal well-order can be collapsed to an ordinal. When all inputs and outputs of a finitary computation are needed, finite computation records first give a $\Sigma_1$ existence definition. Determinism and totality yield a $\Delta_1$ definition, after which its graph can be collected/separated. For programs coded by natural numbers, all finite records can also be coded in $\omega$.

### 2.2 Work temporarily in $S+V=L$

Full Set Induction yields a least uncountable ordinal $\kappa$. One must not first apply unauthorized full Separation to the predicate “uncountable” on $\nu+1$. Instead, apply class minimization directly to the formula defining uncountable ordinals; comparability of ordinals makes a minimal one least. We have $\omega<\kappa$, and $\kappa$ is a limit ordinal, since the successor of a countable ordinal is still the image of a surjection from $\omega$.

For each $0<\alpha<\kappa$ there is a set function $\omega\twoheadrightarrow\alpha$. The assertion that $f$ is such a surjection is bounded in $f,\omega,\alpha$. Thus $\Delta_0$-Collection gives a set $C$ containing at least one required witness for each $\alpha$. In $V=L$, $C$ has a constructible well-order whose relation is a set. Choose within $C$ the least $f$ satisfying this bounded condition; the minimality quantifier ranges only over $C$. Bounded Separation on $\kappa\times C$ gives the entire selection graph, and composition with evaluation gives

$$
e:\kappa\times\omega\longrightarrow\kappa,
\qquad e(\alpha,\cdot):\omega\twoheadrightarrow\alpha\quad(0<\alpha<\kappa),
\quad e(0,n)=0. \tag{2.1}
$$

This is not an application of Choice to an external class of choices. The required constructible well-order can be built together with the $L$ hierarchy. At successor levels, order new sets by their least defining code, consisting of a formula number and a finite tuple of parameters, with old sets first. For parameter tuples of fixed length, use a finite lexicographic power of the preceding level's order; compare formula numbers first. At a successor level, only that level's satisfaction set and bounded Separation/Collection are needed. At a limit level, take the union of the compatible order graphs. Induction on levels shows that every nonempty internal subset has a least element: first choose the earliest level at which one of its members appears, then the least definition code. This is the **internal least-element property for set subsets**; it does not treat the internal order graph of a possibly nonstandard model as an externally well-founded relation.

### 2.3 The countable-bound lemma actually needed below

For any given set function $v:\omega\to\kappa$,

$$
\sup_{n<\omega}(v(n)+1)<\kappa. \tag{2.2}
$$

Proof: the supremum, an ordinal obtained by union, is at most $\kappa$. If it were $\kappa$, the map $(n,m)\mapsto e(v(n)+1,m)$ would surject onto $\kappa$. Composing with a pairing of natural numbers would produce $\omega\twoheadrightarrow\kappa$, a contradiction. Here $v(n)+1<\kappa$ follows from the fact that $\kappa$ is a limit. All quantifiers in the composition graph are bounded by $v$, $e$, and existing product sets.

This proves the required countable-bound property without assuming in advance that $\kappa$ is a regular cardinal. Likewise, finite sums, products, and finite powers of finitely many ordinals below $\kappa$ remain countable and hence below $\kappa$. For example, the elements of $\alpha\cdot\beta$ are enumerated by $(i,j)\mapsto\alpha\cdot j+i$, for $i<\alpha,j<\beta$, followed by the use of (2.1) and natural-number pairing.

## 3. The two actual finite-geometric interfaces

Fix an ordinal row domain $0<\sigma<\kappa$. An atomic edge is $(K,q,p,j)$, with $K<\sigma$ and $q\le p<j<m$. A representation of a finite graph $A$ is a strictly increasing finite function $f:m\to D$ such that every edge satisfies $R(K,f(q),f(p),f(j))$. An endpoint template $N$ is a finite set of triples $(K,q,p)$, with $q\le p<m$. Write

$$
\operatorname{End}_b(N,f)\iff
\bigwedge_{(k,q,p)\in N}R(k,f(q),f(p),b).
$$

At a cut $c<m$ and control parameters $(K,\theta)$, admissibility is

$$
\operatorname{Adm}_{K,\theta}(N,f,c)\iff
\bigwedge_{(k,q,p)\in N}
\bigl(k<K\ \lor\ (k=K\land q<c\land f(q)<\theta)\bigr). \tag{3.1}
$$

The assertion $\operatorname{FR}_{K,\theta}(a,b)$ says: for every finite $A,N,c,f$, if $f$ represents $A$, every $f(i)<b$, $f(c)=a$, and both (3.1) and $\operatorname{End}_b$ hold, then there is a representation $g$ satisfying

$$
g\upharpoonright c=f\upharpoonright c,
\qquad g(i)<a\ (i<m),\qquad \operatorname{End}_a(N,g). \tag{3.2}
$$

The rows of internal edges are **not required** to be below $K$. Only the template pointing to the virtual endpoint $b$ is restricted by (3.1).

### 3.1 The proved finite lemma for Y

In the pinned upstream source, `OneY.RootIndexed.exprDiagram(s)` is the root-indexed graph of the complete finite mountain of $s$. The theorem `expand_lastRepresentation_lower` proves that, when $R$ has strict endpoints, permits root weakening, and satisfies the finite reflection condition above, a representation of a nonempty $s$ yields a representation with a smaller last label for each nonempty actual expansion of $s$. This includes bad-root selection, all finite copying, numeric reconstruction, and correspondence between the new mountain and the copied diagram. It does not leave “correctness of Y copying” as a separate unnamed assumption.

The upstream interface and the natural-number-row interface here agree field by field. In `y-audit/NatSemanticTransport.lean`, `representation_toLocal_iff` and `finiteReflection_iff` provide the two-way transport. Levels, roots, parents, children, cuts, and the strict root inequality are unchanged. Consequently the earlier snapshot cited in the simplified manuscript need not be byte-identical to this project's snapshot: this paper directly uses the proved interface of the current pinned snapshot.

The finite lemma uses only finite mountain reconstruction and induction on the finite number of copies. Replacing labels by members of a given set of ordinals and relation tests by membership in the set $R$ makes this proof available in KP. Only finitely many label witnesses are chosen; this must not be misclassified as an application of Dependent Choice.

### 3.2 The proved finite lemma for current column graphs

Within a column, edges are sorted in decreasing $(p,K,q)$ order. The control edge is greatest in $(K,q,p)$ order. For a nonempty graph $G$, let its final column index be $x=|G|-1$, its control edge be $(K,c,r)$ in **(row, parent, root)** order, and $\ell=x-c$. Ordinary seams follow the actual rules. The $b$th new seam may use any finite package $P_b(K)\subseteq\{H:H<K\}$.

Four semantic properties are needed: strict endpoints, root weakening, finite reflection, and

$$
H<K,\quad\eta\le a,\quad R(K,\theta,a,\beta)
\quad\Longrightarrow\quad R(H,\eta,a,\beta). \tag{3.3}
$$

Under these properties, every expansion of a valid nonempty $G$ has a representation below the old last label $\beta$. The corresponding complete proof is `GeneratedStagedReflection.fs_bounded`, not merely its abstract interface assumption.

Here is the invariant making the finite induction explicit. After $b$ blocks, the width is $x+b\ell$, the cut is $c+b\ell$, and the coordinate shift of the original prefix is $s_b(i)=i$ for $i<c$, and $s_b(i)=i+b\ell$ for $i\ge c$. Maintain a representation $f$ of the current graph, facts for the original prefix edges at $s_b$, and a template sending each edge of the original final column to the virtual endpoint $\beta$. At $b=0$, these are supplied directly by the original representation.

Root truncation at an ordinary seam places same-row template roots strictly below the control root and before the cut; lower-row templates satisfy the first branch of (3.1). The generated package has strictly lower rows, and (3.3) supplies all the new-root-to-cut templates. Apply (3.2) to reflect the current graph to $g<f(c+b\ell)$, and then append the old tail:

$$
h=g\mathbin{\frown}
\bigl(f(c+b\ell),\ldots,f(x+b\ell-1)\bigr).
$$

The function $h$ is strictly increasing and remains below $\beta$. Reflection preserves old edges; the retained source facts and root weakening establish copied edges; endpoint templates establish seam edges. The coordinate identity $h(s_{b+1}(i))=f(s_b(i))$ preserves the source facts and virtual templates required at the next step. Normalization only removes duplicate edges or adds weaker root edges, and therefore preserves representations. Finite induction yields all $n$ blocks. If there is no control edge, or if $n=0$, a prefix suffices; an empty output is handled separately.

These are exactly the stages `reflect_actual_stage`, `splice_actual_stage`, `all_stages`, and `fs_bounded`. The lemmas hold for arbitrary finite package sizes and arbitrary $n$. KP already covers the finite-set constructions and induction on $n$.

## 4. Finite-demand relations for any fixed countable ordinal row domain

Still in $S+V=L$, fix $0<\sigma<\kappa$. Set $D=\{a:\omega<a\le\kappa\}$ and $B=(\kappa+1)^{<\omega}$. Define the complete set relation

$$
R(K,\theta,a,b)\iff
K<\sigma\land\theta\le a<b\le\kappa\land\omega<a
\land\operatorname{FR}_{K,\theta}(a,b). \tag{4.1}
$$

This is not a circular axiom. Recursion in lexicographic $(b,K,\theta)$ order defines the Boolean values for all $a$ simultaneously. Use

$$
T=(\kappa+1)\cdot\sigma,\qquad
\Gamma=T\cdot(\kappa+1),\qquad
\iota(b,K,\theta)=T\cdot b+(\kappa+1)\cdot K+\theta.
$$

Every valid position with $\theta<b\le\kappa$ and $K<\sigma$ is below $\Gamma$; unused positions contain empty rows. Input queries for internal edges have upper endpoint below $b$. Output queries have upper endpoint at most $a$, and thus again below $b$. By (3.1), input queries at the virtual endpoint have a lower row, or the same row and a lower root. Every actual query is therefore strictly earlier.

Coordinate codes for finite diagrams and templates lie in $\omega$, row labels come from $\sigma^{<\omega}$, and labels come from $B$. All these sets already exist. If natural-number shape codes are needed, use the fixed surjection $e(\sigma,\cdot)$. Given a history, the next row in (4.1) is thus a subset of $\kappa+1$ specified by a **bounded formula**. Bounded Separation on the old history constructs that row. A bounded matrix verifies legal histories. Induction on stages gives uniqueness and compatibility on common initial segments. At limits, $\Sigma_1$-Collection collects shorter histories, and their compatible union is taken. This constructs all of $R$ without constructing a power set of all possible histories.

The following are consequences of (4.1), not additional axioms:

1. $R(K,\theta,a,b)\Rightarrow\theta\le a<b$.
2. If $\xi\le\theta$, every demand admissible at $(K,\xi)$ is admissible at $(K,\theta)$; hence root weakening holds.
3. The relation satisfies the finite reflection condition of Section 3.
4. If $H<K$, every template edge admissible at $H$ has row strictly below $K$. Thus reflection at $K$ meets every demand at $H$; provided $\eta\le a$, this gives (3.3).

Item 4 is particularly important: the property required for generated lower-row seams follows from the same relation. It requires neither a higher truth level nor stronger reflection.

## 5. Sufficient initial representations

### 5.1 An elementary ordinal initial segment of a set structure

Let $P(K,\theta,a)\iff R(K,\theta,a,\kappa)$, and take the finite-language set structure

$$
\mathcal A=(\kappa;<,R\upharpoonright\kappa,P,e,\omega,\sigma).
$$

Extend $e$ by the value $0$ when its second argument is not a natural number. The symbols $\omega,\sigma$ are constants of the structure. The relation $P$ separately records edges to $\kappa$, because $\kappa$ itself is not a member of the structure.

For any $\gamma<\kappa$, use the existing satisfaction set to choose the least ordinal witness for each existential formula and finite tuple of parameters, returning $0$ if no witness exists. All Skolem-operation graphs exist as boundedly defined subsets of $\omega\times\kappa^{<\omega}\times\kappa$. Let $H$ be the closure of $\omega\cup\{\omega,\sigma,\gamma\}$ under these operations and $e$. All initial constants and operation symbols can be coded in a countable language. Evaluating the finite closed terms gives exactly $H$. Certificates for finite term evaluation take values in $B$, so finite induction and bounded Separation construct the full evaluation graph. There is therefore an actual set surjection $\omega\twoheadrightarrow H$.

The witness criterion, proved by induction on formulas, gives $\mathcal A\upharpoonright H\prec\mathcal A$. If $0<\alpha\in H$, then every natural number belongs to $H$, and (2.1) together with closure gives $\alpha\subseteq H$. Thus $H$ is an ordinal $\delta\le\kappa$. It contains $\omega,\sigma,\gamma$, so

$$
\max(\omega,\sigma,\gamma)<\delta<\kappa,
\qquad\mathcal A\upharpoonright\delta\prec\mathcal A. \tag{5.1}
$$

The final strict inequality follows from the surjection onto $H$ and the uncountability of $\kappa$, not from regularity or a general collapse theorem. This is an elementary substructure of one fixed **set structure**, not reflection of the universe.

### 5.2 Endpoint agreement

For every height $\delta$ satisfying (5.1),

$$
P(K,\theta,a)\iff R(K,\theta,a,\delta)
\quad(K<\sigma,\ \theta\le a<\delta), \tag{5.2}
$$

and

$$
P(K,\theta,\delta)\quad(K<\sigma,\ \theta\le\delta). \tag{5.3}
$$

Prove (5.2) by ordinal induction on $(K,\theta)$, treating all $a$ simultaneously. If $a\le\omega$, the guards on both sides are false. If $P$ holds, replace the endpoint assumptions of a demand at $\delta$ by the corresponding $P$ assumptions, using the induction hypothesis. Reflection at $\kappa$ now applies. All output labels are below $a$ and all output-edge upper endpoints are at most $a$, so this remains an output at $\delta$.

For the converse, argue contrapositively. If $P$ fails, fix the shape, template, and cut of a finite counterexample. “There is a finite tuple of input labels satisfying the input conditions, but no output satisfying (3.2)” is a first-order formula in $\mathcal A$. Its only parameters are $a,\theta,\omega$ and the finitely many row labels and coordinates of that shape. Every row is below $\sigma<\delta$, and coordinates are natural numbers, so no parameter lies outside $\delta$. Elementarity gives a counterexample whose labels all lie below $\delta$. Convert its endpoint assumptions by the induction hypothesis. All candidate outputs still lie below $a$; the upper endpoints in the same $R$ queries are at most $a$, so the negated output condition is unchanged. This contradicts $R(K,\theta,a,\delta)$.

To prove (5.3), take a demand at $\kappa$ whose cut label is $\delta$. Fix only the labels $u$ before the cut. The finite formula “there is a representation $g$ with prefix $u$ and with the template's $P$ edges” is witnessed by the old representation, and all its parameters lie in $\delta$. Elementarity gives such a $g$ with every label below $\delta$. By (5.2), turn its $P$ edges into edges ending at $\delta$, obtaining exactly (3.2). The formula **does not** fix $g(c)=\delta$, and does not take $\theta$ as a parameter; thus it covers both $c=0$ and $\theta=\delta$. This completes the ordinal induction. Limit row labels do not require an additional truth layer.

### 5.3 Initial representations of finite graphs

If $\alpha<\beta$ both satisfy (5.1), apply (5.3) at $\alpha$ and then (5.2) at $\beta$ to obtain

$$
R(K,\theta,\alpha,\beta)\qquad(K<\sigma,\ \theta\le\alpha).
$$

For any finite valid graph of width $m$, finitely many applications of (5.1) produce $\delta_0<\cdots<\delta_{m-1}<\kappa$. Setting $f(i)=\delta_i$ gives a representation. This supplies initial representations for all finite graphs. Only a finite height sequence for each given $m$ is needed; no entire infinite sequence of heights must first be collected.

## 6. Actual descending ranks and descendant cones

### 6.1 Ranks with fixed row codes

Consider either a domain of natural-number-coded graphs, or a graph domain whose countable row set $X$ has been strictly embedded into $\sigma$ by a given set function. Let $A(G)$ denote the corresponding finite atomic graph. Define

$$
\mu(G)=
\begin{cases}
0,&G=0,\\
\min\{\beta<\kappa:\exists f\in B\ [\operatorname{Rep}(A(G),f)
\land f(|G|-1)=\beta]\},&G\ne0.
\end{cases} \tag{6.1}
$$

Section 5 guarantees that the set of candidates for the minimum is nonempty. Bounded Separation on the product of the graph-code set and $\kappa$ gives the entire function graph. This rank is not defined backwards from accessibility or from an unknown order type. Apply the actual copying lemma of Section 3 to a representation attaining the minimum. It yields

$$
G\ne0\Longrightarrow\mu(G[n])<\mu(G). \tag{6.2}
$$

For nonempty generation packages, use (3.3), already proved in Section 4. Empty outputs still give a strict decrease because $\mu(G)>\omega>0$. If a fixed row pool is used only for one descendant cone, restrict the domain of (6.1) to that cone. Below we prove that the row pool is closed under all those expansions, so the same function continues to satisfy (6.2).

### 6.2 From expansion ranks to ranks for actual column/sequence order

Write $D(G)$ for the finite-expansion descendants of $G$, including $G$. The relevant notations satisfy:

- Every one-step expansion of a nonzero expression strictly decreases actual comparison.
- $G[i]$ is a prefix of $G[j]$ whenever $i\le j$.
- Every prefix is reachable by repeatedly taking the zeroth fundamental-sequence entry.

Fix $G$ and a rank as in (6.2). Induction on $\mu(H)$, for descendants $H$, proves that any two descendants of $H$ are comparable by reachability. If one is $H$, this is immediate. Otherwise the two paths start at $H[i]$ and $H[j]$. Let $k=\max(i,j)$. By the prefix property, both endpoints lie in $D(H[k])$. Their common ancestor has strictly smaller rank, so the induction hypothesis applies. If two descendants satisfy $U<V$, only a nonempty path from $V$ to $U$ is possible; the reverse direction contradicts strict one-step decrease. Consequently

$$
U<V,\ U,V\in D(G)\quad\Longrightarrow\quad\mu(U)<\mu(V). \tag{6.3}
$$

Thus $\mu\upharpoonright D(G)$ strictly embeds the actual comparison order. For any nonempty subset, choose an element with least rank to obtain well-ordering of the entire descendant cone. Neither Dependent Choice nor a special property of some particular computational trajectory is used.

### 6.3 The initial-segment property of unions of seed cones

Suppose $A_n$ is a descendant of the next seed. Then the cones $D(A_n)$ are increasing. More importantly, they are **initial segments** in the union $U=\bigcup_nD(A_n)$. If $x\in D(A_n)$, $y\in U$, and $y<x$, choose a common larger seed ancestor. By Section 6.2, $x$ can expand to $y$, so $y\in D(A_n)$.

Given a nonempty set subset $W$ of $U$, take some $x\in W\cap D(A_n)$. Choose the least element $m$ of this nonempty intersection. Every element of $U$ below $m$ also lies in $D(A_n)$, so $m$ is the global least element of $W$. Adjoining a greatest element preserves well-ordering. This is not the false argument that an arbitrary increasing countable union of well-orders must be well-ordered.

## 7. Instantiations for Y, RPD, and LRD

**Y.** Take natural-number rows, $\sigma=\omega$, and use the actual mountain interface of Section 3.1. Sections 4–6 give a descending expansion rank for every legal Y expression; lexicographic well-ordering is asserted only for a single descendant cone and the standard domain. The upstream proved seed identity $E_1(1,n+2)=(1,n+1)$ makes the seeds a descendant chain, so Section 6.3 applies.

**RPD.** Again take $\sigma=\omega$. Generation packages are empty; root closure, control priority, column sorting, and actual copying are all instances of Section 3.2. No additional semantic property beyond (3.3) is required. Every valid column graph has an expansion rank (6.1), while the column order of standard graphs is handled by Section 6.2. The actual seeds satisfy $S_{n+1}[1]=S_n$, as stated in `RPDGeometry.seed_fs_one`. Section 6.3 therefore proves well-ordering of the actual standard domain, including the external top.

**LRD.** A normalized polynomial row $[a_0,\ldots,a_d]$ has the explicit ordinal code $\omega^d a_d+\cdots+\omega a_1+a_0$, and the special row `limit` is coded by $\omega^\omega$. Take $\sigma=\omega^\omega+1$. Natural-number codes for finite coefficient tuples, together with the special point, explicitly enumerate this ordinal; hence $\sigma<\kappa$. The abstract `Ordinal.type/typein` of the ordinary Lean backend is not used as evidence for this weak-theory fact.

After trailing high-degree zeroes are removed, actual comparison is exactly comparison of these ordinal codes. For a nonzero polynomial, let $j$ be its least nonzero degree. When $j=0$, the row approximation subtracts $1$. When $j>0$, replace the lowest occurrence of $\omega^j$ by $t+1$ copies of $\omega^{j-1}$: the actual ordinal sum is $\gamma+\omega^j(c-1)+\omega^{j-1}(t+1)$, strictly below the original row. The special row is approximated by $\omega^{t+1}<\omega^\omega$. Finite natural-number rows have empty packages; for other rows, the package consists of $0$ and approximations indexed from $0$ through $b$. Thus every package row is strictly lower. The actual fundamental-sequence operation preserves normalization; differently padded coefficient lists are not treated as distinct ordinal points. Sections 4–6 now prove well-ordering of the entire descendant cone of the original two-column LRD seed.

## 8. Ω-LRD3: Finite-origin induction retaining explicit ranks

Here a substantive step is required beyond merely changing the type of row labels. Keep the same $\kappa,e$ throughout. The induction does not demand any additional uncountable ordinal.

### 8.1 Finite syntax properties independent of well-ordering

Let $d(G)$ be the nesting depth of row labels. Each direct edge row $K$ satisfies $d(K)<d(G)$. A fundamental-sequence computation recursively invokes only the fundamental sequences of such $K$. Thus a single expansion is total, and $d(G[n])\le d(G)$. Actual expansion preserves normalization, valid coordinates, and standardness. The new direct row in a single-column seed is the preceding seed. Induction therefore shows that every direct row of a standard graph is also standard.

Comparison recursively compares only finite subtrees. Its strict-linear-order laws follow by induction on depth, not by following a fundamental-sequence chain. A separate depth induction proves $G[n]<G$ for every nonzero standard $G$. The control row $K$ has smaller depth. If $K$ is not a finite-number graph, then $0<K$ and, by the induction hypothesis, $K[t]<K$. Consequently the actual package

$$
P_b(K)=\varnothing\quad(K\text{ is a finite-number graph});\qquad
P_b(K)=\{0,K[0],\ldots,K[b]\}\quad(\text{otherwise})
$$

lies entirely below $K$. We may therefore apply the purely finite column-comparison lemma `GeneratedColumnDecrease.expand_lt`. This lemma uses only validity, normal form, linear-order laws, and decrease of package rows; it does not assume well-foundedness. The prefix property and deletion of the last column at index $0$ follow directly from the block definition.

### 8.2 An explicit ordinal encoding of a finite union

Suppose the nonempty subdomains $E_0,\ldots,E_{m-1}$ of a common strict linear order each have a set strict embedding $\mu_i:E_i\to\beta_i$, where $\beta_i<\kappa$. Let $X=\bigcup_{i<m}E_i$, and define

$$
c_i(x)=\sup\{\mu_i(z)+1:z\in E_i,\ z\le x\}. \tag{8.1}
$$

The supremum of the empty set is $0$, and $c_i(x)\le\beta_i$. These sets and function graphs are constructed from the given $\mu_i,E_i$ using bounded Separation and Union. If $x<y$, then $c_i(x)\le c_i(y)$ for each $i$. Choose $j$ such that $y\in E_j$. For $z\in E_j$ with $z\le x<y$, we have $\mu_j(z)<\mu_j(y)$, whence

$$
c_j(x)\le\mu_j(y)<\mu_j(y)+1\le c_j(y). \tag{8.2}
$$

Choose $2\le B<\kappa$ with $\beta_i<B$ for all $i$, and define the finite-digit code

$$
\rho(x)=\sum_{i=0}^{m-1}B^{m-1-i}\cdot c_i(x)<B^m. \tag{8.3}
$$

The sum is ordinal addition in increasing order of $i$. By induction from right to left, the tail after position $i$ is below $B^{m-1-i}$: if a digit $c$ is below $B$ and the next tail $t$ is below a weight $w$, then $w\cdot c+t<w\cdot(c+1)\le w\cdot B$. Comparing at the first differing position from the left, (8.2) gives $\rho(x)<\rho(y)$. The digit at that position is smaller on the left; the lower-position tail cannot overcome the difference, and the common higher-position prefix preserves the strict comparison. Section 2.3 gives $B^m<\kappa$. We have therefore obtained an **explicit ordinal embedding**, without invoking a general collapse of well-orders. Overlapping subdomains cause no difficulty: the various $\mu_i$ need not agree on their intersections, since (8.1) uses every coordinate simultaneously.

### 8.3 Depth induction retaining rank witnesses

The induction statement is that, for each standard finite $G$, there exists a set function

$$
\mu_G:D(G)\longrightarrow\kappa
$$

which strictly decreases at every nonzero one-step expansion and strictly preserves actual comparison on $D(G)$. The second conclusion follows from the first by Section 6.2. We do not merely induct on the statement “there is no infinite chain.”

Assume the result for standard graphs of depth less than $d$, and take $d(G)=d$. List the finitely many direct rows of $G$ as $K_1,\ldots,K_s$. They are standard and have smaller depth, so each has a rank witness as above. Every $D(K_i)$ has an explicit natural-number enumeration: enumerate all finite index paths and execute them according to the rules. Compose this enumeration with $\mu_{K_i}$ and apply (2.2) to obtain

$$
\beta_i=\sup\{\mu_{K_i}(z)+1:z\in D(K_i)\}<\kappa.
$$

Add $E_0=\{0\}$ with rank $0$, and set

$$
X_G=\{0\}\cup\bigcup_{i=1}^{s}D(K_i).
$$

Section 8.2 supplies $\rho_G:X_G\hookrightarrow\sigma_G$, where $0<\sigma_G<\kappa$, strictly preserving the same actual row comparison. With no direct rows, only the singleton $\{0\}$ remains and the same construction still works. There is no circular appeal to the depth-$d$ statement.

The pool $X_G$ is closed under row fundamental sequences. Zero stays fixed, and a child of any descendant of $K_i$ remains a descendant of $K_i$. The zero row and all children occurring in packages also lie in $X_G$. Thus throughout every outer expansion starting from $G$, every row remains in this **once-and-for-all fixed** pool $X_G$. A larger row domain is not chosen afresh during copying.

Use $\rho_G$ to put the row codes of all these diagrams and packages into $\sigma_G$. Define packages to be empty outside its image; inside the image, the bounded unique inverse of $\rho_G$ specifies the actual package. Section 8.1 and strict order preservation by $\rho_G$ ensure strict decrease of package row codes. Sections 4–6 now provide the actual set rank $\mu_G$ of (6.1) on all of $D(G)$. This closes the depth induction.

Only finitely many rank witnesses for direct rows are chosen at this step. **Finite** selection for an arbitrary formula follows by natural-number induction and Pairing/Union; full Collection is unnecessary. There is no need to collect “all ranks at all depths” into a set, or to collect a sequence of uncountable endpoints. Existence of one set rank for each individual cone is enough.

### 8.4 The standard domain and the actual external top

The actual Ω-LRD3 seeds satisfy $A_{n+1}[0]=A_n$: one deletion of a column suffices, unlike the two deletions in Ω-LRD2. Section 8.3 provides ranks for each $D(A_n)$, and Section 6.3 proves well-ordering of their union as an initial-segment chain. Finally adjoin the actual external top `Limit of Ω-LRD3`, whose $n$th fundamental-sequence entry remains the original $A_n$.

## 9. Removing $V=L$ and relating compressed code

### 9.1 Transfer actual ranks, not the assertion “$L$ regards this as a well-order”

The constructible hierarchy of ordinary KP gives an inner class $L$ satisfying the same KP and having the same ordinals and natural numbers. For this standard fact, see [Rathjen's discussion of ordinary KP and its constructible inner model](https://arxiv.org/html/1801.01897v1). This is neither “KP proves the existence of its own transitive set model” nor a conclusion about Power-KP, which includes Power Set.

To make the required axioms explicit: $\Delta_0$ formulas are absolute between transitive classes. Relativized Separation, Pairing, and Union are performed in a sufficiently large constructible level and its successor. If $a\in L$ and every $x\in a$ has in $L$ a witness $y$ satisfying a given $\Delta_0$ condition, then “there are such a $y$ and a constructible level containing it” is a $\Sigma_1$ condition. In the ambient KP, collect those witnesses and level indices. A larger level gives the entire set bound needed for Collection inside $L$. Apply full Set Induction to relativized formulas; transitivity of $L$ transfers it to $L$. This is class relativization carried out within an arbitrary object model and does not require its membership relation to be externally well-founded.

An ambient uncountable ordinal $\nu$ remains uncountable in $L$: otherwise a surjection in $L$ would also be a surjection in the ambient universe. Inside $L$, choose its least uncountable $\chi\le\nu$, and carry out Sections 2–8. For Y, RPD, and LRD this produces set-valued descending ranks on the corresponding actual coded domains. For Ω-LRD3, it produces one set rank $\mu_G$ for each fixed standard $G$; the entire family of ranks need not be transferred.

All finite syntax, finite index paths, fundamental-sequence computations, and comparisons have the same natural-number codes. Since $L$ and the ambient universe have the same natural numbers, finite computations are absolute, and their $D(G)$ and standard domains agree code by code. Because a rank function belongs to $L$, it is itself an actual set in the ambient universe. Statements that its values lie in $\chi$, or that a particular step has smaller rank, inspect only this set and ordinal comparison, and are therefore absolute as well.

Now work in the ambient universe. For any nonempty set subset, use these ranks to select a least element, as in Sections 6.2–6.3. Even subsets or potential descending chains that are not in $L$ are ruled out by the **same actual rank**. We do not need $\chi$ to remain uncountable in the ambient universe. This establishes the theorem of Section 1 in $S$ itself.

### 9.2 The encoding difference between the three current column expanders and Lean

The expanders use a maximum-root triple $(K,p,q)$ to compress roots $0,\ldots,q$. Lean's `Columns.normalizeColumn` explicitly lists every root, removes duplicates, and sorts. The representations are not byte-identical, but they have the following mathematical correspondence for all parameters.

Expand each compressed group into roots $q,q-1,\ldots,0$. A group with fixed $(p,K)$ occurs consecutively. When two columns are compared, if their first groups differ in $p$ or $K$, expanding the roots does not change the result. If $p,K$ agree but the maximum $q$ differs, the first root immediately decides the same result. If all three entries agree, the entire root group agrees and may be removed from both sides. Induction on the number of groups, followed by induction on row-nesting depth, proves agreement of compressed and explicit-root comparisons, and a bijection of normal forms.

Copying coordinate maps are monotone, so after root closure the maximum root is exactly the image of the maximum root. At an ordinary same-row seam, the maximum root is exactly $\min(f_b(q),f_b(r)-1)$, with a negative value indicating an empty group. Lower rows are not truncated in this way; higher-row groups are removed entirely. For a generated row, the maximum root is exactly $f_b(c)$. Consequently explicit-root copying, truncation, and closure agree with computing the maximum root directly and recompressing. Normalization removes repeated package members and groups copied redundantly into the old prefix; these do not alter the graph. Induction block by block now gives correspondence of actual expansion for every finite legal graph and every index, not merely for a collection of test examples.

The Ω-LRD3 Lean definition independently uses the package $\{0,K[0],\ldots,K[b]\}$ and the single-column seeds. It does not mix in Ω-LRD2's package through $b+1$ or its inserted empty column. The compression correspondence above is a mathematical encoding proof; we do not claim a formalization of a JavaScript interpreter or runtime protections. When a resource guard is triggered, the program throws an error rather than returning a truncated value of the mathematical fundamental sequence. Guards do not change the theorem's semantics for unbounded natural-number indices.

## 10. Dependencies, axiom ledger, and formalization boundaries

| Proof step | Principles used | Misuse specifically avoided |
| --- | --- | --- |
| Finite graphs, one expansion, comparison, finite path sets | Finite/natural-number induction; $\Delta_1$ graph construction | Iteration-to-zero searches do not replace proofs |
| Least uncountable ordinal | Class minimization from full Set Induction | No full Separation for the uncountability predicate |
| Uniform enumeration of all smaller ordinals | $\Delta_0$-Collection; bounded least selection inside $L$ | No Global Choice; internal and external well-ordering are not conflated |
| Entire $R$ table for a fixed $\sigma$ | Recursion along a given ordinal; $\Delta_0$-Separation; $\Sigma_1$-Collection | No added reflection; no power set of histories |
| Set satisfaction and Skolem-term closure | $\Delta_1$-Separation and finite computation graphs | No truth predicate for the universe, regularity, or general collapse |
| Endpoint agreement and initial representations | Ordinal induction; finite selection | All row parameters lie below fixed $\sigma<\delta$ |
| Finite column/mountain copying and last-label rank | Finite copying induction; bounded minimization | Rank is not defined from the well-foundedness being proved |
| LRD row codes | Explicit Cantor polynomials; finite/$\omega$ recursion | Abstract well-order types are not weak-theory evidence |
| Ω-LRD3 finite row pools | Bounded cuts, Union, finite ordinal operations, depth induction | No arbitrary countable union of well-orders; no assumption that the entire row domain is well-ordered |
| Transfer from $L$ | Inner-class relativization; absoluteness of finite computations and ordinal relations | Transfer actual ranks, not an internal assertion of well-ordering |
| Complete standard domains | Descendant reachability, initial-segment chains, least ranks | No use of Choice to construct descending chains |

Final exits in ordinary Lean:

- Y: `finite-demand/YFinal.lean`, with `OrdinalFormal.YFiniteDemand.generated_strictWellOrder` and `expansion_wellFounded`. It is **already connected to the same finite-demand backend**, not to the old truth-tower existence assumption.
- RPD: `finite-demand/RPDFinal.lean`, with `standard_strictWellOrder` and `standard_with_top_strictWellOrder`, plus an actual correspondence exit for the original finite-union definition.
- LRD: `finite-demand/LRDFinal.lean`, with `standard_isWellOrder`.
- Ω-LRD3: `omega3-audit/Final.lean`, with `standard_isWellOrder` and `with_top_isWellOrder`.

These final exits retain no assumption of reflection, initial representations, seed accessibility, or well-ordering of the entire row domain. Ordinary Lean permits `propext`, `Classical.choice`, and `Quot.sound`. These axiom reports do **not by themselves** establish the weak-theory upper bound of this paper. That bound comes from the itemized mathematical arguments above. This release does not contain a formal encoding of this metaproof as a derivation in the weak object theory.

No claim is made about minimal axiom strength, any equality or strict inequality involving a proof-theoretic ordinal (PTO), comparisons between the four order types, a new conclusion for Ω-LRD2, formal equivalence with the original Y JavaScript on its entire legal domain, or global column-order well-ordering of arbitrary hand-written raw graphs.

## References and release notes

- *A Short Proof of 1-Y Well-Ordering in KP with ω₁*: the user-supplied simplified manuscript, filename `1Y-Well-Ordering-KP-Simplified.pdf`. This is a source manuscript for the present route and is not redistributed in this release. Its SHA-256 is `0ed7392c03dc1ddb82c434f5ea3937116b1a59de6842f0d7b48445e1424a2eb9`. The route and extension steps used here are written out independently; readers do not need access to a file on the user's computer.
- [Zachiri McKenzie, arXiv:1806.08500, Section 2](https://arxiv.org/html/1806.08500v4#S2): derived KP principles, set satisfaction, and the constructible hierarchy.
- [Michael Rathjen, arXiv:1801.01897](https://arxiv.org/html/1801.01897v1): background on ordinary KP and its constructible inner model. Strengthened results for Power-KP are not invoked here.
- [Pinned upstream snapshot of 1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean/tree/1689b21131b488ec2ba2515bd630360371a2389d): the concrete finite Y mountain lemma of Section 3.1.

Lean module and theorem names in the text are inspection entry points; they do not imply that every path from the original working directory is unchanged. For corresponding release files and build instructions, see the [Lean project](../../lean/README.md).
