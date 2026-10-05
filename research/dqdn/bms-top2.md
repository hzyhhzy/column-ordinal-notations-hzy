# BMS and the second DQDN layer · [中文版](bms-top2.zh-CN.md)

This is the English presentation of the paper comparison chain recorded on 2026-10-05. It is not an independently reviewed or Lean-certified result. The DQDN rules are unchanged. The conclusions claimed by the manuscript are

$$\sigma_4<\mathrm{PTO}(Z_2)\le |\mathrm{TOP}[2]|,
\qquad \lim(\mathrm{BMS})\le\mathrm{PTO}(Z_2)\le |\mathrm{TOP}[2]|.$$

Here BMS is Hunter's BM4, S_H is the two-column seed (0^H)(1^H), σ_H is the value of the seed, and its descendant cone including the seed has order type α_H=σ_H+1. The distinction matters for strict endpoints. These cones are nested and cofinal in standard BMS.

P₁=TOP[2] has count word `1,2,1,2`. Its new generator G(1) covers System F with native Nat, arbitrary permitted-result-type recursion and strict Q, using only kind `*`. It is not a free container for arbitrary higher-kind Fω programs.

## Fixed-height BMS in Z₂

Work first in ZFC minus Power Set, **with Collection**. H is an externally fixed positive integer. Let Λ be the constructible heights a for which L_a satisfies KPω.

In a transitive KPω set, the satisfaction relation of a named set structure is available and is Δ₁ in KP. This uses bounded assignments, recursion on formula complexity and collection of the countable recursion history, not a truth predicate for the ambient universe. See [Holy, §1.2, Lemma 1.19](https://www.dmg.tuwien.ac.at/holy/dip.pdf) and [Le Sueur, Corollary 2.13](https://ueaeprints.uea.ac.uk/id/eprint/65301/1/ext_diff_coanalytic_apal.pdf).

Consequently a fixed formula B(a,b,j) expresses guarded elementarity L_a≺Σ_j L_b between two named admissible structures, with complexity bounded independently of the numerical parameter j. By contrast, in ambient L_τ the unary formula U_j(a) expressing L_a≺Σ_j L_τ uses the j-th partial truth predicate and its complexity may grow with j. Replacing U_j by B(a,τ,j) would be invalid: τ is not an element of L_τ.

Choose a finite increasing sequence r(0),…,r(H−1) covering the complexity of B, guards, finite diagrams, and each preceding ambient U formula. Put

$$Q_k(a,b)\iff a,b\in\Lambda\ \land\ a<b\ \land\ L_a\prec_{\Sigma_{r(k)}}L_b.$$

These relations are transitive and nested by level. For each fixed finite complexity d, collect witnesses in the class L for a finite family Φ of partial-truth formulas and subformulas. Collection bounds their constructible levels. Iterating the uniquely defined least higher witness-closed level through ω and taking the supremum gives a Σ_d-correct constructible layer. The construction works above any prescribed bound. Include the finite characterization of KP for transitive sets in Φ, so satisfaction is used only after admissibility has been ensured. This avoids circularity and requires neither Power Set, arbitrary V-reflection nor class dependent choice.

Two sufficiently correct layers supply labels for S_H. To copy a finite diagram below an endpoint a of Q_t(a,b), internal edges and edges from an old prefix use B; edges into b at levels k<t use U_r(k). Their existential closure has complexity covered by r(t), so it reflects from L_b to L_a. The guards preserve the intended external meaning.

This is the finite-copy input to [Hunter, Lemma 2.5 and Theorem 2.7](https://arxiv.org/html/2307.04606v3). Retaining only H edge levels removes the need for the original all-level boundary. With initial upper label b fixed, all representations lie in the set (b+1)^{<ω}. Assign to a reachable matrix the least strict upper bound admitting such a representation. Separation and Replacement give an actual set function, not merely a class judged well-founded inside L. Copying strictly lowers this rank on expansion. Standard BM4 comparison agrees with finite expansion descent, so ZFC⁻ proves well-ordering of the fixed-height cone in the ambient sense.

For an explicitly primitive-recursive presentation, let e_H(p) evaluate a coded finite path from S_H and add a redundant parameter t. Put E_H(⟨p,t⟩)=e_H(p) and order all natural numbers by E_H lexicographically, breaking ties by their usual numerical order. Each fiber has type ω, so this primitive-recursive order has type ω·α_H. It avoids unboundedly enumerating the distinct standard matrices.

Its well-ordering is Π¹₁. [Montalbán–Shore, Proposition 1.4](https://pi.math.cornell.edu/~shore/papers/pdf/Delta4DetSub.pdf), transfers it from ZFC⁻ with Collection to Z₂. Adjoin one greatest element to obtain

$$\alpha_H\le\omega\alpha_H<\mathrm{PTO}(Z_2),
\qquad \sup_H\sigma_H=\lim(\mathrm{BMS})\le\mathrm{PTO}(Z_2).$$

This is an external H-indexed scheme, not one uniform Z₂ proof of all-height BMS well-ordering. No BMS=PTO(Z₂) conjecture is used.

## A parameter-preserving native Nat extraction

Let R be a primitive-recursive strict linear order whose well-ordering Z₂ proves. For an arbitrary total χ:ℕ→ℕ and starting point a, let L_R(a,χ) be the first failure among χ(0)Ra, χ(1)Rχ(0), …. The predicate F_R(χ,a,n) saying n is the first failure is uniquely witnessed and primitive recursive relative to χ.

Regard χ as a free function symbol, extending comprehension and induction to that language. Its graph is supplied by comprehension; the well-ordering proof gives ∀a∃n F_R(χ,a,n). The negative translation and Friedman's C-translation preserve this parameter and give the same Π⁰₂ assertion in HA₂(χ). For a fixed free a, take C=∃n F_R(χ,a,n). Decidability of F_R, the substitution lemma for comprehension and variable renaming give the usual double-negation removal. No choice or Markov principle is added. A reference for this proof transformation is [Mazza, Theorem 11.9 and Lemmas 11.4–11.6](https://www.lipn.fr/~mazza/teaching/ProofTheoryNotes.pdf).

The required realizability interpretation uses **native Nat**, avoiding a Church-numeral detour. A predicate variable X is assigned a type variable X:* and an arbitrary default term d_X:X. Formula types are

| Formula | Computational type |
| --- | --- |
| equality or falsity | Nat |
| X(t) | X |
| B→C | \|B\|→\|C\| |
| conjunction, disjunction | product, sum of the constituent types |
| ∀n B | Nat→\|B\| |
| ∃n B | Nat×\|B\| |
| ∀X B | ∀X:*. X→\|B\| |

Products and sums have ordinary System F encodings. Formula types do not depend on numerical variables. Defaults are defined structurally: zero at Nat, the given d_X at a predicate, constant functions at arrows, pairs or a left injection at products/sums, `(0,d_B)` for numerical existence, and `ΛX.λd_X.d_B` for predicate universality. Thus ex falso can be realized by a default function, with no invalid constant of type ∀X.X.

Defaults do **not** make formulas true. Fix arbitrary consistent χ in the metatheory and take closed terms modulo conversion. Assign to X any closed inhabited type σ, a chosen default d:σ, and any family 𝓧_n of sets of closed σ terms; these sets may all be empty. True equalities have every Nat term as a realizer; false equalities and falsity have none. Define the connectives, numerical quantifiers and predicate quantifiers by their usual realizability clauses. Predicate universality quantifies over all such types, defaults and families.

The substitution lemma interprets replacing X by B(n) using the type |B|, its default d_B and its family of realizers. Types do not depend on n, so this needs no dependent types. It covers arbitrary predicate substitution and hence full comprehension, not merely arithmetical comprehension. Logical rules use the corresponding lambda operations. True equations use zero, equality substitution ignores the proof, relative primitive recursion uses Nat/Rec/χ, and induction on B uses Rec_|B|. The empty realizer set handles negative arithmetic axioms.

Proof induction yields a term whose existential first projection returns the witness. Thus one finite proof gives

$$p:(\mathsf{Nat}\to\mathsf{Nat})\to\mathsf{Nat}\to\mathsf{Nat}$$

in System F+Nat+Rec, correct for **every** χ, even noncomputable ones. All quantified types have kind `*`. This is a mathematical extraction lemma, not an implemented general proof compiler.

Substitute the single strict-query function λx.Q(x) to form t_R,a. For a fixed consistent χ, typed normalization, confluence and Nat canonical forms identify its returned number with L_R(a,χ). The larger all-answer tree, including inconsistent repeated answers, is well-founded by the separate reducibility argument. The [Chinese companion](bms-top2.zh-CN.md) also retains a Church/default-value adapter check; it is not needed by this native route.

## Query rank and the generator

Compress finite deterministic segments of t_R,a into a query tree D. Its rank ρ(D) is at most the one-step source rank h(t_R,a). Sequentialize D with a cache of the initial segment of χ already read. A repeated query uses that cache; a new query reads through all skipped positions first. Well-founded induction on D gives

$$\rho(U)<\omega\cdot(\rho(D)+1).$$

Each node adds only a fixed finite reading segment before a strict child; the last ω absorbs that overhead. The cache is a proof construction, not a change to DQDN evaluation.

On a descending prefix that can continue, the first-failure functional is not constant: one can fail immediately or descend once more before failing. U cannot terminate at that prefix. Thus the finite R-descent tree embeds into U, including leaves at a minimum, giving

$$\operatorname{rank}_R(a)<\omega\cdot(h(t_{R,a})+1).$$

This does not assume sequential source queries; a program may ask far ahead.

The finite level-one typing derivation of t_R,a is generated by G(1). Selecting fuel and outputting the program take at least two source steps. With g=h(G(1)),

$$\operatorname{rank}_R(a)<\omega(h(t)+1)
\le\omega^{h(t)+1}<\omega^g\le |P_1|.$$

Earlier columns only strengthen this **lower** bound. If R has type α, use R plus a maximum whose rank is α. Taking the supremum over Z₂-provable primitive-recursive well-orders gives PTO(Z₂)≤|TOP[2]|, completing the paper comparison chain.

## Limits of the result

No equality with PTO(Z₂), internal Z₂ proof of whole BMS or TOP[2], index-preserving fundamental-sequence embedding, count-preserving map or actual smallest carrier index n is supplied. The finite [interface tests](code/test_system_f_oracle_bridge.py) check examples of default elimination, native recursion, strict queries and real level-one construction fields. They do not establish the general realizability lemma, conservativity application, or ordinal comparison. All these remain paper-level work subject to further audit.
