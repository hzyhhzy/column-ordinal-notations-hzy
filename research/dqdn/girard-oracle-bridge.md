# From Zω proofs to DQDN query ranks · [中文版](girard-oracle-bridge.zh-CN.md)

This manuscript records the parameter-preserving functional-interpretation interface behind the paper claim lim(DQDN)≥PTO(Zω). Here Zω is the union of finite-order full-comprehension arithmetics, without arbitrary higher-order choice. Merely extending numerical terms to finite function types, as in System T, would not give this theory.

The relevant sources are [Girard's thesis](https://girard.perso.math.cnrs.fr/These.pdf), its default-value elimination appendix IV.A and free-parameter treatment in V.1, and [Avigad–Feferman, §10](https://math.stanford.edu/~feferman/papers/dialectica.pdf). PTO is the supremum of the order types of provably well-ordered primitive-recursive presentations; see [Walsh, Definition 1.1](https://arxiv.org/html/2209.09765v2).

## The required extraction statement

For a primitive-recursive strict order R whose well-ordering is provable in Zω, consider the first failure of a putative descent χ from a starting point a. Its index n is specified by a predicate F_R(a,χ,n) primitive recursive relative to χ. Well-ordering gives ∀χ∀a∃n F_R(a,χ,n).

Apply the negative translation and functional interpretation while retaining the **same free function parameter** χ:Nat→Nat. The resulting finite polymorphic term p(χ,a) returns a correct failure index, or an upper bound from which the least index is found by bounded search. Only a numerical witness is extracted. A concrete proof uses finitely many logical orders and therefore only finitely many kind levels.

This cannot be justified merely by citing the unparameterized numerical-function representation theorem. It requires uniform correctness for arbitrary χ, not a separate program chosen after fixing each oracle. The paper applies the standard interpretation with these interfaces explicit; no general proof-to-program implementation or Lean translation is included.

## Eliminating default constants

Some presentations of the interpretation use a default at every type. They are not immediately the pure target calculus. In modern Fω notation, define default evidence by

$$D_*(X)=X,\qquad
D_{\kappa\to\lambda}(F)=\forall X:\kappa.\ D_\kappa(X)\to D_\lambda(FX).$$

Preserve Nat, arrow, type lambda and application, and translate universality as

$$ (\forall X:\kappa.\sigma)^*
=\forall X:\kappa.\ D_\kappa(X)\to\sigma^*.$$

Every free type variable now has its evidence variable d_X. Defaults are obtained structurally: zero at Nat, a constant default function at an arrow, d_X at a variable, an extra evidence abstraction at a quantified type/type operator, and `d_F[A*](d_A)` at application. Products use pairs.

If existential types with default constants are translated directly, the correct package is

$$ (\exists X:\kappa.\sigma)^*
=\exists X:\kappa.\bigl(D_\kappa(X)\times\sigma^*\bigr).$$

Unpacking must also bind the hidden default evidence. Omitting it is a real scoping error. A constant Nat operator supplies an inhabited default witness of each finite kind; products and existential types can subsequently be eliminated by ordinary polymorphic encodings. The numerical/free function interface stays native Nat. These modern formulas explicate an implementation choice; they are not presented as verbatim formulas from the thesis.

## Strict demand queries

The Chinese manuscript retains an older full-context LQDN discussion for comparison. Current DQDN uses Q(t), which first evaluates its index to a numeral. Substituting λx.Q(x) for χ therefore gives the required strict oracle strategy directly under demand evaluation. It does not erase the index and rely on a different reduction strategy to read it later.

All-answer reducibility permits arbitrary numeral results, including inconsistent repeated answers. Hence the resulting whole source tree is well-founded. Compressing deterministic segments yields a query tree D with ρ(D)≤h(t). The [sequentialization argument](bms-top2.md) then gives

$$\operatorname{rank}_R(a)<\omega\cdot(\rho(D)+1)
\le\omega\cdot(h(t)+1).$$

Wrapping t as t⁺=(λx.x)t gives exactly one demand step and h(t⁺)=h(t)+1. Thus

$$\omega\cdot(h(t)+1)\le\omega^{h(t)+1}=\omega^{h(t^+)}.$$

This converts a correct first-failure functional into a genuine ordinal lower bound, not merely a large numerical runtime.

## Coverage by the actual generator

Every extracted program has a finite kind bound and a finite typing derivation. The incremental generator constructs that derivation and its contexts in dependency order; type beta/eta conversion is resolved into finite local steps. With enough finite fuel, some G(k) branch outputs the program. No completeness claim for an obsolete whole-certificate enumerator is substituted here.

The active-column weight, generator steps and preceding prefix cover the displayed bound. Adjoining a maximum to R gives a point of rank equal to its order type. Taking the supremum over all Zω-provable primitive-recursive well-orders yields the paper conclusion

$$\boxed{\lim(\mathrm{DQDN})\ge\mathrm{PTO}(Z_\omega).}$$

Missing work remains: a complete executable extraction chain, machine proofs for the type kernel and its coverage, and the [reverse PTO bound](upper-bound-open.md). This does not establish a short exact name for every naturally described large ordinal, or prove that each fixed generator is internally well-founded in a specified finite-order fragment.
