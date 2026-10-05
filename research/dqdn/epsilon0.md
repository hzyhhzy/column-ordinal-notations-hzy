# Two distinct DQDN calibrations at epsilon zero · [中文版](epsilon0.zh-CN.md)

There are two paper equalities to distinguish: an independent 21-column ordinary program diagram has value ε₀, and the common standard-domain boundary TOP[1], just two columns, has value ε₀. They are not the same raw string. Neither equality is a finite-test or Lean result.

## Stretching a query tree

For a closed typed Nat term, compress the finite deterministic demand-computation segments into a query tree of rank ρ(t). Write h(t) for the rank counting every source step. Then

$$\rho(t)\le h(t)<\omega\cdot(\rho(t)+1).$$

The proof is induction on the well-founded query tree. A leaf has finitely many deterministic steps. If l steps precede a query with children t_n, then h(t)=sup_n(h(t_n)+1)+l. By induction each child rank is below ω·ρ(t); taking their supremum and adding the finite l stays below ω·(ρ(t)+1). The finite segment length may vary between nodes; no global finite runtime bound is assumed.

## One finite program for a cofinal tower family

Let q=Q(0), J(x)=R(x,λk.λy.y,q) and F(f)(x)=R(x,λk.λy.fy,q). The [exact profiles](tower-profiles.md) show that the simple-type instances T_m have query rank θ_m, where θ₀=1 and θ_(m+1)=ω^{θ_m}. Their full ranks are below ε₀ and cofinal in it.

Let Z=λf.λx.x and use the polymorphic Church type C=∀A.(A→A)→A→A for the iterator. Define the ordinary erased macros

$$S=\lambda k.\lambda x.xF,\qquad E=(R(Z,S,q)\ J)\ 0.$$

The typed meaning of xF is `ΛA.x[A→A](F[A])`, so S:Nat→C→C and E:Nat. E's first demanded action is the query q. Answer n=0 gives three deterministic steps to zero. For n≥1 the child R(Z,S,n)J0 takes exactly 3n+3 deterministic steps to T_(n−1). Every child full rank is below ε₀ and these ranks are cofinal, so h(E)=ε₀.

The active column has weight ω^{ε₀}=ε₀, absorbing a finite data prefix and even the optional fixed ω prefix. `dqdn.epsilon_seed` uses 20 data nodes plus an active column, or 22 columns when preserving that ω prefix. [check_dqdn_seeds.py](code/check_dqdn_seeds.py) checks annotated typing, erasure and finite computation prefixes; it is not the all-n proof.

## Why the standard two-column boundary is epsilon zero

TOP[1]=P₀ contains the source G(0) for **all simple types**, not an ε₀ special case. The lower bound comes from the preceding finite simple-type tower programs generated with finite fuel.

For the upper bound, use [Xiao–Sun, Theorem 1.1](https://arxiv.org/html/2609.20369v1) for the designated System T dialogue trees. DQDN's contexts are exactly demand contexts: function head for application, numerical argument for S/Q, third argument for R, no reduction under lambda. Deterministic steps preserve the corresponding query tree; a demanded Q(k) is a query root with the continuation at each numeral. Higher-result-type recursion is interpreted pointwise. This is a strategy/tree correspondence, not merely equality of numerical output, and is not asserted for the older arbitrary-context LCDN/LQDN kernels.

Thus every fixed simple-type Nat source has full rank below ε₀ by stretching. At each fixed finite generation budget, the finitely many construction shapes and uniformly bounded type complexity give a bound below ε₀; numerical atoms range freely but only add finite iterations within those shapes. Taking all finite budgets and using the cofinal tower lower bound gives the generator rank ε₀. The column valuation then yields

$$\boxed{|\mathrm{TOP}[1]|=|(1,2)|=\varepsilon_0.}$$

The particular independent E calculation has its own tower-profile upper bound and does not require the uniform theorem for all System T programs. The global P₀ calculation does. This result supplies no short exact standard name for BHO, BO, or every naturally described ordinal.
