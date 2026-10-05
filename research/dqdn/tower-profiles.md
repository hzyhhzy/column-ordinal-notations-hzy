# Exact query ranks of finite towers · [中文版](tower-profiles.zh-CN.md)

This paper calculation gives exact ranks for one uniform program family. It is not a bound for every System T program and is not a Lean theorem. The family uses only the unchanged DQDN demand rules.

## Types and pointwise choice

Put A₀=Nat, A_(i+1)=A_i→A_i. Let V₀ consist of well-founded natural-number query trees, with leaf rank zero and query rank the supremum of child ranks plus one, and V_(i+1)=V_i→V_i. For a countable family u_n define C₀(u_n) by a query at zero followed by u_n, and C_(i+1)(u_n)(x)=C_i(u_n(x)). This is call-by-name pointwise choice, not eager evaluation of x or of a function before choosing it.

With q=Q(0), use the ordinary macros

$$J(x)=R(x,\lambda k.\lambda y.y,q),\qquad
F_i(f)(x)=R(x,\lambda k.\lambda y.fy,q),$$

where F_i is instantiated at A_i. Then J(d)=C₀(d,d,…) and F_i(f)=C_(i+1)(f⁰,f¹,…).

## Exact profiles

Define P₁(f,α), for α≥0, to mean ρ(f(d))=ρ(d)+α for every ground tree d. Define P₂(g,α), for α≥1, by: whenever δ>0 and P₁(f,δ), one has P₁(g(f),δα). For i≥3, define P_i(g,α), α≥1, by: whenever δ≥2 and P_(i−1)(f,δ), one has P_(i−1)(g(f),δ^α).

These are profiles on specific test families, not assigned ordinal values for all semantic higher-type objects. The lower bound δ≥2 is essential at exponentiation levels: at base 1, iteration would not strictly grow and a new query could fail to be absorbed.

If λ is a nonzero limit, all α_n<λ are cofinal in λ, and P_i(u_n,α_n), then P_i(C_i(u_n),λ). At level one this is

$$\rho(C_1(u_n)(d))=\sup_n(\rho(d)+\alpha_n+1)=\rho(d)+\lambda.$$

At level two use δα_n cofinal in δλ; at higher levels use δ^{α_n} cofinal in δ^λ. The stated lower bounds on δ ensure strict growth. Thus the pointwise choice lemma holds at each level.

Finite iteration of a profile δ at level one has profile δ·n. At levels i≥2 it has profile δ^n, including the identity profile 1 for n=0. These statements use associativity of multiplication, and (ε^a)^b=ε^(ab) at the higher levels. All compositions are between objects of the same semantic type.

## Tower calculation

J has profile P₁(J,1). The preceding lemmas give

$$P_2(F_0,\omega),\qquad P_{i+2}(F_i,\omega)\quad(i\ge1).$$

For the first equation the finite profiles δn approach δω; for the latter they approach δ^ω. All chosen children are already well-founded semantic values, so the definition does not presuppose the normalization theorem it is intended to illustrate.

Let θ₀=1, θ_(m+1)=ω^{θ_m}, and

$$T_0=J0,\qquad T_m=F_{m-1}\cdots F_1F_0J0\quad(m\ge1).$$

Successive profile applications from the left replace the parameter β by ω^β, and the last P₂ application to J gives 1·θ_m. Hence

$$\boxed{\rho(T_m)=\theta_m.}$$

The first ranks are 1, ω, ω^ω, ω^(ω^ω). They arise from one macro at different finite simple types, not from separate ordinal-specific rules.

Each deterministic segment is finite by ordinary System T normalization. The [stretching lemma](epsilon0.md) gives

$$\theta_m\le h(T_m)<\omega\cdot(\theta_m+1)<\varepsilon_0.$$

The warmed-up polymorphic source that first queries m and selects this tower family therefore has full source rank ε₀. Its independent 21-column diagram also has value ε₀. Identifying it with a specific TOP-standard carrier requires a separate prefix analysis; the short independent graph is not automatically a short public name.
