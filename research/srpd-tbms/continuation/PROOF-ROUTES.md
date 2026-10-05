# Proof architecture and intermediate results · [中文](PROOF-ROUTES.zh-CN.md)

[Current status](README.md). This guide organizes existing positive arguments; it does not discharge their historical premises or contribute a new comparison proof.

## 1. The shared logical framework

A persistent simulation must handle every source index n by a **nonempty finite native descent from the current target**, restoring the same contract for the source child and target endpoint. Well-founded rank induction then gives `ρ(source)≤ρ(target)`. A separate nonempty initialization descent supplies a strict inequality where applicable.

The strategy may keep archives, filler columns, and history-dependent choices. This does not automatically define a canonical order embedding. Conversely, an upper bound for a target expression must cover **all its native descendants**, not only the routes chosen by the forward simulator.

Truncation, ancestor exposure, and same-width D (`[1]`, then `[0]` back to the previous width) are macros for actual finite descents. A fast endpoint calculation or ancestor-DAG certificate does not make a macro a single fundamental-sequence step.

## 2. Lower bounds from reusable TBMS row banks

The [seven exact capacity cases](../archive/output/tbms-e0mn-bridge-20260925/FULL-REFLECTION-CAPACITY-INTERFACE.zh-CN.md) distinguish external points, same-copy transport, cross-copy transport, cuts, and seams. `Cap(p,q)` records the initial row interval on which p is an ancestor of q. Point transport and row transport have different boundary conventions.

### Finite banks and paid returns

A row label is represented by its entire native parent graph, not just a numerical height. All ordered representative pairs require background capacity, including source nonedges. Higher banks use cumulative endpoint codes already registered in lower banks, commonly archive address plus one.

Subcovariance is sufficient: smaller banks may remain in the old prefix while larger banks move. Their new codes must be bounded by transported old codes, not necessarily equal to them. A working column may inherit an archive entirely; the main source operation resumes by actual truncation to the healthy main area. Each call, return, and repeated use consumes genuine auxiliaries or prepaid coupons.

The [baseline reading route](../archive/README.md) supplies endpoint closure, native banks, recursive banks, and one-row returns in dependency order.

### Removing the infinite template: the D44 proof

The [finite-roof argument](papers/output/tbms-srpd-equalities-20260929/FINITE-ROOF-WHOLE-TBMS-LOWER.zh-CN.md) proceeds as follows.

1. Fix finite L in `T0=()`, `T_(d+1)=()(1^T_d)`. Recursive endpoint closure bounds all future endpoints of `T_(L+1)` at each level by the corresponding finite `T_(l+1)`.
2. Register those finite maxima once. Future demands are reached by genuine descents in finite banks; no infinite generating template is subsequently needed. Lower-level registration precedes higher-level registration.
3. `D44[n]` has a fixed six-column prefix followed by six-column blocks. Block b has `r_b=7+6b`, `h_b=8+6b`, and columns

   ```text
   [r_b-1], [r_b]^7, [r_b+1]^(h_b),
   [r_b,r_b], [r_b+3]^7, [r_b+4]^(h_b).
   ```

   Powers here repeat a parent within a column.
4. In `D44[2L+1]`, choose alternate-block bank representatives `u_l=11+12l`, `v_l=12+12l`. Their capacity `8+12l` pays the requirement `12l+3`. A private root `a=10+12L` and main height `K=8+12L` allow a genuine initialization and persistent simulation.

For each L this gives `ρ(T_(L+1))≤ρ(U_L)<ρ(D44)`. The supremum gives `TBMS Limit≤D44`, not a strict inequality.

Successful intermediate manuscripts retain useful interfaces: [main rows below the top endpoint](papers/output/tbms-srpd-equalities-20260929/PROPER-ROOF-WHOLE-TBMS-LOWER.zh-CN.md), [archive-only coupons](papers/output/tbms-srpd-equalities-20260929/ARCHIVE-ONLY-COUPONS-WHOLE-TBMS-LOWER.zh-CN.md), [delayed guards](papers/output/tbms-srpd-equalities-20260929/DELAYED-GUARDS-WHOLE-TBMS-LOWER.zh-CN.md), [contiguous main columns](papers/output/tbms-srpd-equalities-20260929/CONTIGUOUS-MAIN-WHOLE-TBMS-LOWER.zh-CN.md), and [weak one-row template returns](papers/output/tbms-srpd-equalities-20260929/WEAK-CEILING-WHOLE-TBMS-LOWER.zh-CN.md). These compress carriers; they do not prove equality with those carriers.

## 3. Reverse bounds and TBMS equalities

Every first child of `S(12484)` lies in a specific closed parent-graph class K. Lifting low-ancestor rows to finite ω bands preserves each parent's complete row interval. A persistent TBMS target gives the `B_(ω²)` upper bound; the second-order bank gives the reverse inequality.

Larger equalities use fresh frames, opened private graphs, and complete index forests. The current frame root contributes Q=ω², strict ancestral roots contribute ω, and component roots inside the index may contribute separate ω bands. External callbacks insert finite same-parent pieces absorbed by `δ+ω=ω` or `δ+Q=Q`; distinct parent boundaries must remain intact.

The [recursive-crown proof](papers/output/tbms-srpd-equalities-20260929/RECURSIVE-CROWN-OMEGA3-EQUALITY.zh-CN.md) recursively decomposes the index itself. Opened leaves retain the **same actual TBMS table** through transport. Its forest potential has the form

\[
V(v)=a_v\,\omega^{\sum_{w\text{ an ordered child}}V(w)}.
\]

Fresh-frame weights use epsilon enumerations above `Γ_m=ρ(B_(ω²m))`; index descent lowers those weights, and opening replaces a frame by a strictly smaller private-table rank. A TBMS context-with-a-hole argument proves the requisite absorption by higher Γ_m, rather than assuming a large ordinal absorbs everything.

After the first step of `J6[k]`, fresh depth is at most k−1 and opened depth at most k. Every first child therefore has rank below Γ_(k+1). Combined with multiple-Q-bank lower bounds, this gives `J6[k]=B_(ω²(k+1))`, then `J6=B_(ω³)` by cofinality. The fixed-depth argument does not yet cover `J7[2]` or the whole recursive TBMS limit.

## 4. Exact Y calibrations

The [Y134258 calibration](papers/output/y-tbms-epsilon0-20260927/Y134258-TBMS-OMEGA2.zh-CN.md) uses finitely many ω bands to retain shared high-tip contexts along finite owner chains. High steps transport all data; ordinary steps keep real return columns. Returning through tips must follow actual parent chains. Persistent simulations in both directions yield `Y134258=B_(ω²)` in rank.

Protected root substitution and prefix absorption then identify Y tails 3 and 4 with petal powers and power towers over β. On the SRPD side, relative offset-block cones, petal copying, and weighted-forest upper bounds yield the same values. Both arguments cover complete descendant cones.

Tail 5 has only prefix location and improved bounds: `Y1342585=Y12585`, and the SRPD upper bound improves from `U[7]` to `U[5]`, with `U=S(P,12,43)`. Its complete equal representative remains unknown. Different first children do not refute rank equality, but also do not prove it.

## 5. Progression of higher Y lower bounds

The source records ordinary parents, high parents, permanent root marks, tip colors, and owner sets. Initially, color-2 tips carry ordinary one-row forests with budgets below ε₀, yielding `Y1342589,11≤B_(ε₀)`.

Recursive components replace those simple bodies. Each initial child has finite port-nesting depth, preserved through copying. Lower-depth port ranks become available in higher recursive TBMS row universes. Together with the all-prefix capacity contract, this yields `Y13425810≤TBMS Limit`, without assuming equality.

Later source nodes contain private closed branches returned to the active workspace. The positive development has several distinct layers:

1. Fixed ports, exact pruning, closed roots, and finite nesting depth establish `Y(C)≤R`.
2. Actual self-indexed banks and reusable six-point parents improve `Y(C,6)` to a fixed I29 bound.
3. Persistent **Cap** (paying arbitrary strict requests over finite histories) is separated from completed **Val**. A completion lemma, not an initialization assumption, produces a completed value below R. The nearest completed upper value is checked again after preparation.
4. General control graphs, return trees, and feedback closure yield fixed I120 bounds for `Y(C,6,7,9)` and `Y(C,6,8)`.
5. Full type prefixes, coefficient graphs, row copies, working leaves, reset blocks, and generating grades extend the source classes, eventually reaching `Y(C,6,8,10,12,13,14)`.

For the last layer read [finite types](papers/output/srpd-limit-y-lower-20261001/FINITE-TYPED-CARRIER.zh-CN.md), [ordinary type graphs](papers/output/srpd-limit-y-lower-20261001/ORDINAL-TYPED-CARRIER.zh-CN.md), [finite blocks](papers/output/srpd-limit-y-lower-20261001/FINITE-BLOCK-CARRIER.zh-CN.md), [ordinary blocks](papers/output/srpd-limit-y-lower-20261001/ORDINAL-BLOCK-CARRIER.zh-CN.md), [multiple working leaves](papers/output/srpd-limit-y-lower-20261001/MULTIPLE-LIVE-LEAVES-BOUND.zh-CN.md), [three-level return heads](papers/output/srpd-limit-y-lower-20261001/THREE-LEVEL-CANOPY-BOUND.zh-CN.md), [finite choice strings](papers/output/srpd-limit-y-lower-20261001/FINITE-CHOICE-SHADOW-CARRIER.zh-CN.md), and [multiple generating ports](papers/output/srpd-limit-y-lower-20261001/STRONG-TIER-PRODUCT-CLOSURE.zh-CN.md). Their companion algebra papers are in the [catalogue](CATALOGUE.md).

These closure functions require their own definitions, finite-generation restrictions, and relative-background hypotheses. A displayed ψ is not an unconditional invocation of a standard literature OCF.

## 6. The conditional S9 induction

The [finite-structural-grade paper](papers/output/srpd-limit-y-lower-20261001/FINITE-STRUCTURAL-GRADE-CARRIER.zh-CN.md) explicitly assumes the capacity formulas, ordered registration, persistent completion, full type vectors, whole-inner-block generation, and finite-depth source lift. It separates three inductions:

- Finite **structural depth** constructs resource-generating geometry without evaluating that resource's own function.
- Pure closure handles explicitly finitely generated requests, not a countable cofinal sequence through an uncountable ordinal.
- The **whole outer-context measure** proves completion of ordinary outputs, with Cap-to-Val completion used only afterward.

Ordinary row endpoints are completed countable values. Declared structural grades are not ordinary row values. Entire ownership trees are copied, while port order within connected blocks remains strict. Ordinary inputs are prepared before the waiting outer frame; all physical addresses are reread after transport.

With U=ω₁ as the relative uncountable background, finite seeds have

\[
a_0=U^{U^U}\cdot2,\qquad
\delta_{d+1}=U^{\omega^{a_d}},\quad
\theta_{d+1}=U^{\delta_{d+1}},\quad
a_{d+1}=U^{\theta_{d+1}}.
\]

The a_d are cofinal in the first epsilon number above U. Each d has a finite layout of 25-wide slots, with `w0=8`, `w_(d+1)=9+2w_d`, and, under the historical interfaces, `Closed(a_d,λ_d)` with `λ_d<R`.

The source formula is

\[
S9[n]=Y(C,6,8,10,\ldots,6+2n).
\]

Each complete child requires a finitely generated index below some a_d, so has rank strictly below R. Taking the supremum yields only `S9≤R`. Different depths use different finite parents; there is no asserted single finite carrier or strict final inequality.

This remains a historical-premise-dependent paper argument. There is no complete all-depth compiler or independent review of the whole foundational chain. Finite prototypes do not prove the induction.

## 7. Useful local results beyond the whole-node bound

### SRPD blocks and event ranks

[Closed-block decomposition](papers/output/y-134258a-49141710-srpd-20260930/SRPD-COMPONENT-REDUCTION.zh-CN.md) and [strict growth](papers/output/y-134258a-49141710-srpd-20260930/SRPD-STRICT-GROWTH.zh-CN.md) give relative block ranks β_a with `β_a·ω<β_(a+1)` and `ρ(S(124842))=sup_a β_a`. The final 2 of that expression is not justified as merely multiplying a fixed block by ω.

[Y private-bank normal forms](papers/output/y-134258a-49141710-srpd-20260930/PRIVATE-BANK-NORMAL-FORM.zh-CN.md) retain marked kernels with exact index behavior. [Alternating event-rank reduction](papers/output/y-134258a-49141710-srpd-20260930/ALTERNATING-GRAFT-RETURN-RANK.zh-CN.md), under its calibration premises, separates continuous phases from returns needing additional payment. These reductions do not compare the two event trees yet.

### Local TBMS upper-bound protocols

[Sparse full-ancestor coverage](papers/output/tbms-srpd-equalities-20260929/SPARSE-COVER-AND-PORT-FUNDING.zh-CN.md) permits noncontiguous representatives and retained filler, and pays new tails from actual last-port capacity. [One-mark returns](papers/output/tbms-srpd-equalities-20260929/ONE-MARK-GENERAL-RETURN.zh-CN.md) and [elastic private stacks](papers/output/tbms-srpd-equalities-20260929/ELASTIC-PRIVATE-STACK.zh-CN.md) retain persistent TBMS tables and potentials for specified protocols. General opening, cross-module returns, and the whole `J7[2]` cone are not covered.

### The latest Y resource interfaces

For positive live root c of height h_c, take relevant owned source edges at rows r with represented target capacities A. Define

\[
P_c=\min A,\qquad E_c=\min(A-r+h_c-1),
\]

with empty minimum infinity. P is raw capacity; E subtracts the absolute row offset.

The [common-floor contract](papers/output/srpd-limit-y-lower-20261001/COMMON-FLOORS-AND-BOUNDED-HEIGHT-CALLS.zh-CN.md) uses one non-top gate g_s beyond all live natural owner depths, uniform reserve at least 2, and P_c>g_s for all roots. First-tip high steps and suitably paid second-tip steps restore this contract. Repeated body rows inherit old capacities; they cannot all be credited with top capacity Q.

[Maximal-row preparation and external controls](papers/output/srpd-limit-y-lower-20261001/MAXIMAL-HEIGHT-PUMPS-AND-EXTERNAL-ARCHIVES.zh-CN.md) give exact updates at cut c, row q, displacement Δ: old controls a<c retain reserve; old c gets q−1 and its last copy q; old a>c gets `min(ρ_a,q−1)`, while its last copy gets `f_c(ρ_a)`, where `f_c(x)=x` for x≤c and `x+Δ` otherwise. Exact bookkeeping is not a perpetual-supply theorem.

[Preallocated auxiliaries](papers/output/srpd-limit-y-lower-20261001/BUFFERED-PREPARATIONS-AND-ORDINARY-PHASES.zh-CN.md) start with k+2 auxiliaries. Each preparation consumes the last one; the others keep parents at or after working representative p and `Cap(p,z)=Q`. After k preparations, two remain for the original `C.step`. Read-only prefix views are not target mutations; actual truncations must be native `[0]` steps.

Given a uniform interior control `g<d<min(g_(s+1),P_c)` and, if needed, an exterior one `0<b<min(g0,β)`, amplification followed by copying at d can make every E_c≥g+1. During an ordinary step at control row t, a reattached row r<t satisfies

\[
q-1\ge E_c+t-h_c\ge E_c+r-h_c+1.
\]

Thus an entire ordinary/deletion phase preserves E and reserves without a per-step charge. **Control availability is a premise.** Its preservation through arbitrary high-phase alternation is still missing, so none of this upgrades S9 or proves B≤R.

## 8. The delivered mapping interfaces are different

The earlier `Y→M13` prototype has a [canonical strict-order argument](papers/output/y-m13-order-embedding-20260920/ORDER-EMBEDDING.zh-CN.md) on its explicitly smaller source domain, not on S9.

`M13≥Y` selects the largest available proved label and may repeat or skip labels; it is not an inverse embedding. `TBMS≤SRPD` descends persistently along a chosen history; its reseeded view constructs fresh covers independently. Neither claims a global history-independent order embedding. See [the viewer guide](EVIDENCE.md).
