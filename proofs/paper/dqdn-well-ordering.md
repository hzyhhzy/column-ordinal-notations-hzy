# DQDN standard-domain well-ordering · [中文版](dqdn-well-ordering.zh-CN.md)

This paper argument concerns the incremental-generator [definition](../../notations/DQDN/definition.md), including its fixed common TOP. It does **not** assert well-ordering of every raw graph accepted by the internal evaluator. It collects the existing proof route; packaging and finite replay are not independent mathematical review or Lean certification.

The argument is given in ordinary set-theoretic mathematics. No optimized weak-theory bound is established here; in particular the weak-KP bound for RPD/ARD is not inherited just because these systems share a column presentation.

## Typed source trees

Use the implicit typing judgment Δ;Γ⊢e:A for the erased program. Universal introduction and elimination alter its typing derivation, not its runtime syntax. Type conversion is backed by a finite, kind-correct beta/eta derivation. This avoids assuming that each erased step corresponds to exactly one explicitly typed step.

Extend the usual reducibility-candidate proof for Fω with native Nat and recursion by the reductions Q(n)→m for **every** natural m. Candidate closure for neutral terms quantifies over all immediate successors. Numerals are computable at Nat; well-founded induction on computation of the argument establishes the query case. The usual recursion computability lemma handles arbitrary permitted result types. Induction on the typing derivation then proves strong normalization for the entire extended relation, and hence for its demand subrelation.

This is a genuinely all-answer statement. A different occurrence of the same query may receive a different answer. Termination separately for each fixed, consistent oracle would not suffice. Nor does a countably branching well-founded tree need a finite uniform bound on the lengths of its paths.

To pass to the actual immutable DAG implementation, unfold it into an occurrence tree as a proof device. Demand selects one occurrence. Rebuilding precisely its path to the root implements one tree contraction and leaves all other occurrences unchanged. Capture-avoiding substitution caches include binding depth. A DAG infinite computation would therefore induce an erased typed-tree infinite computation. The implementation does not materialize this unfolded tree.

## Generator preservation and termination

The fixed initial library consists of correct judgments. Each of the 28 local rules preserves its judgment and level bound. Application checks its argument type; recursion checks the index and step types. Generalization and eta contraction enforce the necessary non-occurrence conditions. An inapplicable construction ends its branch rather than admitting an invalid judgment.

Every B step decreases a fixed finite fuel counter. At zero fuel it selects a closed Nat judgment, or zero. The ordinary term grammar has no generator node; library traversal cannot import arbitrary neighbouring columns. Thus no program can return to G/B and refill fuel. Every G(k) tree is well-founded: a branch first chooses a finite fuel value, then makes finitely many construction steps, then enters an all-answer typed program tree.

The generator also covers every finite derivation at its permitted level. Arrange its dependencies in order, explicitly constructing contexts and local conversions. Repeating a finite derivation in an extended context supplies weakening when needed. With sufficient finite fuel, that closed program is an output. This coverage is used for strength comparisons, not for the preceding termination argument.

## An ordinal assignment

For a well-founded source s put

$$h(s)=\sup\{h(t)+1:s\longrightarrow t\}.$$

A stopped source has rank zero and is not represented by an active column. Give each data column weight 1 and each active column pointing to s weight ω^{h(s)}. For a finite expression A, let v(A) be the ordinal sum of its column weights in their original order.

Deleting a final data column strictly decreases v. Expanding an active column replaces ω^{h(s)} by finitely many data nodes and active children with ranks strictly below h(s). Since h(s)>0 and ω^{h(s)} is additively principal, this finite sum is strictly smaller. Earlier columns are unchanged. Therefore v(A[n])<v(A) for every nonzero ordinary standard A.

Fair repetition of every child gives cofinality. If the child-rank supremum is limit, child exponents approach it; if the supremum is a successor attained by a child, infinitely many repetitions supply the next power of ω. In the rank-one case arbitrarily many finite data blocks have supremum ω. Consequently

$$v(A)=\sup_n v(A[n])$$

for a limit A, with the expected predecessor equation for a successor. TOP is assigned sup_k v(P_k). Its finite roots are nested prefixes with further positive columns, so each is strictly below TOP and the same equation holds there.

## Why this also proves lexicographic well-ordering

Descent of individual fundamental-sequence steps alone would not establish the claim about the entire lexicographic order. The common-root condition supplies the additional argument.

Starting at TOP, all children of an active prefix are nested prefixes of one deterministic infinite block stream. To reach a given finite standard target, take the smallest child whose count word still covers the target, then delete or refine its last unsettled column. The first differing count must be 1 at the target and 2 at the active prefix. Each successful refinement fixes another target column; if the target is a prefix, only deletions remain.

This reconstructs the tagged columns uniquely from the count word. If B<A are standard, the same first-difference argument, starting with their common construction, gives a nonempty finite sequence of expansions and deletions from A to B. Hence v(B)<v(A). An infinite lexicographic descent would give an infinite ordinal descent, which is impossible. Cofinality and the successor equations identify v with the actual standard order type, not merely a convenient upper bound.

## What the conclusion does and does not cover

The conclusion is whole standard-domain well-ordering. It is not a claim that the system has a non-well-founded part above ω₁^CK. For example the raw untyped graph

```text
[v(0)][a(0,0)][l(1)][a(2,2)][run(3)]
```

represents ΔΔ. Repeated [1] expands its count word from 11112 to 111112 and so on, giving a genuine raw-graph descent. All these expressions are outside the TOP-standard domain.

The [Zω lower-bound manuscript](../../research/dqdn/girard-oracle-bridge.md) and [BMS comparison](../../research/dqdn/bms-top2.md) add separate extraction and rank arguments. They are not consequences merely of normalization. The exact global PTO equality remains [open](../../research/dqdn/upper-bound-open.md).

Missing machine-checked work includes the general type-kernel preservation and completeness lemmas, all-answer reducibility, the DAG/tree substitution bridge, and the standard-domain order theorem. Bounded tests exercise these interfaces, including negative controls, but cannot replace them. No `lean/DQDN` target, `sorry`-based certificate, or change to another notation's proof project is included.
