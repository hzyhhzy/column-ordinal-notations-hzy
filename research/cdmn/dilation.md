# CDMN finite simulation under uniform dilation · [中文版](dilation.zh-CN.md)

This manuscript preserves the **legacy hereditary-zero** strict-guard CDMN argument. In the simulation formulas below, `[0]` means the old one-column hereditary trim δ, not the current prefix-zero operation. The mathematical dilation transformation is unchanged. The final section transfers finite simulation to the current rule, without transferring the short macro or its length bound. This supplies a sufficient certificate for infinite descent, **not a proof that such a certificate exists on the standard domain and not a well-ordering proof**.

## Transformation

For integers d≥1 and b≥0, let $D=D_{d,b}$ place each graph's original columns at local positions 0,d,2d,…, inserting d−1 empty columns between consecutive originals, with no final padding. Recurse through all rows and replace every parent p by b+dp. Zero remains zero.

For an external context Γ, use $D^+\Gamma$, padding after every outer column including the last; rows still use unpadded D. Prepend any fixed legal context Λ of length b. A graph G legal over Γ then becomes DG legal over $\Lambda\mathbin{\|}D^+\Gamma$.

D is not a fundamental-sequence step and need not preserve standardness. For example, with d=2,b=0 it maps `[][0:1]` to the nonstandard `[][][0:1]`.

## Legacy-rule simulation theorem

If H=G[n] over Γ, then DG finitely expands to DH over $\Lambda\mathbin{\|}D^+\Gamma$ using the original CDMN rule. For nonzero G the path is nonempty and has at most2d−1 steps. It requires no reachability search or unknown ordinal rank.

Let δ be zero pruning and C count all nested column occurrences. If n=0 or G's last column is empty, use precisely

$$C(DG)-C(D\delta G)\in\{1,d\}$$

zero steps. One step suffices when the pruned local graph has a single column; otherwise d steps remove the original final empty column together with its interval padding. Removing an empty row wrapper costs no additional column.

Otherwise descend to the unique active control row R ending empty. Its parent and owner are c and m; let ℓ=m−c. The macro is

$$[0]^u[n][0]^{d-1},\qquad u=\begin{cases}d-1,&|R|>1,\\0,&|R|=1.\end{cases}$$

Here |R| is the outer width of R, not its literal size. Lift this same index sequence through the enclosing final-record spine.

## Active-step verification

Dilation preserves recursive lexicographic comparison and commutes with relocation. If φ adds ℓ at cut c, then

$$D(\phi U)=\phi'(DU),$$

where φ′ adds dℓ at cut b+dc. All threshold comparisons and the strict source filter are therefore preserved.

When R has a preceding column, DR is D(R⁻) followed by d empty columns, where R⁻ removes the last original column. The preparatory d−1 zero steps leave one of those empty columns; the subsequent [n] lowers precisely to D(R⁻). A singleton empty R requires no preparation.

The lowered shell, its maximum row and all accepted relocated source records are consequently the D-images of the original ones. If the original fixed block is

$$B=(Q)\mathbin{\|}\phi(C_{c+1},\ldots,C_{m-1}),$$

the transformed block is exactly $D^+B$: the original interval padding after source position c becomes the padding after the seam Q, and all middle columns carry their interval padding. The transformed block width is dℓ. Relocation commutation verifies every one of the n blocks.

The result is DH with d−1 extra empty columns at the end of the active graph. The final d−1 zero steps remove them. Before the unique positive step, preparation leaves the active record nonempty, so outer recursion still reaches the intended position. After it, all steps are zero and cannot accidentally trigger outer copying. This proves the lifted simulation and its uniform length bound.

## A sufficient closed-copy pump

Suppose a nonzero closed graph A has a nonempty actual path to B, and some contiguous column segment in B is D(A), with b equal to its actual starting address. All its references are at least b, so it reads no earlier external material.

Zero-prune everything after that occurrence to expose it on the final-record spine without altering it. Simulate A's path to B inside the copy. This yields a further dilated and relocated copy of A, allowing indefinite repetition. Every round has at least one step and leaves a nonzero A copy, hence gives an infinite expansion chain.

For lifting, replace any original step at an empty final column by index0; its result is unchanged and this avoids outer copying. Extra prefix context and enclosing wrappers therefore do not affect replay. If A has a verified standard-seed entrance, the chain is a standard-domain counterexample.

**No A and B meeting this condition have been found.** Infinite chains without such a finite self-replication certificate are not excluded.

## Transfer to the current prefix-zero rule

The [finite-properties paper, §2](../../proofs/paper/cdmn-properties.md#2-hereditary-trim-and-prefix-zero) gives two-way finite reachability simulation over every fixed legal context, using finite parent/row-size induction rather than global well-ordering. A current step can therefore be simulated by a finite legacy path. Apply the legacy dilation macro to each step of that path and then convert the resulting legacy path back to current steps. This proves the same **existence of a finite nonempty dilation simulation** for the current rule.

It does **not** prove the current path has at most `2d−1` steps or is the displayed zero-only macro. The legacy closed-copy pump criterion also transfers by finite simulation, but no standard closed-copy pump is known. Standardness must still be certified separately; dilation alone does not preserve it.

## Implementation checks

[dilation.cjs](dilation.cjs) implements the transformation. The historical **legacy-rule** full run checked17139 source steps, including7196 nonempty contexts, using49484 actual expansion steps, factors2–4 and nonzero translations, with no mismatch or budget stop. Its [saved result](historical/dilation-results.json) is not a replay under the current rule. The [packaged tests](../../tests/cdmn.cjs) now search for and replay actual current-rule witnesses within explicit budgets; unknown cases are reported separately in the [current receipt](../../tools/cdmn-validation.json). These bounded witnesses are not a verification of all cases of the transfer theorem.

These checks support implementation fidelity but do not replace the structural proof or establish global well-ordering.
