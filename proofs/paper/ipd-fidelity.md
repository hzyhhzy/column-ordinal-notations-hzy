# IPD definition correspondence and verification · [中文版](ipd-fidelity.zh-CN.md)

2026-09-14. The object is the current zero-start IPD. The proof does not change the notation, define its domain after the fact by accessibility, or assume reflection supply.

## 1. Fixed versions and conclusions

The mathematical reference is [ipd.py](../../notations/IPD/ipd.py); its browser implementation is [IPD.ne-rewritten.js](../../notations/IPD/IPD.ne-rewritten.js). Neither was changed for this proof or packaging.

| File | SHA-256 |
| --- | --- |
| `ipd.py` | `12D3F08FD38FC51AA78B9972BAE2D5E02FC8EFC09DE085A9B1752880948EBAB1` |
| `IPD.ne-rewritten.js` | `ACC1A1C2AE260DA9BE7D13E14AC17D84A92679F82EFE97AA85CD0E3B072F6011` |

The [Lean project](../../lean/README.md) contains the mathematical definitions and proofs. [IPDStandardOrder.lean](../../lean/IPD/src/IPDStandardOrder.lean) concludes:

```lean
IPD.standard_wellFounded : WellFounded IPD.StandardLt
IPD.standard_total : ∀ a b, a = b ∨ IPD.StandardLt a b ∨ IPD.StandardLt b a
IPD.term_wellFounded : WellFounded IPD.TermLt
```

`Standard G` means exactly finite reachability from some actual `seed n` by actual `expand`. Its definition includes no `Acc`, well-foundedness, semantic representability or proof certificate. `StandardLt` is the actual column-list lexicographic relation; `TermLt` adjoins a greatest TOP.

Additionally `IPD.Semantics.valid_step_wellFounded` covers strict fundamental-sequence expansion on every structurally valid auxiliary graph. This is **not** global column-order well-ordering on all hand-written valid graphs.

## 2. Constructor-by-constructor encodings

A column is a finite edge list. An edge with parent p and profile (d,t) is `(p,(d,t))` in Python, `[p,d,t]` in JS and `Edge.mk p ⟨d,t⟩` in Lean.

| Object | Python | JS shared pool | Lean |
| --- | --- | --- | --- |
| Level-zero ROOT/SELF address | Natural integer | Natural integer | `Layer Nat 0` |
| Positive-level zero tree | `()` | ID 0 | `Tree.zero` |
| CAP head | `-1` | `-1` | `WithTop.top` |
| Ordinary head | Lower-level tree | Lower-level tree ID | `WithTop.coe` |
| Nonzero tree | `(head,children)` | ID from `make(d,head,children)` | `Tree.node head children` |

Decode shared nodes along their established finite structures. Node IDs do not order nonzero trees. Interning keys include level, head and the ordered child IDs, so identical structures share IDs. Different-level zeros, ROOT0 and CAP remain distinguished by the current type.

The executable edge validity condition is Lean's `Edge.Valid j`: $p<j$, with every base reference i satisfying $i\le p$ or i=j. Checking enters ordinary heads and every child. Canonical columns have decreasing unique parents and maximum profiles.

Thus canonical valid constructor data admit direct recursive translations in both directions. Sharing, caching and input repetition abbreviations leave decoded values unchanged. The domain here is finite legal constructor data, not arbitrary dynamically typed Python or browser objects.

## 3. Comparison

The branch order agrees: equality, zero, left-child shielding, right-child shielding, head, arity, first unequal child. Lean's `Tree.cmp_node_rule` proves this actual recursive equation for the mathematical LPO order.

Ordinary-head comparison lowers the level; child comparison enters a proper subtree. The finite branch equation therefore uniquely determines the reference result. Profiles compare level first. Graphs compare columns left to right, with parent before profile inside each column and proper-prefix tie breaking.

Controller selection is distinct: profile first, parent second. `controller_max` verifies that priority; the proof does not use the column priority in its place.

## 4. Lowering and JS pruning

Lean's `Tree.lower` processes every original child and returns `none` at zero, matching Python's skipping of zero children. A nonzero positive-level child cannot return `none`, by `Tree.lower_none_iff`, so no Python replacement candidate unexpectedly contains `None`.

Internal seeds, CAP replacement heads, recursive ordinary-head lowering, initial maxima, smaller-arity and smaller-head candidates, every original-head replacement position, and exactly n+1 closure rounds agree with Python. The recursive `replacements` list enumerates

$$
(a_0,\ldots,a_{i-1},u_i,M,\ldots,M),
$$

not recursive lowering of new terms. Cross-level minima move to a lower-level seed; the bottom-level minimum deletes the edge.

JS keeps the rightmost non-final nonzero position and the final nonzero position. [Section 10 of the paper](ipd-well-ordering.md#10-python-and-ner-correspondence) proves exact equality: M bounds every original child; a right non-final candidate contains M as a proper child and dominates all earlier candidates. The final candidate may lack M and must be retained separately.

This applies to every finite legal tree, not just tested samples. Induction on the original tree, level and rounds gives equal recursive values and equal maxima. Lean directly formalizes the all-position algorithm. The source correspondence and pruning argument are paper semantic proofs, not a formal certification of JS VM instructions, interning or browser execution.

## 5. Normalization and expansion

Python/JS dictionary normalization and Lean insertion normalization satisfy the same unique specification: exactly the input parent set, its maximum input profile at each parent, and decreasing parents. Insertion checks this by placing a larger parent before a smaller one, taking the maximum at an equal parent, or recursively passing a larger existing parent. List induction proves the specification. The dictionary takes the same per-parent maxima independently. Profile totality and unique parents make the specification unique; equal maxima are the same tree structure, not unspecified representatives.

Let x be the last column, c the controller parent and $L=x-c$, with $\phi_b(i)=i$ below c and $i+bL$ otherwise. The loop/block correspondence is:

- Source copy zero gives `G.take x`, unchanged on canonical input.
- Lean's new block b is the program's source copy b+1 of columns c through x−1.
- Its first column, x+bL, also receives seam b. The program inserts the seam before the source; Lean lists source before seam. Unique normalization makes these identical.
- Both relocate the entire profile before lowering controller-parent edges using the moved parent, moved SELF and block number b.
- Both output x+nL columns. Index zero and empty last columns delete the last column; zero stays zero.

This is a correspondence for every finite n, independent of subsequent termination. `IPDGraphGeometry` and `IPDSpliceLabels` check relocation composition. `IPDStageSplice` handles all old, source and seam edges of the whole result.

Both seeds are two-column minimum-level profiles; `seed_succ_one` proves $A_{n+1}[1]=A_n$, and TOP[n]=$A_n$. Induction on finite paths therefore identifies the three implementations' standard domains.

## 6. Dependencies and explicit nonclaims

The chain is: actual profile well-foundedness, actual finite-demand recursion, actual least Bad/Ext witnesses, countable downward closure, endpoint agreement, initial supply, whole-expansion last-label decrease, expansion well-foundedness, and standard column-order well-ordering.

Final Lean reports use only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`, custom well-ordering/reflection axiom or large-cardinal axiom. Every intermediate interface premise is instantiated by proved results. Generic closure, ordinal-height and reachability modules are reused, but no Y or ARD well-ordering theorem stands in for IPD.

The paper upper bound is $KP_\omega+\text{there exists an uncountable ordinal}$ with full set induction. [Section 12](ipd-well-ordering.md#12-explicit-witness-closure-matching-lean) gives the witness-closure route matching Lean. This bound is not encoded internally and is not inferred from Lean's axiom reports.

No relative strength inequality, optimal axiom bound, PTO comparison or fundamental-sequence cofinality is established here. Counts, drawing and their optimizations do not enter mathematical terms or column comparison. An FS budget exception does not return a truncated term. Finite hardware feasibility is distinct from the unbounded natural-number definition. Historical comments in frozen files are superseded by the paper and release validation.

## 7. Verification record

The original research verification rebuilt all 40 IPD modules from source in 424.91 seconds and checked 117 axiom reports. The release integrates them into its own complete source closure. Filenames gain the `IPD` prefix to match their existing imports; mathematical definitions are unchanged. Original and release LF-normalized hashes are recorded in [sources.json](../../lean/sources.json).

The publication rebuild status is in the [Lean instructions](../../lean/README.md) and [verification receipt](../../lean/VERIFICATION.json). The verifier runs sequentially, with a 120-second timeout and 2048 MiB limit per compiler, cleaning its own process trees. Finite example testing is not a well-ordering proof.
