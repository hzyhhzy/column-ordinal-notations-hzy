# Bounded validation / 有限核验

Run from this directory:

    python -B tools/validate.py

The latest recorded output is [validation.json](validation.json). The collection's exact original-language Markdown inventory is separately pinned in [PUBLICATION_MANIFEST.json](PUBLICATION_MANIFEST.json) for the repository release checker. A PASS records these finite checks only:

- Every imported proof/kernel file matches its collected SHA-256.
- Local Markdown links resolve within this directory; no obsolete prescribed-input statement or machine-specific user path remains in the collected text.
- The pinned original IBLP code gives the exact six-row $R$, five-row $C$, and $C[n]=J^{n-1}(A)$ for $2\le n\le7$.
- Twenty-five small original $R[k][n]$ examples have the inspected Sat/direct-positive-mark invariants.
- Small one-row parent-table BMS examples agree with finite-forest evaluation and the original-BM4 / parent-display index shift.

Limits are 15 seconds in total, at most 400 original basic steps, 600 rows, 60,000 stored fields and input indices at most 7. One-row BMS examples use at most three columns, indices 1 or 2 in original BM4, at most 300 steps each, and at most 128-bit forest integers. The tested inputs are fixed small cases. No hierarchy target or large Laver table is evaluated, and no background process is launched.

The checks do not establish actual elementary-embedding semantics, transfinite well-founded induction, all-input source closure, hereditary type contracts, natural-mark transport, or the FGH inequalities. Those remain the paper proofs and explicit dependencies in the collection. These bounded Python checks remain distinct from the new Lean theorem; they make no external independent-referee claim.

## Lean verification / Lean 核验（2026-11-06）

The separate [Lean project](lean/README.md) proves the original numerical BM4 conditional bound `q(5) exists => q(5) > F_(lim(BMS)+omega+1)(3)`. Its [receipt](lean/verification/VERIFICATION.json) and [full log](lean/verification/build.txt) record a fresh 152-module kernel-checked build and the exact source hashes. This certifies the stated direct Lean theorem, not an internal ZFC derivation or the stronger archived paper claims. / 新增 Lean 工程认证原数值版 BM4 的上述条件下界；不另编码内部 ZFC 推导，也不认证旧文更强结论。

Rebuild from `lean/` with `python -B build.py --record`; use `python -B verify.py` to check the published receipt against the packaged sources without recompiling. The latter is an integrity check, not a replacement for kernel compilation. Each compiler uses one thread, at most 2048 MB and 60 seconds; timeouts terminate its own process tree.

## Edition notes

Original research files are read-only sources for this import. Supporting manuscripts retain their local conditions and historical withdrawal notices. Obsolete paragraphs about an arbitrarily prescribed input are omitted with source line ranges recorded in the manifest; the three publication papers prove the natural-input statements. This is an edited reading collection, not a claim that every imported historical line is a current theorem.

The untouched original IBLP kernel has SHA-256:

    b8ffa27818ba6104dbb8fd110581c9898930ebf29e00b2c50065b0bbf7a137a3

The code files have scoped Git attributes preserving their bytes across checkout platforms. Supporting Markdown uses GitHub dollar-delimited mathematics; original plaintext proof notes retain their textual mathematical notation.
