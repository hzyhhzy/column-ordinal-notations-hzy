# Fixed-row BMS upper bounds for BTnSS · [中文](README.zh-CN.md)

For every finite $n\ge2$, the collected paper gives an order embedding of the entire standard **strong BT*(-1)Y-nSS v2** domain below one fixed standard BMS term. Put

$$
B_r=(0^r)(1^r),\qquad U_r=(0^r)(1^r)(2^r)(3^r).
$$

Then

$$
\boxed{\lim(\mathrm{BTnSS})\le |U_{n+1}|<|B_{n+2}|.}
$$

The endpoint $|B_{n+2}|$ is the supremum of **standard $(n+1)$-row BMS**. The intermediate ceiling is uniform over all source seeds, nesting depths and term sizes: $U_{n+1}=B_{n+2}[3]$ under the frozen short fundamental sequence.

This is a self-reviewed **paper proof**, not a Lean theorem or independent referee certification. It does not assert equality, an initial image, or commutation of equally indexed fundamental sequences. The comparison uses the finite BTnSS invariants and Hunter's BMS well-ordering theorem; the older I3/almost-2-huge model interpretation of BTnSS is not a premise. No minimal axiomatic theory is claimed here.

## Reading the proof

- [Full English main paper](upper-bound.md) · [中文主证明](upper-bound.zh-CN.md).
- [Frozen definitions and finite invariants](source-finite/definitions-and-invariants.zh-CN.md): the retained sections 1–3 of the earlier BTnSS paper, with 18 supporting finite-combinatorial manuscripts. The later model-theoretic sections are excluded.
- [Pruned context encoder](lemmas/context-encoder.zh-CN.md): finite output, exact parent table, fixed-context order, and middle-row transport.
- [Owner-entry key decrease](lemmas/owner-entry.zh-CN.md) and [partial-rebase key comparison](lemmas/partial-key-comparison.zh-CN.md).
- [Cross-leaf extension](lemmas/cross-leaf.zh-CN.md), [top-two-row transport](lemmas/top-row-transport.zh-CN.md), and [first-diagonal lemma](lemmas/first-diagonal.zh-CN.md).

The main paper is available in both languages. Supporting manuscripts retain their full Chinese arguments; they are not English translations. Older comments about what one local lemma does not prove must be read with that lemma's stated scope, not as a replacement for the assembled main proof.

## Row count and nonstandard matrices

Here $d=n-1$ is the number of source numerical coordinates. The encoder uses $d+2=n+1$ target rows. In particular the theorem gives

$$
\lim(\mathrm{BT3SS})\le |(0000)(1111)(2222)(3333)|<|(00000)(11111)|.
$$

The distinction between raw matrices and standard terms is essential. A numerically legal $r$-row matrix starting with zero is lexicographically below $B_{r+1}$ after zero padding; this alone does not assign it an ordinal below that bound. The raw legal lexicographic order even contains

$$
(0)(1)>_{\mathrm{lex}}(0)(0)(1)>_{\mathrm{lex}}(0)(0)(0)(1)>_{\mathrm{lex}}\cdots.
$$

That is not asserted to be an FS descent. For the encoded matrices the paper separately proves all finite block conditions, then uses finite coverage and standard BMS well-ordering to establish target standardness. Neither arbitrary raw matrices nor a raw lexicographic bound are substituted for that step.

## Frozen sources and evidence

The two definitions are pinned to NER revision `c539d8f68c5553da2d681c1251ea443b6b735e62`:

- [strong BT*(-1)Y-nSS v2](https://github.com/SmileLee-lyx/ne-rewritten/blob/c539d8f68c5553da2d681c1251ea443b6b735e62/src/notations/BM-like/Minus1_Y_nSS-series/BT_star_Minus1_Y_nSS-v2.ts).
- [BMS source, default BM4 short FS](https://github.com/SmileLee-lyx/ne-rewritten/blob/c539d8f68c5553da2d681c1251ea443b6b735e62/src/notations/BM-like/BM.ts).
- Rachel Hunter, [*Well-Orderedness of the Bashicu Matrix System*](https://arxiv.org/abs/2307.04606), for the target well-ordering theorem.

The [manifest](MANIFEST.json) records original and collected hashes, the exact excerpt range, editorial changes and frozen rule hashes. It imports 26 mathematical manuscripts and one [historical audit receipt](verification.json), unchanged except for LF line endings. This addition redistributes no private source PDF, upstream implementation, or old experiment scripts; it adds no notation kernel or Lean project. Historical script filenames and the receipt's original `repository_changes` field describe the earlier research run, not this publication.

The receipt distinguishes standard-path samples from raw numeric/finite-invariant samples, caps and a timed-out run. Batches overlap. These are finite error-finding checks, not a proof of universal correctness. To check the **collected files**, links and hashes, run from the repository root:

```sh
node research/btnss-bms/tools/validate.cjs
```

The validator is not a mathematical proof checker. The collector is provided for provenance and requires the original workspace as an explicit argument; it is not needed to read or validate a fresh clone.
