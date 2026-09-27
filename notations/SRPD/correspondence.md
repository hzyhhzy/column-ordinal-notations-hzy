# SRPD's common segment and well-ordering transfer · [中文版](correspondence.zh-CN.md)

2026-09-28. This paper-level note consolidates existing low-segment results and
the parent-list coordinate change. No new Lean certificate is asserted.
See the [definition](definition.md). Only default fundamental sequences and
standard generated domains are considered.

## 1. Meaning of the common initial segment

Let $\alpha=\operatorname{otp}\operatorname{Desc}^{+}([0])$, excluding the SRPD
initial expression itself. The standard domains strictly below the following
endpoints have the same order type α.

| System | Endpoint | Basis |
| --- | --- | --- |
| RPD | `1,2`: `[][(0,0,0)]` | [Zero-layer skyline paper](../../research/order-comparisons/proofs/strong-e0mn-counting-20260919/RPD-12-correspondence.zh-CN.md), followed by the coordinate change below |
| ARD | `1,1,3`: `[][][(0,1,1)]` | [Ordinary e0MN/ARD isomorphism](../../research/order-comparisons/proofs/e0mn-ard-embedding-20260917/README.zh-CN.md) |
| ARD2 | `1,1,3`: the same triple graph | Section4: this cone has exactly the current ARD rule |
| IPD | `1,2`: `[][0:0/0]` | [Ordinary e0MN/IPD isomorphism](../../research/order-comparisons/proofs/ipd14-e0mn-20260917/e0MN-13-equals-IPD-12.zh-CN.md) |
| Ordinary e0MN | `1,3`: `()(1:ω)` | [Ordinary e0MN/RPD paper](../../research/order-comparisons/proofs/e0mn13-rpd12-20260919/README.zh-CN.md), and Section3 |
| Newer strong e0MN | `1,2`: `()(1:1)` | The specified version in the zero-layer paper above |

Both e0MN versions were invented by @test_alpha0; “newer strong” means the
2026-09-19 edition in this repository. These equalities do not identify raw
strings, all `FS_short` operations, or the complete systems. In particular,
α is not the whole RPD limit.

## 2. Compressing zero-layer RPD into parent lists

A zero-layer relation $(0,p,q)$ contains roots $0,\ldots,q$ at parent p.
Merge the greatest root at each parent and discard records dominated by a
greater parent with at least as great a root. Equivalently, at position t list
the greatest parent possessing root t. Thus $(0,5,1),(0,3,2)$ becomes `[5,5,3]`.

For last control root $q=h-1$ and parent c, the old shell below q still contains
parent c, so inherited parents from $C_c$ cannot replace its greatest parents.
At and above q the old shell is gone and only the inherited suffix remains.
Local lowering is therefore exactly

$$C[:h-1]\mathbin{\frown}C_c[h-1:].$$

Transport shifts parent and root addresses i≥c by span d. Parent-list values
shift likewise, while the d root positions crossed at c repeat the zero-based
c-th parent. This is precisely SRPD row insertion.
Successive seams require a separate check, not just a one-step local match:

* If $q<c$, the control root stays fixed and the preceding seam's lower shell
  cannot enter the next high-suffix inheritance.
* If $q=c$, the control root increases with the block number; the source and
  preceding seam both lie below the next inheritance threshold.

Both cases give the native seam formula. Internal copies, final controller
deletion and zero-index cases consequently commute at every default index.
The linked skyline paper supplies the full seam and standard-domain injectivity
arguments; finite samples are not substituted for them.

### The hidden-root exception at the bottom

Delete the first empty column without changing parent numbers, and read parent0
as the common root. The RPD endpoint becomes SRPD `[0]`. Counts lose their first1
and all remaining column counts agree exactly. Old zero and old one both map
to new zero, so this raw projection is **not** injective on the entire domain.

After excluding old zero, old positive integer m maps to new m−1 and the rest
of the correspondence is strictly order preserving. Both strict-descendant
domains contain an initial ω segment. Removing its first element does not
change the total infinite order type: $\omega+\gamma$ remains $\omega+\gamma$.
Alternatively align the finite ordinals separately to obtain a full order
isomorphism, at the expense of indexed commutation at that boundary.

## 3. The ordinary M13 strict cone

Every nonzero strict descendant of S starts with an empty column and satisfies
the stronger inequality $h\le p$ in its nonempty columns. The seed formula is

$$S[n+1]=D_n=[][1][2,2]\cdots[n]^n,\qquad S[0]=0.$$

Compress equal-parent runs into `(parent, ending row)` records. In this strict
cone the result is exactly the ordinary e0MN finite-row skyline. Local decrement,
high-suffix inheritance, parent reflection and finite row insertion coincide.
D_n and its descendants therefore form the same finite graph system as
ordinary `M13[n]`, including zero and every default index. Only the endpoints
have the indicated one-index shift. Taking suprema gives $\alpha=|\mathrm{M13}|$.

## 4. Why current ARD2 is included

Add an initial empty column to an ordinary finite M graph and replace `(p:r)`
by $(0,p,r-1)$. Its row anchors are0 and its roots satisfy $q<p$.
These conditions survive lowering, source inheritance and transport: row0
remains0, positive roots decrease, root0 disappears, and parent/root addresses
use the same strictly increasing map. Row SELF, root SELF and positive-row
borrowing branches specific to ARD2 cannot occur. Current compressed ARD and
ARD2 therefore have identical rules throughout this strict cone.

Their endpoint `[][][(0,1,1)]` also has identical children: index0 gives `[][]`;
positive n appends n chain columns $(0,j,j-1)$ for j starting at1.
Every subsequent path agrees. These are actual standard endpoints, and the
existing initial-segment/reachability lemmas identify their descendant cones
with the indicated standard initial segments. Applying the archived ARD
finite-bottom adjustment gives the ARD2 order-type statement.

The IPD projection additionally needs its forest condition and redundant-edge
argument; “also zero-layer” is not a replacement for its separate linked proof.
Likewise, finite-row rule similarity alone does not prove a corresponding
initial-segment equality for LRD or Ω-LRD3.

## 5. Well-ordering, axioms and formalization status

The specified RPD standard initial segment is well-ordered. The paper
correspondence transfers well-ordering to SRPD's strict descendants; adding S
as a greatest element preserves it. Equivalently, lift nonzero SRPD descent to
RPD and terminate separately at the finite bottom, without treating a zero
self-loop as descent.

The coordinate changes concern finite lists, natural numbers and already
constructed standard orders. They introduce no new large-cardinal or higher
semantic assumption. Relative to the existing RPD paper, the bound remains
$KP_\omega+\text{there exists an uncountable ordinal}$ with full set induction.
This is a paper well-ordering **transfer**, not a new Lean derivation internal
to that theory.

Existing seven-system Lean sources, closures and receipts are unchanged.
The new SRPD JS/Python package, these isomorphisms and the TBMS simulations have
no new Lean theorems. [Bounded tests](../../tests/srpd.cjs) compare the packaged
RPD, ARD and ARD2 kernels directly; they test implementations, not the universal
standard-domain claims.
