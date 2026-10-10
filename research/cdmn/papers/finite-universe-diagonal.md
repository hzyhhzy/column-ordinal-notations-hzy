# Finite proof layers and their common endpoint · [中文全文](finite-universe-diagonal.zh-CN.md)

This is an abridged English companion to the [full Chinese derivation](finite-universe-diagonal.zh-CN.md).

Use two natural-number indices \((h,k)\): proof-family layer \(h\), finite type \(k\). At \((0,0)\), Good means complete-cone well-ordering of a nonzero closed graph. At \(h>0,k=0\), an object is a coherent finite-pattern family of all permitted types in layer \(h-1\). Positive types preserve the previous type. The definitions recurse on \(\omega h+k\), without assuming a rank for the whole CDMN system.

Let \(m(0)=1\), \(m(h)=2\) for \(h>0\). At every finite layer, the row-2 family diagonal is good before it is used as the layer's type-1 operator. Root caps, fixed closed-row drivers, and a final open \(W\) then admit the same parameter-uniform proofs. Macro head row 2 is allowed only where the already proved diagonal supplies it.

The family
\[
\Lambda_{h,k}=[a_{k-1}:1][a_k:W],\qquad k\ge m(h)
\]
is good at every permitted pair. Its row-2 diagonals and positive root caps are good as well.

For a known-good closed \(G\), put \(g=|G|\) and
\[
H_1(G)=G[0:1][g:W][g:2],
\]
\[
H_{d+1}(G)=H_d(G)[b-1:1][b:W][b:2],
\quad b=|H_d(G)|,\qquad
Z_d(G)=H_d(G)[|H_d(G)|-1:1].
\]
These are concrete evaluations of the finite-layer templates, so every full cone is well-ordered. Now set
\[
F_\infty(G)=H_1(G)[g+2:1;g:1].
\]
Direct expansion gives \(F_\infty(G)[n]=H_{n+1}(G)\) for every \(n\ge0\). Any infinite descent would enter one fixed first-step cone, giving a contradiction. This is not the false assertion that an arbitrary union of well-orders is well-ordered.

At \(G=S\), the resulting standard endpoint is
\[
F_\infty=[][0:W][0:1][2:W][2:2][4:1;2:1].
\]
It exceeds every finite \(Z_d(S)\); it is not the entire CDMN limit. No equality with a named external notation is proved.

All conclusions remain self-reviewed paper arguments. Ordinary ZFC suffices for the given proof predicates and reflection construction; no KP plus uncountable-ordinal audit or Lean formalization is supplied. See [dependencies](../proof-dependencies.md).
