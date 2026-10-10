# Coherent families as a new proof layer · [中文全文](polymorphic-family-driver.zh-CN.md)

This is an abridged English companion to the [full Chinese derivation](polymorphic-family-driver.zh-CN.md), extending the [finite-type argument](finite-type-driver.md).

A coherent family \(A=(A_j)_{j\ge1}\) is described by one finite block pattern. Its first column is \([z_{j-1}:1]\); all other references, including nested ones, are global 0 or \(z_j+t\). The old anchor cannot reappear internally. Require \(\forall j\,\operatorname{Good}_j(A_j)\).

Appending \([z_j:2]\) defines \(\Delta A\). Its children are the type-correct chain
\[
A_{j+n}(A_{j+n-1})\cdots A_j.
\]
The entire coherent family, not one instance, therefore supplies the higher-type arguments needed to prove preservation.

At the next proof layer, type 0 is such a good coherent family. Type 1 starts with row 2, while higher types start with row 1. The single-column row-2 template is already known good because it implements \(\Delta\). Root caps at positive types implement finite iterations.

The separated-driver argument still works: ordinary ports are singleton row 1, so they empty their shell and copy an entire row-2-headed macro. Ordinary data cannot cut straight into that macro's first column. The skeleton and its reflection measure are independent of both layers of parameters.

After fixing every parameter, the final-reader argument again uses the independently known closed row domain \(R\cup E_f\). Quantification over the full parameter string comes last.

For every new type \(i\ge2\), the two-column template
\([a_{i-1}:1][a_i:W]\) preserves the preceding type. This does **not** prove a type-1 analogue with row-2 head followed by \(W\).

Evaluating the resulting finite diagonals at the original \(L\) family, the row-2 operator, and \(S\), gives a full-cone proof for
\[
Z_2=()(1^{(1)})(1)(3^{(1)})(3^2)(5)(6^{(1)})(6^2)(8).
\]
Its standard initial segment is covered via standard-domain comparability. The construction generalizes to all finite proof layers in the following paper.

Claims are self-reviewed paper arguments, not Lean certificates. The [historical experiments](../historical/README.md) check finite substitution and scope; they do not prove the universal preservation predicates.
