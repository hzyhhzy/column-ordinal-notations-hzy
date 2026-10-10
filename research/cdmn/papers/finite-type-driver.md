# Finite types and diagonal fundamental sequences · [中文全文](finite-type-driver.zh-CN.md)

This is an abridged English companion to the [full Chinese derivation](finite-type-driver.zh-CN.md). The finite types occur only in the proof; evaluating a template produces an ordinary finite CDMN graph.

Type 0 consists of nonzero closed graphs with well-ordered complete cones. A type-\(k\) rigid block has formal anchors \(0=z_0<\cdots<z_k\), first column \([z_{k-1}:1]\), and only older anchors or local references thereafter. Application is finite substitution and concatenation. Define
\[
\operatorname{Good}_{k+1}(B)\iff
 B\text{ preserves }\operatorname{Good}_k.
\]
This is a recursive predicate on finite codes, not an oracle for an unknown CDMN rank.

A root cap implements a finite iteration of its lower-type argument. The [separated driver theorem](separated-operator-driver.md) extends uniformly to all finite types: compress entire known macro blocks, retain their first columns, and use one parameter-independent reflection measure \(\mu\). Data never cut into hidden interiors. For a terminal macro, apply its assumed preservation property only after proving the shorter prefix at smaller \(\mu\).

The final-reader lemma is pointwise in parameters. Fix the parameters first, prove the concrete prefix \(f\), and then use \(R\cup E_f\). Only afterwards quantify over all parameters. This avoids assuming a single unknown row rank for every parameter value.

## The diagonal family

For every \(j\ge1\), the template
\[
L_{j-1}=[z_{j-1}:1][z_j:W]
\]
is \(\operatorname{Good}_j\), by the driver and final-reader lemmas. For \(g=|G|\),
\[
H(G)=G[0:1][g:W][g:2]
\]
has the exact children
\[
H(G)[n]=L_n(L_{n-1})\cdots L_1(L_0)(G).
\]
All applications have matching finite types. Thus every complete child cone is well-ordered, giving the same for \(H(G)\).

A further simultaneous induction on appended row-2 columns yields
\[
Z=()(1^{(1)})(1)(3^{(1)})(3^2)(5).
\]
Both \(H=H(S)\) and \(Z\) have full standard initial-segment paper proofs, not merely well-ordered embedded subsets. The argument does not extend automatically to arbitrary row-3 control or arbitrary interior readers.

The [Chinese manuscript](finite-type-driver.zh-CN.md) gives all template hypotheses and substitution identities. These are self-reviewed, unformalized paper proofs; ZFC is a sufficient ambient theory for the argument, while the KP plus uncountable-ordinal ledger remains unaudited. [Bounded checks](../historical/README.md) are not the all-type proof.
