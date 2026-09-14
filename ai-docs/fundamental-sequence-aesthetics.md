# Designing Beautiful Fundamental-Sequence Ordinal Notations · [中文版](fundamental-sequence-aesthetics.zh-CN.md)

[AI reading documents](README.md) · [Repository home](../README.md)

— A design guide for a GPT‑6 Astra agent taking over this research

Date: 2026-09-15.

This document hands over design requirements, mathematical interfaces, and research methods. It does not define a new notation, nor does it survey the relative order types of existing notations. You do not need to know all the rules of Y, wY, RPD, ARD, or IPD before reading it.

The central goal is: **design genuinely powerful notations while keeping expressions visibly organized as finite sequences of columns. Expansion should act only on the last column and extend to the right; comparison should proceed from left to right. Complexity should arise mainly from interactions between columns, rather than from hiding another enormous notation inside each column.**

Here, “aesthetics” primarily means coherence between mathematical structure, rules, comparison, and presentation—not colors or typography.

## Two practical entry points: research references and the eventual user platform

- **[The user's ordinal-notation GitHub repository](https://github.com/hzyhhzy/column-ordinal-notations-hzy)** provides existing definitions, expansion rules, implementations, and well-ordering proof ideas to consult during research. You can study column structures, copying and transport, semantic descent, written proofs, and Lean code. This does not require copying an existing design or restricting a new notation to the strength of the existing ones. The local relative links later in this document point to the corresponding repository files; if you received only this Markdown file, you can find them in the online repository.
- **[NER (ne-rewritten)](https://smilelee-lyx.github.io/ne-rewritten/)** is where the user will actually inspect, manipulate, and expand the completed notation one term at a time. The final deliverable should therefore include a JavaScript expander compatible with its “custom notation” feature. It should let the user browse lists, count sequences, and graphical views suited to the structure. Delivering only a paper or a Python program does not complete the browser-facing part of the task. Compatibility and display behavior should be checked against NER as it exists when the work is delivered.

Their roles are distinct: **the repository supports design and proof; NER provides the eventual user experience.** The mathematical notation itself does not depend on a website. Integrating it into NER must not silently change its fundamental-sequence rules to accommodate a display.

## 1. Keep this requirements table in mind

| Priority or role | Requirement | Precise meaning |
| --- | --- | --- |
| Core form | A finite sequence of columns | The expression is a column structure, not the history of operations that produced it. |
| Core form | Act only on the last column | Every earlier column remains unchanged; delete or modify the last column, then append to the right. |
| Core form | The zeroth term deletes the last column | For an ordinary nonzero expression, `A[0]` is exactly the result of deleting its last column. Delete a column, not a row. |
| Core form | Prefix-nested fundamental sequences | `A[n]` is a prefix of `A[n+1]` as a sequence of complete columns; equality is allowed. |
| Standard domain | Generation from compatible seeds | Study finite expansion descendants of the designated starting expressions, rather than mixing in arbitrary objects that happen to fit the data format. |
| Core goal | Columnwise comparison and unique representation | On a compatible reachable domain, finite exact local countdowns give an injective numerical-sequence representation ordered lexicographically; do not retain duplicate construction histories. |
| High-priority aesthetic | A concise definition | The complete, readable core definition should be concise—not merely the code left after essential subroutines have been omitted. |
| High-priority aesthetic | A small burden inside each column | Prefer a few kinds of finite relations and simple parameters; avoid embedding an entire complex tree notation in a single edge. |
| High-priority aesthetic | A substantive increase in strength | Seek stronger internal mechanisms, not merely an easily separable small wrapper around the old system. |
| Proof goal | A credible route to well-ordering | Conjectures may come first, but identify what you intend to prove and which structures will support it. Long computations are not proofs. |
| Optional implementation technique | Copying in segments | Often natural, but not compulsory; in particular, copying exactly `n` times is not required. |
| Low-priority preference | Moderate numbers and gentle count growth | Prefer these when they arise naturally, but do not sacrifice the main strength goal or structural simplicity for them. |
| Explicit exception | An adjoined top | An external top is not an ordinary last column. Its fundamental sequence may fail the literal prefix condition, but its seeds should still be compatible. |

Do not upgrade low-priority preferences into hard conditions that reject every candidate. Equally, do not turn the top exception into permission to introduce exceptions throughout ordinary expressions.

## 2. The minimum ordinal background

### 2.1 Ordinals are not large natural numbers

Natural numbers measure finite lengths; ordinals also describe infinite well-order types. For example, putting all the natural numbers in order and then adding one more position gives $\omega+1$. Putting two such blocks one after another gives $\omega\cdot2$.

When we call a notation “large,” we are primarily concerned with the length of the well-order it can represent—not the number of decimal digits in an expression, the length of an expanded array, or how slowly the program runs.

### 2.2 Zero, successors, and limits

Zero has no smaller ordinal. A successor $\beta+1$ has a greatest predecessor, $\beta$. A nonzero limit $\lambda$ has no greatest predecessor; it calls for a sequence of smaller ordinals approaching it from below.

Write a fundamental sequence as

$$
A[0],A[1],A[2],\ldots.
$$

The brackets here denote the fundamental-sequence operation, not an array lookup. For successors, a common convention makes all the $A[n]$ equal to the same predecessor. For limits, we want all these terms to be strictly below $A$ and cofinal below it: every standard term smaller than $A$ must be no greater than some $A[n]$.

“Cofinal” does not mean numerically “very close.” It means that no entire upper portion below the limit is missed. Merely supplying an increasing sequence of smaller terms does not establish cofinality in the intended limit.

### 2.3 Give finite rules first; then prove they really form an ordinal notation

A design normally starts with finite expressions and executable expansion rules. One then proves that nonzero expansion cannot descend indefinitely and establishes a well-order on the standard expressions.

Do not put the desired conclusion into the definition. For example, “the legal expressions are exactly those with well-founded semantics” is not an independent, effective legality criterion.

These are also three different statements: “each individual step finishes,” “one trajectory that repeatedly takes `[1]` finishes,” and “no infinite expansion chain is possible under any choice of parameters.”

## 3. The ideal expression: a structural sequence, not an operation sequence

### 3.1 One column per position

Write an ordinary expression as

$$
A=(C_0,C_1,\ldots,C_{m-1}).
$$

Each $C_j$ is the finite structure of column $j$. It may be a number or a small collection of relations pointing to earlier columns. The whole expression must still have an unambiguous decomposition into column zero, column one, column two, and so on.

A list view might look like this:

```text
[][contents of column 1][contents of column 2][contents of column 3]
```

A column may contain multiple relations. There is no requirement that it contain only one integer, or that the number of relations have a fixed uniform bound. The aim is a small number of relation types, simple parameters for each relation, and clear meanings.

Distinguish the empty sequence from an empty column. In a graph-based design, one can adopt:

```text
∅       zero: no columns
[]      one empty column, representing one
[][]    two empty columns, representing two
```

This is not a universal convention that every ordinal notation must follow, but it is natural for this style of research.

### 3.2 An operation history is not the mathematical object

`Top[3][2][1]` may be useful as an input shorthand or a debugging record of provenance. After expansion, however, the actual object should be the resulting column structure.

If two different operation paths produce the same column graph, they produce the same expression. Do not treat the two paths as two different ordinals and then invent a “path priority” to compare them.

This is why a display such as `023`, meaning only “apply `[0]`, then `[2]`, then `[3]`,” is unsatisfactory. It hides the structure and promotes irrelevant construction history into the notation itself.

### 3.3 The same structure should have a canonical data representation

If a column is a set of relations, the order in which those relations are enumerated usually has no mathematical significance. Sort them, remove duplicates, and compress redundancies that can be recovered deterministically.

For example, if a single key includes every root $0,1,\ldots,q$, storing just the greatest root $q$ may suffice. But state the closure rule explicitly: “greatest root” must not be mistaken for the presence of only one root edge.

Normalization should remove representational redundancy without changing the mathematical object. It must not quietly reorder earlier columns after each append, since that would destroy the genuine prefix relation required below.

## 4. The core expansion contract

### 4.1 One formula captures the main requirements

Let $A=P\frown(C)$, where $P$ is the prefix obtained by deleting the last column, and $\frown$ denotes concatenation of column sequences. Require

$$
A[n]=P\frown R_A(n),\qquad R_A(0)=\varepsilon,
$$

and

$$
R_A(n)\preceq_{\mathrm{pref}}R_A(n+1).
$$

Here $\varepsilon$ is the empty column sequence, and $\preceq_{\mathrm{pref}}$ means “is a prefix of, allowing equality.” Consequently,

$$
A[0]=P,\qquad A[n]\preceq_{\mathrm{pref}}A[n+1].
$$

Intuitively, the last column is an instruction awaiting execution. Expansion removes it or lowers it by one stage, then appends the subsequent structure it permits. Earlier columns are neither reinterpreted nor rewritten.

### 4.2 A prefix means an exact structural prefix

The complete column contents must agree, including relations, markers, and references. It is not enough for the displayed numbers to happen to match.

Computing a larger index must not change columns already produced. For example:

```text
A[0] = P
A[1] = P D E
A[2] = P D E F G
A[3] = P D E F G H
```

This shape is acceptable. The following is not:

```text
A[1] = P D E
A[2] = P D E' F       E has been changed to E'
```

Increasing the index may append more output, but must not revise existing output.

### 4.3 The copy count need not equal the index

You may copy one segment, successively copy different segments, or generate new columns by a deterministic rule. `n` need not mean exactly “copy n times.”

One easy way to preserve prefixes is to specify an output stream independently of the eventual index and let `n` select a nondecreasing sequence of finite prefixes of that stream. The stream itself still needs a clear, effective finite generation rule. It must not use an unknown ordinal comparison or termination test as its generator.

Even when copying is used, specify whether the convention is “the original block plus n new copies” or “n copies in total.” That difference of one directly affects the fundamental sequence.

### 4.4 Handle successors, zero, and the top separately

A successor's fundamental sequence is normally constant at the expression with its last column deleted. Thus the prefix condition must allow equality; not every expression's fundamental sequence can be required to grow strictly in length.

For software convenience, you may define $0[n]=0$, but this self-loop does not count as a nonzero descent step.

An external top $\mathsf{Top}$ may have a separately specified sequence of seeds:

$$
\mathsf{Top}[n]=S_n.
$$

It need not be a finite column expression, and $S_n$ need not literally be a prefix of $S_{n+1}$. Ideally, however, prove that an earlier seed can be obtained by expanding a later seed. This prevents the seeds from being a collection of unrelated systems.

For example, `Limit of ARD2` in the expander is such a special entry point: it is placed above all ordinary standard expressions and expands to designated seeds, rather than adding a new label inside every ordinary expression. If the ordinary standard domain has no greatest element, this top represents the limit of the entire ordinary domain. Merely adjoining such an entry marker is not the substantive increase in strength sought in this document.

## 5. The standard reachable domain is not an optional footnote

### 5.1 Do not confuse three sets

First come all objects that fit the data format. Next come structurally legal objects satisfying local coordinate constraints, closure conditions, and so forth. Only then come the standard reachable objects actually studied by the notation.

For a seed $S$, define

$$
D(S)=\{A: S\text{ can produce }A\text{ by finitely many fundamental-sequence operations}\}.
$$

Zero steps are allowed, so $S\in D(S)$. Throughout the rest of this document, arrows count only actual expansions whose source is nonzero, ignoring the software convention $0\to0$. Adding or removing that halted-state self-loop does not change finite reachable sets. With multiple seeds, one usually takes

$$
U=\bigcup_n D(S_n).
$$

“Standard” must not mean “the objects that happen to avoid problems.” Instead, independently specify the seeds and expansion rules, then define the domain by finite reachability.

### 5.2 Seeds need compatibility

A simple sufficient condition is

$$
S_{n+1}\longrightarrow^*S_n,
$$

where $\longrightarrow^*$ means zero or finitely many expansion steps. It follows that

$$
D(S_n)\subseteq D(S_{n+1}).
$$

More generally, the same purpose is served if every pair of seeds has a seed whose descendants include all descendants of both.

This condition allows the external top to violate the literal prefix requirement while keeping the entire standard domain unified. RPD's seeds satisfy $S_{n+1}[1]=S_n$; adjacent ARD2 seeds are linked by `[0]`. Both exemplify this interface. See the [RPD definition](../notations/RPD/definition.md) and [ARD2 definition](../notations/ARD2/definition.md) for their actual rules. We are using only their seed compatibility here, not drawing conclusions about the relative sizes of their order types.

### 5.3 Why a counterexample made from arbitrary handwritten expressions may be irrelevant

If the raw syntax permits two different handwritten one-column symbols both claimed to “represent ω,” this only shows that the raw syntax permits duplicates. It does not establish duplication in the standard domain.

Under the compatibility and finite-local-count assumptions below, two distinct objects with the same count sequence cannot both belong to one standard reachable domain. With global well-foundedness as well, neither can two distinct objects with the same expansion rank. A challenge to uniqueness on the standard domain must therefore first establish that both proposed counterexample objects are reachable.

Likewise, an unusual column graph does not automatically belong to the domain on which columnwise well-ordering is claimed merely because it satisfies local coordinate restrictions. Conversely, excluding a counterexample on reachability grounds requires a real argument. An expression's unfamiliar appearance is not evidence that it is unreachable.

## 6. Why this form really supports lexicographic order and unique representation

This section matters. Do not treat “prefix” as magic that eliminates the need for a well-ordering proof. But do not ignore the standard reachable domain and dismiss the structural conclusions it does provide, either.

The precise statement is: **last-column-local expansion, prefix-nested fundamental sequences, and a compatible standard reachable domain already make reachability total. If local countdowns are finite, they rule out cycles and make exact count sequences an injective lexicographic representation. Global well-ordering remains a separate next step.**

Global well-foundedness of expansion is sufficient to make local countdowns finite, but it is not a necessary premise for this comparison result. Keeping these statements separate avoids a circular presentation: “first prove well-ordering to explain comparison, then use comparison to prove well-ordering.”

### 6.1 Longer fundamental-sequence terms can descend to shorter ones

If $A[i]$ is a prefix of $A[j]$, repeatedly taking `[0]` from $A[j]$ reaches $A[i]$.

Hence, for $i\le j$,

$$
D(A[i])\subseteq D(A[j]).
$$

The subsystems below the children of one parent are not independent branches: their descendant sets are nested. This is a particularly valuable feature of this design style.

### 6.2 Well-foundedness is not needed first: descendants of a common seed are already comparable by reachability

First observe a “prefix barrier.” If $P$ is a prefix of $X$, an expansion path starting at $X$ cannot destroy the prefix $P$ before visiting $P$ itself. As long as the current expression is strictly longer than $P$, changing its last column still preserves all of $P$. Moreover, any extension of $P$ can return to $P$ by repeatedly taking `[0]`.

Now take two finite paths $A\longrightarrow^*B$ and $A\longrightarrow^*C$. Use ordinary induction on the sum of their lengths. If either path has length zero, comparability is immediate. Otherwise, consider their first steps $U=A[i]$ and $V=A[j]$. After interchanging names if necessary, assume that $U$ is a prefix of $V$.

- If $U$ is still a prefix of $C$, then $C\longrightarrow^*U\longrightarrow^*B$.
- Otherwise, the path from $V$ to $C$ must pass through $U$. Thus both $B$ and $C$ are reachable from $U$, and the sum of the two path lengths has decreased, so induction applies.

Therefore any two descendants of a common root are related by reachability in at least one direction. Cycles permitting reachability in both directions have not yet been excluded, so the initial conclusion is, precisely, a **total preorder**. This argument uses only finite paths and assumes no global well-foundedness.

Section 6.4 shows that finite exact local countdowns make every step strictly descending, thereby ruling out cycles. Once that is established, for distinct standard terms $A,B$, exactly one of the following holds:

$$
A\longrightarrow^+B
\quad\text{or}\quad
B\longrightarrow^+A.
$$

Here $\longrightarrow^+$ means at least one expansion step. An increasing union over compatible seeds retains this conclusion, because any two standard terms have a common seed ancestor. No claim is being made that arbitrary raw legal graphs are comparable by reachability.

### 6.3 What is a column's “count”?

For a fixed prefix $P$ and the following column $C$, regard $P\frown(C)$ as a complete expression. Perform an expansion with a nonempty replacement tail, then delete the newly appended suffix, retaining only the new column at the original position.

All nonempty replacement tails have the same first column, since they are prefix-nested. Denote this local rewrite by

$$
T_P(C).
$$

If every expansion simply deletes the column, there is no next local state. Assign this terminal state count one: the count includes the final deletion. In general,

$$
h_P(C)=
\begin{cases}
1,&C\text{ is a local terminal state},\\
1+h_P(T_P(C)),&\text{otherwise}.
\end{cases}
$$

This is not the total running time obtained by repeatedly taking `[1]` from the whole expression. It tracks only the column at a fixed position, ignoring the temporary material generated to its right.

One can directly prove this count finite using an acyclic finite state graph in the fixed context, or another local descent measure. Merely having finitely many states is insufficient, since a finite state system may cycle. If a global well-foundedness proof is already available, local finiteness follows: each local rewrite can be realized by “one actual expansion followed by finitely many `[0]` truncations.” An infinite local process would therefore yield an infinite actual expansion chain.

An implementation should also provide finite algorithms for terminal-state recognition and $T_P$. Abstractly knowing that “some n produces a nonempty tail” does not make it effective to decide that “no n produces a nonempty tail.” In common simple designs, a nonterminal column produces the same first replacement column for every positive index, so this unbounded search is unnecessary.

### 6.4 Every expansion step strictly decreases the exact count sequence lexicographically

Define the full count sequence by

$$
\chi(A)=
\bigl(
h_{\varepsilon}(C_0),
h_{(C_0)}(C_1),\ldots,
h_{(C_0,\ldots,C_{m-2})}(C_{m-1})
\bigr).
$$

Counts depend on the context to the left; they are not simply isolated “complexities” of individual columns.

If expansion deletes the last column, the count sequence becomes a proper prefix. If a rewritten column remains at the original position, then:

```text
Before expansion:  a0, a1, …, a(m−2), k
After expansion:   a0, a1, …, a(m−2), k−1, further appended numbers…
```

Earlier columns and their contexts have not changed, so their counts are identical. At the last original position, the count decreases by exactly one. No matter how long the new suffix is or how large its entries are, it cannot affect this lexicographic decrease.

Use the ordinary lexicographic order on finite sequences, with a proper prefix smaller than its extension. There is no requirement that the sum of the entries, their maximum, or the total number of columns decrease.

### 6.5 On the standard domain, the count sequence is more than a statistic that might collide

The previous section establishes that if $A\longrightarrow^+B$, then

$$
\chi(B)<_{\mathrm{lex}}\chi(A).
$$

Combine this with the reachability totality of Section 6.2. Distinct standard terms $A,B$ are strictly reachable in one direction, so their count sequences differ, and lexicographic comparison gives exactly their order.

In other words, under these hypotheses,

$$
B<A\quad\Longleftrightarrow\quad
\chi(B)<_{\mathrm{lex}}\chi(A),
$$

where the left-hand side means that a strict expansion descendant is smaller. Thus $\chi$ is an order embedding and, in particular, injective.

Consequently, **one must not say without qualification that these counts are “merely a display, necessarily lose information, and cannot be used for comparison.”** Those risks exist for arbitrary handwritten structures. On a standard domain satisfying the stated conditions, the mathematical conclusion is stronger.

Conversely, not every program output called a “count” is this $\chi$. Column height, edge count, tree size, or a truncated approximation need not be the exact local countdown. Check separately whether a particular implementation uses this definition and declares the same standard domain.

### 6.6 “One expression per ordinal” also has a precise interpretation

The injectivity of counts above does not require a prior proof of global well-ordering. A genuine ordinal interpretation, however, still requires well-foundedness of nonzero expansion. Since strict comparison is the transitive closure of finite nonzero expansion, this also makes the standard domain a well-order. Then interpret $A$ as the order type of all standard expressions below it:

$$
|A|=\operatorname{otp}\{B\in U:B<A\}.
$$

Distinct standard terms occupy distinct ordinal positions and therefore do not represent the same ordinal. This “position in a well-order” is a standard ordinal interpretation; see mathlib's definitions of [order type and typein](https://leanprover-community.github.io/mathlib4_docs/Mathlib/SetTheory/Ordinal/Basic.html).

Fundamental sequences also automatically cover all smaller standard terms: if $B<A$, take a finite expansion path from $A$ to $B$. Its first step $A[n]$ satisfies $B\le A[n]$. Thus this is not an arbitrary choice of a well-order paired with expansions that might miss predecessors.

If an additional traditional ordinal formula is assigned to each expression and claimed to equal $|A|$, that external interpretation must still be proved consistent with the intrinsic order. Uniqueness of intrinsic representation does not make every casually chosen external assignment injective.

## 7. A proof obligation remains: lexicographic descent is not well-ordering

The fact that count sequences consist of positive integers does not make the set of all such sequences lexicographically well-ordered. The simplest warning is

$$
(2)>(1,2)>(1,1,2)>(1,1,1,2)>\cdots.
$$

At each step, the number at the first changed position decreases, but new work is moved farther to the right.

We can even specify a nonterminating toy system that meets the shape requirements. Use only the symbols $1,2$. An expression ending in $1$ always loses its last column. For one ending in $2$, define

$$
(P,2)[0]=P,
\qquad
(P,2)[n]=(P,1,\underbrace{2,\ldots,2}_{n\text{ copies}})\quad(n\ge1).
$$

These rules act only on the last column, their fundamental sequences are prefix-nested, and the local counts are respectively $1$ and $2$. Yet repeatedly taking `[1]` from the seed $(2)$ produces the infinite descending chain above. **Every term in this counterexample really is reachable from the same seed.**

Keep these statements separate:

- The structural contract explains why expansion can be organized lexicographically.
- Exact local counts provide natural comparison coordinates.
- A global well-ordering proof must still rule out work being transferred to the right forever.

A well-ordering proof cannot stop at “some number decreases by one each time.” It must explain why newly generated suffixes cannot produce an endless succession of further descent stages.

## 8. A complete, small positive example

This example illustrates the design style; it is not a candidate intended to achieve the desired strength.

Take nonincreasing sequences of natural numbers

$$
(a_0,\ldots,a_{m-1}),\qquad a_0\ge\cdots\ge a_{m-1},
$$

and interpret them as

$$
\omega^{a_0}+\cdots+\omega^{a_{m-1}}.
$$

The empty sequence represents zero. Here each column is a natural-number exponent; a column with exponent zero contributes one.

If the last exponent is zero, every expansion deletes that column. If it is $k>0$, set

$$
(P,k)[n]=(P,\underbrace{k-1,\ldots,k-1}_{n\text{ copies}}).
$$

For example:

```text
(3,2)[0] = (3)
(3,2)[1] = (3,1)
(3,2)[2] = (3,1,1)
(3,2)[3] = (3,1,1,1)
```

This has the properties we like: the old prefix is unchanged; the zeroth term deletes a column; fundamental sequences are prefix-nested; individual columns are extremely simple; an original exponent $k$ has local count $k+1$; comparison is lexicographic; and the nonincreasing condition gives the usual canonical expressions.

That condition also illustrates why canonical form matters. If arbitrary exponent sequences were allowed with the same ordinal-sum interpretation, both $(0,1)$ and $(1)$ would give $\omega$, since $1+\omega=\omega$. Duplication involving a nonstandard expression must not be mistaken for duplication on the nonincreasing standard domain.

The finite standard expressions in this example represent the ordinals below $\omega^\omega$. One can adjoin a top whose nth fundamental-sequence term is the one-column expression $(n)$. These seeds need not be literal prefixes of one another, but $(n+1)[1]=(n)$, so they are compatible. The top exception is natural here.

A stronger candidate should try to retain this clear external appearance while introducing internal relational mechanisms much more powerful than fixed natural-number exponents. Repeatedly putting wrappers around this small example does not by itself meet the research goal of being “large and beautiful.”

Nor should “it can ultimately be written as a sequence of natural numbers” be taken to limit a notation to the strength of this small example. What matters is which sequences are actually generated, how they expand, and the order type of their lexicographically ordered subdomain—not the complexity of the characters used in each coordinate.

## 9. Simplicity must account for the real costs

### 9.1 A short definition is not code golf

A readable Python core with explicit data classes, a few small functions, and an expansion procedure that can be checked directly is often simpler than a version compressed into a few dozen lines using implicit recursion and magic indices.

Assess at least five costs separately:

1. **Syntax cost:** How many kinds of objects and parameters must a reader understand?
2. **Rule cost:** How many independent expansion cases are there, and which require mutual recursion?
3. **Comparison cost:** Can objects be compared directly, or must a long expansion be executed?
4. **Invariant cost:** How many hidden conditions underlie legality, and what is easy to omit when copying?
5. **Per-column information cost:** How many levels of brackets and kinds of explanation does a typical printed column require?

Do not count only the lines in the main function while hiding complexity in `normalize`, `compareOrdinal`, `findReachable`, or “choose a suitable rank.” Those subroutines are part of the definition too.

### 9.2 Account for the mathematical core and the software wrapper separately

A NER file includes parsing, menu registration, HTML/SVG, colors, caching, and resource-limit messages. These may be lengthy without making the mathematical definition complex.

Conversely, a short-looking NER file that depends on an enormous interpreter not included with it does not demonstrate a simple mathematical core.

A good deliverable usually includes a standalone, readable Python or pseudocode definition expressing the actual notation rules. The browser expander then handles interaction.

### 9.3 Expansion, comparison, and counting should have clear interfaces

A useful conceptual separation is:

```text
normalize(A)     Normalize a finite structure
expand(A, n)     Compute the actual fundamental-sequence term
compare(A, B)    Compare standard terms
local_step(P,C)  Compute the local rewrite at a fixed position
count(P,C)       Compute the exact local countdown, with separate optimizations if useful
render(A, mode)  Display the object without changing it
```

These need not literally be six functions. The point is that display must not determine the mathematical rules, a counting timeout must not block an otherwise easy expansion, and comparison should not depend on expensive counting by default.

## 10. Do not turn the inside of each column into another universe

### 10.1 What makes column contents attractive?

Prefer a few edge types; fixed-arity tuples of integers or column addresses describing each edge; levels and references that can be located directly in the whole graph; and clear closure conventions that compress certain large sets.

For example, a column's triples might describe a level anchor, a parent column, and a root parameter. Future designs need not use triples: the point is the pattern of simple relations giving rise to rich global behavior.

An expression can derive its power from repeated use of earlier columns, transport of references during copying, creation of relations at a splice, and feedback between these operations. Extreme complexity inside a single label is not the only source of strength.

### 10.2 Why putting a tree directly inside every edge can be unattractive

Suppose every edge carries a level number and a tree; the tree's head is itself another tree; and each level has its own top element, local order, and substitution rules. A column may still be enclosed in one pair of brackets, but the reader must effectively understand two or more notations at once.

The costs include deeply nested brackets, an additional recursive comparison order, traversal of all internal references during copying, difficulty displaying the full graph, and a proof that must connect the external column structure to the internal tree structure.

This does not mean tree parameters are necessarily weak, useless, or mathematically unnatural. The [IPD definition](../notations/IPD/definition.md), for example, explicitly uses iterated profile trees; that is a genuine design choice worth studying. The aesthetic requirement here is: **if the goal emphasizes simplicity comparable to RPD or ARD, the possibility of greater strength does not justify ignoring a substantial increase in per-column complexity.**

### 10.3 Encoding everything as one integer does not solve the problem

Every finite tree can be encoded by a natural number. Replacing a huge tree with a Gödel code does not genuinely simplify the rules: decoding, comparison, and transport still require the original tree.

Likewise, compressing an entire ordinal expression into “label q,” while invoking the entire old notation during expansion, merely hides complexity.

Useful compression exploits regularities already present in the structure to make both storage and operations more direct. Merely shortening the printed representation is not enough.

### 10.4 Do not make the rules worse just to flatten the structure

Splitting a tree into many columns does not automatically improve a design. If that requires numerous bracket-matching columns, jump markers, and global scans—or if one expansion revises much earlier columns—the original last-column locality may be lost.

Compare the full costs of the alternatives. Do not first declare “trees are bad” and then eliminate all tree-shaped information at any price.

## 11. Large and beautiful: reject small wrappers without substantive gains

### 11.1 Being “strictly larger” may not satisfy the research goal

Let the old notation cover an order type $\alpha$. Adding an easily separable external level to obtain $\alpha\cdot\omega$, $\alpha^\omega$, or some simple closure may genuinely increase it mathematically.

But the user is not asking for a succession of such easily described external extensions. The goal is an enhancement that changes the system's internal organizing capacity. “Not large enough” here is relative to that research goal. It does not claim that these ordinal operations produce equally small changes for every $\alpha$; an operation may sometimes fail to increase a particular $\alpha$ strictly at all.

The analogy of “applying one more exponential to Graham's number” expresses dissatisfaction with simple wrappers. It is not a proof of an order-type comparison.

### 11.2 To detect a small wrapper, try to decompose the candidate

For a proposed new system, actively ask:

- Can every new object be decomposed into “an old object plus an independent small label”?
- Does the new label change only after the old object has completed some phase, without participating in internal control?
- After removing the label, is expansion essentially just the old expansion repeated several times?
- Are the new levels or tree parameters merely decorative, or do they change source selection, the scope of copying, transport, and splice generation?
- Is the supposed enhancement merely a choice of farther-out seeds or a reindexing of the same fundamental sequences?

If the answers suggest “old-system body plus separable label,” seriously consider whether the gain in strength comes mainly from a wrapper.

These are diagnostic questions, not an ordinal-classification theorem. Conversely, failing to see a decomposition does not prove that none exists.

### 11.3 More promising internal enhancements

A more promising direction is to make formerly fixed parameters participate in the structure's internal interactions. For example:

- Replace fixed row labels with references to earlier columns, and transport those references during copying.
- Change which roots, rows, or contexts may control the last column, so that the new relations actually affect the next expansion.
- Let newly generated structure become a source of control for later expansions, rather than a one-use decoration.
- Introduce new dependencies between previously independent levels while retaining simple finite relations.

These mechanisms might still be simulated by the old notation, or they might destroy well-foundedness. Label them as candidate mechanisms. The mere presence of feedback is not a proof of a strict increase in strength.

### 11.4 What counts as evidence of strength?

During research, a provisional judgment such as “very likely no smaller” is acceptable, but explain the mechanism and actively look for a simulation in the opposite direction.

More reliable evidence includes explicit order embeddings, simulations of rules, coverage of standard domains, or lower bounds on order type. Remember that an order embedding, a fundamental-sequence simulation, and an initial-segment embedding impose different requirements. They must not be passed off as interchangeable.

Slower computations, larger counts, deeper graphs, stronger ready-made proof theorems, and an `Ω` in the name are not evidence of this kind.

Do not assume that putting a familiar collapsing function, tree order, or higher-order label around an already large notation must produce an important enhancement. Relative strength needs investigation, not a judgment based on familiarity.

## 12. Well-ordering proofs should guide design, not act as strength labels

### 12.1 Borrow proof ideas rather than fixing the name of an axiom system

Earlier research considered finite relations, source transport, splice construction, finite demands, semantic representations, and reflection. A new design can borrow these ideas to understand why, after the last-column control is lowered, newly generated material can still be placed below the original object.

Not every future candidate must remain forever within $KP_\omega+$“there exists an uncountable ordinal.” A stronger theory is allowed if the structure naturally calls for it and the reason can be explained.

What is objectionable is arbitrarily adding a powerful axiom one does not understand, merely to look stronger, and then declaring the goal achieved. Axiom requirements should arise from specific proof steps.

### 12.2 An axiomatic upper bound is not the notation's exact strength

If the same theory proves two notations well-ordered, their order types need not be close. Nor does a particular proof's use of a stronger theory imply that its notation is larger; the proof may simply be unoptimized.

Distinguish:

- The object's actual order type.
- Proved upper and lower bounds on order type, or embedding relations.
- The axiomatic upper bound supplied by the current proof.
- Lower bounds on the required axiomatic strength, or unprovability results.

Do not infer the fourth item from the third. Likewise, successful compilation in ordinary Lean must not be described as “a formalization inside a particular weak set theory.” That requires separately encoding the object theory and its derivations.

### 12.3 A proof strategy should answer three questions clearly

First, why do the finite rules always produce structurally legal objects, with no omissions in coordinate transport?

Second, given a proposed semantics or rank, why does every nonzero expansion descend? In particular, why do new splices and newly generated relations remain within the original bound?

Third, why does the theorem cover the claimed standard domain, and why does its semantics match the actual expansion rather than a different model chosen for ease of proof?

Under this document's structural contract, establishing the standard-domain interface and finiteness of local counts uniformly gives columnwise linear order and injective counts. Adding well-foundedness gives ordinal semantics, coverage by fundamental sequences, and uniqueness of intrinsic ordinal representation. There is no need to invent an unrelated comparison method from scratch for every new system.

## 13. Attractive counts are welcome, but should not take over the design

### 13.1 Numbers should be derived, not merely reassigned

Ideally, each column has a natural countdown that decreases by exactly one when that position is rewritten. Stronger landmark nodes would preferably appear as a short, structured sequence of small numbers rather than `(1,huge parameter)`.

However, “small numbers should come from the structure itself” and “count growth should not be conspicuously superexponential” are lower-priority suggestions. First obtain a promising core mechanism, then check whether these features can be improved naturally.

Do not merely change the top's display to `1,n` while keeping enormous hidden internal labels, then claim that the structure has become simple. Nor should small numbers be forced through numerous buffering states, decorative columns, and complicated conversion rules.

### 13.2 Injective does not mean cheap, or that arbitrary number sequences are valid inputs

Even a proved-injective exact count sequence on the standard domain may be difficult to compute. Its image may be a very special family of sequences. Recovering a standard column graph from an arbitrary numerical string requires an additional algorithm and a correctness proof.

It is therefore entirely reasonable to keep a lossless structural list as the core input, offer a count view as an attractive display, and implement the same order with a faster structural comparator.

“Counts suffice for comparison mathematically” and “the implementation should always compute all counts first” are different statements.

### 13.3 A counting algorithm should not simulate a global descending chain

Prefer recurrences in a fixed prefix context, finite states, shared subproblems, bulk elimination, or closed-form subcases. Do not construct and expand ever-larger whole expressions merely to obtain one column's countdown.

If no useful optimization is available, counting can have an independent resource budget. Report “not computed” clearly; do not substitute zero, infinity, a truncated large number, or a fake value that participates in comparison.

## 14. Presentation and implementation should follow the same aesthetic

### 14.1 Show the structure first

At minimum, provide a lossless, single-line, column-by-column list. If natural local counts are available, add a numerical-sequence view. Graphs and adjacency tables can aid understanding, but do not replace the mathematical object.

Separate columns with `[]` and retain empty columns. An adjacency table must distinguish “no edge” from “an edge whose parameter is zero”; zero must not be treated as a blank.

### 14.2 Graphs should be honest

In a mountain diagram, tree diagram, or arc diagram, every line, level marker, and parameter should correspond to a clearly defined relation. Layout heights introduced to avoid overlapping lines must not be mistaken for new mathematical levels.

Draw the whole graph when possible. If it is too large to draw completely, say so explicitly or use a clearly labeled navigable viewport. Do not silently show only part of it while implying that all relations are visible.

If drawing the graph is very difficult, a clear list is better than a misleading “mountain-like” picture. Do not distort the mathematical structure to preserve a particular appearance.

### 14.3 Engineering safeguards are not the definition

Mathematical integers, finite objects, and fundamental-sequence rules must not be determined by a website's default thresholds. Separate resource limits, caching strategies, and UI timeouts from the mathematical definition.

Experiments with large expansions need time, step, and memory budgets. Clean up unnecessary processes you started. Timeouts and limit violations indicate limitations of the current algorithm or resources, not evidence of an infinite descending chain.

If different language implementations or multiple NER expansion entry points claim to implement the same notation, align their index conventions and check their rules. A display layer must not silently replace the nth term with the (n+1)st.

## 15. A recommended workflow for the design agent

### Step 1: Deliver one page of actual definitions first

At least specify the column data structure, zero and seeds, the standard domain, control rules, last-column rewriting, append rules, and comparison interface. Do not build an elaborate UI first and then reverse-engineer a mathematical definition from it.

### Step 2: Prove the shape interface

Check preservation of the old prefix, deletion by `[0]`, prefix nesting across indices, stability under normalization, and seed compatibility. If a property holds only on the standard domain, identify the invariant that establishes it.

### Step 3: Establish local counts and structural comparison

Explain what local termination means, how $T_P$ is computed, and when termination can be proved. A conditional theorem may come first, followed by verification for the actual rules. If using a direct structural comparator, prove that it agrees with the intended reachability order or exact-count order.

Do not use “search expansions in both directions and see which reaches the other first” as an unproved comparator. A comparability theorem on the standard domain does not automatically provide an inexpensive search algorithm.

### Step 4: Work through small examples, but do not inspect only the numbers

Calculate by hand a successor, the smallest limit, the first complicated splice, a copy involving references, and an example where two operation paths merge into the same structure. Compare the complete column relations and counts side by side.

During copying, check which values are global constants, which are column addresses, and which are SELF markers (self-references to the current column). Verify that every reference needing transport or rebinding is handled according to the rules, and that closure supplies all necessary intermediate values.

### Step 5: Investigate well-foundedness and strength mechanisms in parallel

For well-ordering, look for descending semantics and splice invariants. For strength, look for embeddings of the old system, reverse simulations, and possible small-wrapper decompositions. Do not wait until extensive implementation is complete to discover that the enhancement is merely cosmetic or that the fundamental sequences can cycle.

### Step 6: Add presentation and performance optimization afterward

Get the canonical list right, then add counts and graphs. Optimizations must not change the mathematical rules. Necessary rule changes should receive a separate name or version, followed by renewed checks of interfaces and proofs.

### Step 7: Label the level of evidence at handoff

Distinguish design motivation, strength conjectures, finite tests, written proofs, ordinary Lean formalizations, and formalizations inside a specified weak theory. Do not let the next agent inherit research expectations as if they were proved theorems.

## 16. Candidate-notation acceptance checklist

### Mathematical interface

- [ ] Expressions are explicitly defined finite column structures, independent of operation history.
- [ ] For an ordinary nonzero expression, `[0]` deletes exactly the last column.
- [ ] Expansion preserves the entire old prefix, and normalization does not alter it.
- [ ] `A[n]` is a complete structural prefix of `A[n+1]`.
- [ ] Exceptions for successors, zero, and the external top are explicit and limited.
- [ ] The standard reachable domain and seed compatibility have independent definitions and justifications.
- [ ] An individual expansion is a finite executable rule, not a call to an unknown semantic decision procedure.
- [ ] Local rewriting and countdowns are defined precisely; termination and computation methods are not confused.
- [ ] Comparison and uniqueness claims for standard expressions use the correct domain.
- [ ] Well-foundedness is not claimed merely because “a number decreases by one” or because finite tests pass.

### Aesthetics and strength

- [ ] The core definition is short and readable, without hiding complexity in black boxes.
- [ ] An entire enormous notation is not embedded inside a column without justification.
- [ ] Parameters are few and purposeful; levels and addresses have clear meanings.
- [ ] The enhancement changes internal interactions rather than merely attaching labels to the old system.
- [ ] Simulations by the old notation and small-wrapper decompositions have been actively sought.
- [ ] Strength expectations have a mechanistic rationale, not running time or count size offered as proof.
- [ ] The main objectives have not been sacrificed to the low-priority preference for small numbers.
- [ ] Axiom requirements come from specific proof steps, not powerful axiom names used as decoration.

### Implementation and handoff

- [ ] A lossless columnwise list is available; zero and an empty column, and missing edges and zero parameters, are distinct.
- [ ] Exact counting, structural comparison, expansion, and drawing are kept separate.
- [ ] The domain of count injectivity is explicit; no unproved inverse for arbitrary numerical strings is promised.
- [ ] Graphs are complete and faithful; unfinished computations are reported explicitly.
- [ ] Resource safeguards are not disguised as mathematical rules; experiments are bounded and processes are cleaned up.
- [ ] The correspondence between language implementations, index conventions, and mathematical definitions is checked.
- [ ] Documentation distinguishes proved properties, conditional conclusions, and strength judgments still under investigation.

## 17. A short brief that can be handed directly to a new agent

> We want to design “large and beautiful” fundamental-sequence ordinal notations. An ordinary expression is a finite sequence of columns. The mathematical object is the structure itself, not a record of operations from the top. Expansion may only delete or modify the last column and then append to the right; the old prefix remains completely unchanged; `A[0]` deletes the last column; and `A[n]` must be a prefix of `A[n+1]` as a sequence of complete columns. Copying n times is not compulsory. An adjoined top may be an exception, but its seeds should be compatible, and the standard domain consists of finite expansion descendants of the designated seeds.
>
> On such a standard domain, nested fundamental sequences already make reachability total. If local last-column countdowns are finite, they exclude cycles and make exact count sequences an injective lexicographic representation, without first requiring global well-ordering. A separate proof that no infinite descending chain exists is still needed for a genuine ordinal interpretation. Do not use arbitrary unreachable handwritten expressions to challenge uniqueness on the standard domain, and do not mistake lexicographic descent for a global well-ordering proof.
>
> The aesthetic priorities are a readable short definition, simple individual columns, and substantive internal enhancement. Do not hide a complex tree or another entire ordinal notation inside each edge, or merely wrap the old system in an easily separable outer layer. Borrow ideas from existing well-ordering proofs; stronger axioms are allowed when there is a natural reason, but an axiomatic upper bound is not evidence of order-type size. Small numbers and gentle count growth are low-priority preferences: welcome when natural, not mandatory. Design the core first, then verify the structural interface, the route to well-foundedness, and the strength mechanism; finish with NER presentation and optimization.

## 18. Reading paths and the limits of this document

These design preferences come from repeated clarifications in this conversation about sequences, last-column expansion, prefixes, counts, simplicity, and substantive enhancement. They are not presented as a universal aesthetic standard shared by all mathematicians.

For concrete finite-relation examples, read the definitions of [RPD](../notations/RPD/definition.md), [ARD](../notations/ARD/definition.md), and [ARD2](../notations/ARD2/definition.md). To understand the representational cost of trees inside columns, compare [IPD](../notations/IPD/definition.md). These links supply structural examples. This document does not establish order-type inequalities between those systems and Y or wY, or among the systems themselves.

Section 6 gives a general argument under explicitly listed assumptions. Before applying it to a particular notation or program, check that the same fundamental sequences, standard domain, local countdowns, and all hypotheses are implemented. It does not replace definition-consistency audits of those instances or automatically revise the proof claims already in the repository.
