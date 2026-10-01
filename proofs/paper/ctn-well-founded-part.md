# The maximal well-founded initial segment of CTN · [中文版](ctn-well-founded-part.zh-CN.md)

Packaged 2026-10-01. CTN means the [current linear-limit definition](../../notations/CTN/definition.md), formerly called CTN2. This manuscript combines the finite-table-tree argument with successor-chain padding. It needs no unimplemented abstract Kleene-tree oracle and does not retain the retired frontend.

**CTN is ill-founded, but its maximal well-founded initial segment has order type $\omega_1^{CK}$.** This is a paper argument using classical computable structure theory, not a Lean theorem or a newly independently refereed result. Ordinary classical set theory suffices as the metatheory below; no optimal axiom bound is claimed. CTN is not added to the repository's weak-KP well-ordering collection.

## 1. The finite checker defines a computable tree

Let T be the natural-number tables accepted by [ctn_table.py](../../notations/CTN/ctn_table.py). Only addresses below the current length are tested. Decoding and local obligations are finite computations. Missing dependencies defer a check; there is no recursive truth evaluation or satisfiability search.

A rejected table has a finite failure witness consisting of fields already present. Extensions preserve their values and keep the check enabled. Rejection is permanent, so T is prefix-closed. Acceptance does not promise an infinite extension; retaining that undecidable global question is intentional.

## 2. T has a path

In the metatheory, consider $(\mathbb N,\mathcal P(\mathbb N))$ as a two-sorted first-order structure in a countable language. Take a countable elementary substructure containing every natural number. Its number sort remains standard; enumerate its set sort as $(X_i)_{i<\omega}$.

Fill M with actual membership, V with satisfaction in this ω-model, W with chosen witnesses for true existentials, and C with indices for comprehension sets. Put 0 in reserved/invalid fields. Full comprehension supplies all required rows. Every finite prefix of this infinite table lies in T.

The elementary-substructure and witness choices occur only in this existence proof, never in the expansion algorithm.

## 3. Every path encodes an ω-model of Z₂

For $f\in[T]$, set $X_i=\{n:M(i,n)=1\}$. Induction on finite formulas identifies V with satisfaction in $(\mathbb N,\{X_i:i<\omega\})$:

- Atomic and Boolean clauses have their prescribed meanings.
- True existentials have the instance supplied by W.
- Each number or set-index instance of a false existential has a checking address. Every fixed instance and all its dependencies eventually appear along f, ruling out any true instance.

Comprehension checks supply the row for every formula-defined set. The standard number sort validates induction. The resulting structure is an ω-model of Z₂, not necessarily a β-model, and its set domain is not asserted to contain all external reals.

## 4. T has no hyperarithmetic path

Use the classical fact that every ω-model of ATR₀, hence of Z₂, contains all hyperarithmetic sets. A genuinely recursive well-order still has no descending sequence in an ω-model; arithmetic transfinite recursion along it gives the correct jump hierarchy, explaining this closure property.

If f were hyperarithmetic, its Turing jump $f'$ would also be hyperarithmetic and would occur as some row $X_i$. But every $X_i\le_T f$, by querying its membership fields. This implies $f'\le_T f$, contradicting strictness of the Turing jump.

Thus T has paths but no hyperarithmetic paths. Coordinatewise addition of one yields the tree U in the [definition](../../notations/CTN/definition.md); its paths and T's paths compute each other.

For the ω-model closure background, see Montalbán's [Theories of Hyperarithmetic Analysis](https://math.berkeley.edu/~antonio/slides/FriedmanFestH.pdf) and [Indecomposable Linear Orderings and Hyperarithmetic Analysis](https://math.berkeley.edu/~antonio/papers/indec.pdf). These are classical inputs, not new results of this project.

## 5. Column order and linear successor tails

For $s\in U$, put $C(s)=E(s)2$ and $q(s,k)=E(s)1\,2^k$. Branch intervals are arranged in natural-number order between the entry and cap:

- If $s^\frown k\in U$, the interval after q(s,k) contains the child's entire interval, followed by its cap and the cap's finite tails of ones, before q(s,k+1).
- Otherwise the interval contains only the terminal successor chain $q(s,k)1,q(s,k)11,\ldots$.

Each padding tail is a genuine ω-chain, not a new ill-founded component.

An expression ending in 1 has its deleted prefix as immediate predecessor. The three ending-in-2 cases enumerate branch separators, a valid child's post-cap tail, or a failed child's terminal tail. These are cofinal below their endpoints and have no last element. Hence ending in 2 is precisely having no direct predecessor. Replacing the last 2 by a string starting with 1 gives strict lexicographic descent, while the displayed formulas give complete prefix coherence.

From C(s), one can reach any separator. To enter child k, first reach q(s,k+1), then the child's cap, and repeat there. Each entry consumes a whole block of the finite target expression, so this construction finishes. For successor tails choose a sufficiently large index and then delete extra ones. For general B<A, truncate to the first difference and use these cases. Therefore

$$B<A\quad\Longleftrightarrow\quad B\text{ is reachable from A by a nonempty finite expansion path}.$$

This does not assume well-foundedness. In particular, every legal expression is reachable from the top `2`.

## 6. Descending chains exist, but none is hyperarithmetic

A path g through U gives

$$C(\varnothing)>C(g\upharpoonright1)>C(g\upharpoonright2)>\cdots.$$

These are actual legal expressions. Each inequality decomposes into finitely many fundamental-sequence steps, so the entire domain is ill-founded.

Conversely, let d be an infinite descending sequence of expressions. Once it enters a node's branch interval, its branch number can only decrease or remain fixed, hence eventually stabilizes. An entry, separator or ω-shaped padding tail cannot contain infinite descent. A later tail must therefore lie inside one genuine child's subtree interval. Repeating this constructs a path through U.

Relative to d, the assertion that all terms after a specified index lie in a given child interval is $\Pi^0_1$. Thus $d'$ uniformly finds a suitable child and tail at each stage, and computes the entire path. Hyperarithmetic d would yield a hyperarithmetic path, contradicting Section 4.

## 7. Harrison's theorem identifies the CK cut

The legal domain is decidable and its comparison is computable. An effective repetition-free enumeration produces a computable copy on the natural numbers. It is ill-founded with no hyperarithmetic descending sequence. The corresponding consequence of Harrison's pseudo-well-order classification gives

$$\boxed{\operatorname{otp}(\operatorname{WF}(\mathrm{CTN}))=\omega_1^{CK}.}$$

WF denotes the maximal well-founded initial segment. See the Harrison pseudo-well-order section of Montalbán's [Computable Structure Theory, Part 2](https://math.berkeley.edu/~antonio/CSTpart2.pdf); the original result is Harrison's *Recursive pseudo-well-orderings* (1968). The present logical table and column wrapper are not fundamental-sequence rules taken from those sources.

The upper bound can also be explained directly: for a in WF, the strict lower set is decidable by `x<a` and is well-ordered. Its type is therefore a recursive ordinal, strictly below CK. The supremum of all these ranks is at most CK. The absence of hyperarithmetic descent supplies the classical input establishing the exact lower bound.

## 8. Important limitations

- No finite legal expression equals CK, and there is no first bad element: either would yield a computable well-order presentation of CK as its lower set.
- The well-founded part cannot be effectively enumerated exactly, for the same reason.
- Ignoring implementation resource guards, every total computable index-selection strategy has finite descent. Otherwise it would compute an infinite descending chain. Noncomputable infinite chains nevertheless exist.
- Z₂ specifies the models represented by infinite tables; this does **not** assert whole-system well-ordering in Z₂ or equality with PTO(Z₂).
- The CK result does not automatically provide an effective expression converter for Y, RPD, ARD or another notation, or locate a particular finite string.

## 9. Cost and implementation evidence

For actual input length L, the number of completed blocks and every decoded table value are at most L. Expansion uses linear parsing, at most two table checks and an $O(L+n)$ output. Visible addresses are bounded by L; decoded environment/formula lengths are $O(\log(L+2))$. New addresses use a fixed number of pairing layers, retain $O(\log(L+2))$ bit length and do not control array allocation.

With ordinary integer algorithms, a conservative bit-complexity bound is

$$O(L\log^4(L+2)+n)\text{ time,}\qquad O(L+n)\text{ space.}$$

This uses the raw unary string length, not the length of a compressed display, and is not a fixed-seconds promise. Resource guards are separate from the mathematical definition.

Tests of the independent five-family grammar, table clauses, cross-language expansions and small-ordinal address certificates are linked in the [definition](../../notations/CTN/definition.md) and [validation record](../../VALIDATION.md). They check the implementation, not absence of hyperarithmetic paths, and do not replace this infinite-structure argument.
