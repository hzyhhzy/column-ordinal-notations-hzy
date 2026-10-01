# The exact ω^ω location in CTN · [中文版](omega-omega.zh-CN.md)

Research dated 2026-09-28; renamed and packaged on 2026-10-01. The checker [ctn_table.py](ctn_table.py) and current [ctn.py](ctn.py) rules are unchanged mathematically from the research edition called CTN2. This is a paper argument with reproducible finite calculations, not a Lean proof.

## 1. Expression and size

Let g be the actual-value table in [omega-omega.sparse.json](fixtures/omega-omega.sparse.json): length **23,191,452**, with **4,352 nonzero fields**, all omitted fields zero. With the usual encoding,

$$F(g)=\prod_{j<|g|}1\,2^{g_j+1}1,\qquad |F(g)2|=\omega^\omega.$$

Powers mean literal repetition and the product means concatenation. The raw expression has **69,593,927 columns**. The sparse table is a lossless external description of this one fixed expression, not a change to the notation's runtime representation. The approximately 70 MB expanded word is not bundled and ordinary NER limits still apply.

[locate_omega_omega.py](locate_omega_omega.py) generates the sparse certificate using [ctn_sparse.py](ctn_sparse.py); it visits only potentially active addresses and does not descend through fundamental sequences or allocate millions of table cells.

## 2. The decisive false existential

Use $\varphi(x,y)=\exists S\,(y=x)$. The bound set variable is unused, but the syntax permits it. The fixed encoding gives:

| Item | Code / address |
| --- | --- |
| EQUAL(1,0) | Formula 4 |
| EXISTS_S(EQUAL(1,0)) | Formula 95 |
| C(φ, number parameters (1), no set parameters) | 11,802,507 |
| V(φ, number parameters (0,1), no set parameters) | 23,184,643 |
| W(φ, number parameters (0,1), no set parameters) | 23,191,452 |

The comprehension field chooses row **3**, previously fixed as all natural numbers. It therefore forces V=1 at x=0: “there is a set S such that 1=0.” The prefix g stops immediately before the witness field.

Why row 3? The actual comprehension set is {1}. Rows 0, 1 and 2 were already forced to omit 1, while row 3 includes {1}. Its extra members can only be refuted by the false existential's as-yet-unspecified witness. The inconsistency can therefore be deferred for arbitrarily long finite tables.

## 3. Every fixed child has finite height

If the witness is w, the positive existential reads

$$u(w)=\operatorname{truth\_address}(4,6,\operatorname{cons}(w,0)).$$

Here 6 encodes the number environment (0,1). Arithmetic at u(w) forces V(1=0)=0, while the parent existential demands 1. Once the length reaches $\max(|g|+1,u(w)+1)$, every extension fails, regardless of its intervening values.

| w | u(w) |
| --- | --- |
| 0 | 175,526 |
| 1 | 445,094 |
| 2 | 2,158,001 |
| 3 | 14,329,979 |
| 4 | 103,140,701 |
| 5 | 709,608,626 |
| 6 | 4,414,099,859 |

Witnesses 0–3 fail immediately. The first accepted child is w=4, but it too has a fixed finite extension bound.

## 4. The local type is ω^ω

For a well-founded subtree, the [branch formula](small-ordinals.md) yields δ(s)≤ω^(h+2) when the remaining table height is at most h. If every individual child has finite height, their countable sum is at most ω^ω even when the bounds vary with the child. This gives δ(g)≤ω^ω.

For the reverse bound, unbounded height alone is insufficient. The logical checker supplies a stronger property. For any r, choose an accepted extension long enough to contain r fresh scoped comprehension fields, for instance x=x with differing number parameters. Let its length be m. Independently change these fields to arbitrary row numbers greater than m. Their comprehension checks now encounter missing membership addresses and become pending. No other check reads C, so no new failure is introduced. This gives r nested, naturally ordered infinite branchings. Arbitrary r forces the local column type to be at least ω^ω.

Section 6 establishes that g has extensions of every finite length. Combined with the fixed-child bounds, it follows that δ(g)=ω^ω.

## 5. From local to global equality

Call a prefix U-type if it has accepted extensions of every finite length. The locator selects the smallest U-type value at each address, stopping at g when no child is U-type. Every earlier skipped child consequently has a uniform finite height bound and column type below ω^ω.

The path g and all its values are finite, so only finitely many such earlier blocks and padding chains precede F(g). Ordinals below ω^ω are closed under finite sums. Therefore

$$|F(g)|<\omega^\omega,\qquad |F(g)2|=|F(g)|+\delta(g)=\omega^\omega.$$

This argument requires a valid U-type criterion for this particular finite fragment, not a general undecidable extension oracle. The next section records that restricted criterion.

## 6. The restricted symbolic calculation

### Formula range

Before the stopping address, the greatest scoped formula code is **113**. Negations and conjunctions have quantifier-free, membership-free children. Membership atoms occur alone. Number existentials have codes `36,46,57,69,82,96,111`, with bodies 0–6; set existentials have codes `45,56,68,81,95,110`, with bodies 0–5, none using the bound set variable.

| Number-existential body code | Meaning | Smallest witness when true |
| --- | --- | --- |
| 0 | ∃z(z=0), always true | 0 |
| 1 | ∃z(z=z), always true | 0 |
| 2 | ∃z(x=0), equivalent to x=0 | 0 |
| 3 | ∃z(z+1=z), false | None |
| 4 | ∃z(x=z), true | x |
| 5 | ∃z(y=0), equivalent to y=0 | 0 |
| 6 | ∃z(z+z=z), true | 0 |

Comprehension sets in this range are finite/cofinite arithmetic sets, existing set rows, or the empty/full set determined by one fixed membership bit. Arithmetic requires only nonnegative integer roots of degree-at-most-two integer polynomials, complement and intersection.

### Constraints and finite refutations

For each row-equivalence class, maintain known bits, an optional exact finite/cofinite set and a finite/cofinite lower bound. Quantifier-free comprehension requires exact equality or row identification. An existential whose witness is not yet fixed only requires its true set to be included in the chosen row: a true point cannot be labeled false, while a false point temporarily labeled true can defer its false witness beyond any proposed finite horizon.

Conflicting exact sets, lower bounds or bits produce a particular natural-number witness. Arithmetic clauses, a fixed true existential witness and comprehension tests turn that conflict into finitely many fixed checking addresses. Consequently every such rejected choice has a uniform finite extension bound. A lower bound must not be mistaken for an exact set.

### Minimal choices

The locator visits addresses in order:

1. Fill a membership bit with 1 if forced, otherwise 0.
2. Use the constrained truth of a quantifier-free formula.
3. At comprehension, choose the first compatible row, recording exact equality, row equality or an existential lower bound.
4. Obey already assigned comprehension truth; otherwise use actual existential truth. A genuinely true existential cannot be false. A false one may remain temporarily true before its witness field.
5. A false parent gets witness 0. A truly true parent gets its least true witness (0 for set quantifiers). If a false formula has been assigned true, every fixed witness has a finite failure bound, so stop.
6. All other fields take the forced value 0.

Every smaller rejected choice in steps 1–4 has a finite refutation of the preceding kind; bad witnesses in step 5 have the atomic finite refutation. Free membership bits cause no hidden preference for 1: choosing 0 allows the minimal empty row 0, while 1 cannot allow a smaller row. Membership is not nested under negation or conjunction in this fragment.

### Arbitrarily long finite completions

For any horizon m, choose sets satisfying the consistent exact/lower/bit constraints. Fill visible consequences accordingly. Previously forced false existentials assigned true have no previously fixed witness: choose a witness large enough to defer its instance beyond m. Previously false existentials are genuinely false and can be filled honestly. Give new existential assertions deferred witnesses as necessary, propagate Boolean clauses and choose fresh comprehension rows whose membership addresses exceed m.

Old quantifier-free formulas contain no new quantifiers; old quantified bodies are the listed arithmetic atoms, so this does not corrupt existing truth values. Already fixed witnesses are true witnesses. The resulting finite table extends the prefix. Together with the finite refutations, this justifies the minimal U-type choices in this restricted range, not merely heuristic finite testing.

The first stopping field is 23,191,452, formula 95, number environment (0,1), empty set environment. Other relaxed comprehensions exist earlier but have later bad-witness addresses; the locator records them instead of silently ignoring them.

## 7. Reproduction and scope

From the repository root:

```sh
python -B notations/CTN/locate_omega_omega.py
python -B tests/ctn_omega_omega.py
```

`--sparse` prints the exact actual-value table as JSON. The checked fixture must match every generated nonzero field and both lengths. There are only O(√m) potentially active addresses: other kinds and invalid scopes are forced to 0 with no further obligation. All active fields are rechecked with the original logical checker.

The generator rejects formulas outside its audited fragment; it is not a universal U-type decision procedure. Tests do not prove the global ordinal equality, which relies on Sections 3–6. ε₀ remains unlocated.
