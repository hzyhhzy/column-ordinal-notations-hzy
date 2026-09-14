import Mathlib.ModelTheory.Semantics
import Mathlib.SetTheory.Ordinal.Basic

/-!
# Actual mixed first-order languages with arbitrary lower-row symbols

This generalizes the syntax/reduct layer of the fixed upstream
`OneYTruth.Language`: `Fin k` is replaced by an arbitrary type `D`. It uses
Mathlib's finite first-order formulas and its genuine realization relation.
The two index types are *symbols*, not additional sorts or quantified terms.
No reflection, truth-tower adequacy, or well-ordering assertion is assumed.
-/

namespace OrdinalRow

open FirstOrder FirstOrder.Language

universe u v w x y z

inductive Relation (D : Type u) (I : Type v) : Nat → Type (max u v)
  | mem : Relation D I 2
  | diagonal (d : D) : Relation D I 3
  | named (i : I) : Relation D I 2

abbrev language (D : Type u) (I : Type v) : FirstOrder.Language where
  Functions _ := Empty
  Relations := Relation D I

instance (D : Type u) (I : Type v) : (language D I).IsRelational :=
  fun _ => by dsimp [language]; infer_instance

/-- Both maps act on predicate symbols, never on an interpreted index term. -/
def symbolMap {D : Type u} {E : Type v} {I : Type w} {J : Type x}
    (df : D → E) (nf : I → J) : language D I →ᴸ language E J where
  onFunction := fun {_} e => nomatch e
  onRelation := fun {_} r => match r with
    | .mem => .mem
    | .diagonal d => .diagonal (df d)
    | .named i => .named (nf i)

structure Interpretation (D : Type u) (I : Type v) (A : Type w) where
  mem : A → A → Prop
  diagonal : D → A → A → A → Prop
  named : I → A → A → Prop

@[instance_reducible]
def Interpretation.structure {D : Type u} {I : Type v} {A : Type w}
    (M : Interpretation D I A) : (language D I).Structure A where
  funMap := fun {_} e => nomatch e
  RelMap := fun {_} r xs => match r with
    | .mem => M.mem (xs 0) (xs 1)
    | .diagonal d => M.diagonal d (xs 0) (xs 1) (xs 2)
    | .named i => M.named i (xs 0) (xs 1)

def Interpretation.restrict {D : Type u} {E : Type v} {I : Type w}
    {J : Type x} {A : Type y} (M : Interpretation E J A)
    (df : D → E) (nf : I → J) : Interpretation D I A where
  mem := M.mem
  diagonal d := M.diagonal (df d)
  named i := M.named (nf i)

theorem restrict_structure {D : Type u} {E : Type v} {I : Type w}
    {J : Type x} {A : Type y} (M : Interpretation E J A)
    (df : D → E) (nf : I → J) :
    (M.restrict df nf).structure =
      @LHom.reduct (language D I) (language E J) (symbolMap df nf) A M.structure := by
  apply FirstOrder.Language.Structure.ext
  · funext n e
    nomatch e
  · funext n r xs
    cases r <;> rfl

def realize {D : Type u} {I : Type v} {A : Type w} {α : Type x} {n : Nat}
    (M : Interpretation D I A) (φ : (language D I).BoundedFormula α n)
    (v : α → A) (xs : Fin n → A) : Prop :=
  @BoundedFormula.Realize (language D I) A M.structure α n φ v xs

/-- Exact reduct semantics for every finite first-order formula, with quantifiers. -/
theorem realize_symbolMap {D : Type u} {E : Type v} {I : Type w}
    {J : Type x} {A : Type y} {α : Type z} {n : Nat}
    (M : Interpretation E J A) (df : D → E) (nf : I → J)
    (φ : (language D I).BoundedFormula α n) (v : α → A) (xs : Fin n → A) :
    realize M ((symbolMap df nf).onBoundedFormula φ) v xs ↔
      realize (M.restrict df nf) φ v xs := by
  letI := M.structure
  letI := (symbolMap df nf).reduct A
  change ((symbolMap df nf).onBoundedFormula φ).Realize v xs ↔
    @BoundedFormula.Realize (language D I) A
      (M.restrict df nf).structure α n φ v xs
  rw [restrict_structure]
  exact (symbolMap df nf).realize_onBoundedFormula φ

theorem restrict_comp {D : Type u} {E : Type v} {F : Type w}
    {I : Type x} {J : Type y} {K : Type z} {A : Type*}
    (M : Interpretation F K A) (df : D → E) (dg : E → F)
    (nf : I → J) (ng : J → K) :
    (M.restrict dg ng).restrict df nf = M.restrict (dg ∘ df) (ng ∘ nf) := rfl

/-! ## Finite support on both predicate families -/

section FiniteSupport

variable {D : Type u} {I : Type v} [DecidableEq D] [DecidableEq I]

def relationDiagonalSupport : {n : Nat} → Relation D I n → Finset D
  | _, .mem => ∅
  | _, .diagonal d => {d}
  | _, .named _ => ∅

def relationNamedSupport : {n : Nat} → Relation D I n → Finset I
  | _, .mem => ∅
  | _, .diagonal _ => ∅
  | _, .named i => {i}

def diagonalSupport {α : Type w} : {n : Nat} →
    (language D I).BoundedFormula α n → Finset D
  | _, .falsum => ∅
  | _, .equal _ _ => ∅
  | _, .rel r _ => relationDiagonalSupport r
  | _, .imp φ ψ => diagonalSupport φ ∪ diagonalSupport ψ
  | _, .all φ => diagonalSupport φ

def namedSupport {α : Type w} : {n : Nat} →
    (language D I).BoundedFormula α n → Finset I
  | _, .falsum => ∅
  | _, .equal _ _ => ∅
  | _, .rel r _ => relationNamedSupport r
  | _, .imp φ ψ => namedSupport φ ∪ namedSupport ψ
  | _, .all φ => namedSupport φ

omit [DecidableEq D] [DecidableEq I] in
theorem term_realize_irrel {A : Type w} {α : Type x}
    (M N : Interpretation D I A) (t : (language D I).Term α) (v : α → A) :
    @Term.realize (language D I) A M.structure α v t =
      @Term.realize (language D I) A N.structure α v t := by
  cases t with
  | var => rfl
  | func e => nomatch e

/-- Truth only depends on membership and the two finite symbol supports. -/
theorem realize_eq_of_support {A : Type w} {α : Type x} {n : Nat}
    (M N : Interpretation D I A) (φ : (language D I).BoundedFormula α n)
    (hmem : M.mem = N.mem)
    (hd : ∀ d ∈ diagonalSupport φ, M.diagonal d = N.diagonal d)
    (hn : ∀ i ∈ namedSupport φ, M.named i = N.named i)
    (v : α → A) (xs : Fin n → A) :
    realize M φ v xs ↔ realize N φ v xs := by
  induction φ with
  | falsum => rfl
  | equal t s =>
    simp only [realize, BoundedFormula.Realize]
    rw [term_realize_irrel M N t, term_realize_irrel M N s]
  | rel r ts =>
    cases r with
    | mem =>
      change M.mem
        (@Term.realize _ A M.structure _ (Sum.elim v xs) (ts 0))
        (@Term.realize _ A M.structure _ (Sum.elim v xs) (ts 1)) ↔
        N.mem (@Term.realize _ A N.structure _ (Sum.elim v xs) (ts 0))
          (@Term.realize _ A N.structure _ (Sum.elim v xs) (ts 1))
      rw [hmem, term_realize_irrel M N, term_realize_irrel M N]
    | diagonal d =>
      have h := hd d (by simp [diagonalSupport, relationDiagonalSupport])
      change M.diagonal d
        (@Term.realize _ A M.structure _ (Sum.elim v xs) (ts 0))
        (@Term.realize _ A M.structure _ (Sum.elim v xs) (ts 1))
        (@Term.realize _ A M.structure _ (Sum.elim v xs) (ts 2)) ↔
        N.diagonal d (@Term.realize _ A N.structure _ (Sum.elim v xs) (ts 0))
          (@Term.realize _ A N.structure _ (Sum.elim v xs) (ts 1))
          (@Term.realize _ A N.structure _ (Sum.elim v xs) (ts 2))
      rw [h, term_realize_irrel M N, term_realize_irrel M N,
        term_realize_irrel M N]
    | named i =>
      have h := hn i (by simp [namedSupport, relationNamedSupport])
      change M.named i
        (@Term.realize _ A M.structure _ (Sum.elim v xs) (ts 0))
        (@Term.realize _ A M.structure _ (Sum.elim v xs) (ts 1)) ↔
        N.named i (@Term.realize _ A N.structure _ (Sum.elim v xs) (ts 0))
          (@Term.realize _ A N.structure _ (Sum.elim v xs) (ts 1))
      rw [h, term_realize_irrel M N, term_realize_irrel M N]
  | imp φ ψ ihφ ihψ =>
    apply imp_congr
    · exact ihφ (fun d h => hd d (Finset.mem_union_left _ h))
        (fun i h => hn i (Finset.mem_union_left _ h)) xs
    · exact ihψ (fun d h => hd d (Finset.mem_union_right _ h))
        (fun i h => hn i (Finset.mem_union_right _ h)) xs
  | all φ ih =>
    exact forall_congr' (fun a => ih hd hn (xs := Fin.snoc xs a))

omit [DecidableEq D] [DecidableEq I] in
/-- Relational terms have variables only, so transport requires no index choice. -/
def transportTerm {E : Type w} {J : Type x} {α : Type y} :
    (language D I).Term α → (language E J).Term α
  | .var a => .var a
  | .func e _ => nomatch e

/-- Re-express a formula using only prescribed finite sets of both symbols. -/
def restrictFormula {α : Type w} (S : Finset D) (T : Finset I) : {n : Nat} →
    (φ : (language D I).BoundedFormula α n) → diagonalSupport φ ⊆ S →
      namedSupport φ ⊆ T →
      (language {d // d ∈ S} {i // i ∈ T}).BoundedFormula α n
  | _, .falsum, _, _ => .falsum
  | _, .equal t s, _, _ => .equal (transportTerm t) (transportTerm s)
  | _, .rel .mem ts, _, _ => .rel .mem (fun i => transportTerm (ts i))
  | _, .rel (.diagonal d) ts, hd, _ =>
      .rel (.diagonal ⟨d, hd (by simp [diagonalSupport, relationDiagonalSupport])⟩)
        (fun i => transportTerm (ts i))
  | _, .rel (.named i) ts, _, hn =>
      .rel (.named ⟨i, hn (by simp [namedSupport, relationNamedSupport])⟩)
        (fun i => transportTerm (ts i))
  | _, .imp φ ψ, hd, hn => .imp
      (restrictFormula S T φ (fun _ h => hd (Finset.mem_union_left _ h))
        (fun _ h => hn (Finset.mem_union_left _ h)))
      (restrictFormula S T ψ (fun _ h => hd (Finset.mem_union_right _ h))
        (fun _ h => hn (Finset.mem_union_right _ h)))
  | _, .all φ, hd, hn => .all (restrictFormula S T φ hd hn)

omit [DecidableEq D] [DecidableEq I] in
theorem symbolMap_transportTerm {E : Type w} {J : Type x} {α : Type y}
    (df : E → D) (nf : J → I) (t : (language D I).Term α) :
    (symbolMap df nf).onTerm (transportTerm t) = t := by
  cases t with
  | var => rfl
  | func e => nomatch e

/-- The finite-sub-language expression maps back to precisely the original syntax. -/
theorem symbolMap_restrictFormula {α : Type w} {n : Nat}
    (S : Finset D) (T : Finset I) (φ : (language D I).BoundedFormula α n)
    (hd : diagonalSupport φ ⊆ S) (hn : namedSupport φ ⊆ T) :
    (symbolMap (Subtype.val : {d // d ∈ S} → D)
      (Subtype.val : {i // i ∈ T} → I)).onBoundedFormula
      (restrictFormula S T φ hd hn) = φ := by
  induction φ with
  | falsum => rfl
  | equal t s =>
    simp only [restrictFormula, LHom.onBoundedFormula,
      symbolMap_transportTerm, Term.bdEqual]
  | rel r ts =>
    cases r <;>
      simp only [restrictFormula, LHom.onBoundedFormula,
        Relations.boundedFormula, Function.comp_def, symbolMap_transportTerm] <;> rfl
  | imp φ ψ ihφ ihψ =>
    simp only [restrictFormula, LHom.onBoundedFormula, ihφ, ihψ]
  | all φ ih =>
    exact congrArg BoundedFormula.all (ih hd hn)

/-- Actual finite factorization, simultaneously at a limit row and a limit root. -/
theorem exists_finite_fragment {α : Type w} {n : Nat}
    (φ : (language D I).BoundedFormula α n) :
    ∃ (S : Finset D) (T : Finset I)
      (ψ : (language {d // d ∈ S} {i // i ∈ T}).BoundedFormula α n),
      (symbolMap (Subtype.val : {d // d ∈ S} → D)
        (Subtype.val : {i // i ∈ T} → I)).onBoundedFormula ψ = φ :=
  ⟨diagonalSupport φ, namedSupport φ,
    restrictFormula _ _ φ (fun _ h => h) (fun _ h => h),
    symbolMap_restrictFormula _ _ _ _ _⟩

end FiniteSupport

/-! ## Strict ordinal-stage specialization -/

/-- The fixed outer row bound is represented in the type of the current row. -/
abbrev RowBelow (σ : Ordinal.{u}) := {ξ : Ordinal.{u} // ξ < σ}

/-- Only strict predecessors of the current row are diagonal symbols. -/
abbrev LowerRow {σ : Ordinal.{u}} (ξ : RowBelow σ) :=
  {δ : Ordinal.{u} // δ < ξ.val}

/-- Only strict predecessors of the current root are separately named symbols. -/
abbrev EarlierRoot (η : Ordinal.{u}) := {ν : Ordinal.{u} // ν < η}

abbrev stageLanguage {σ : Ordinal.{u}} (ξ : RowBelow σ) (η : Ordinal.{u}) :=
  language (LowerRow ξ) (EarlierRoot η)

theorem no_current_diagonal {σ : Ordinal.{u}} (ξ : RowBelow σ) (d : LowerRow ξ) :
    d.val ≠ ξ.val := ne_of_lt d.property

theorem no_current_named (η : Ordinal.{u}) (i : EarlierRoot η) :
    i.val ≠ η := ne_of_lt i.property

def lowerRowInclusion {σ : Ordinal.{u}} {ξ χ : RowBelow σ} (h : ξ.val ≤ χ.val) :
    LowerRow ξ → LowerRow χ := fun d => ⟨d.val, lt_of_lt_of_le d.property h⟩

def earlierRootInclusion {η θ : Ordinal.{u}} (h : η ≤ θ) :
    EarlierRoot η → EarlierRoot θ := fun i => ⟨i.val, lt_of_lt_of_le i.property h⟩

def stageMap {σ : Ordinal.{u}} {ξ χ : RowBelow σ} {η θ : Ordinal.{u}}
    (hr : ξ.val ≤ χ.val) (ht : η ≤ θ) : stageLanguage ξ η →ᴸ stageLanguage χ θ :=
  symbolMap (lowerRowInclusion hr) (earlierRootInclusion ht)

/-- This is a genuine formula-reduct theorem; it is not a reflection theorem. -/
theorem realize_stageMap {σ : Ordinal.{u}} {ξ χ : RowBelow σ}
    {η θ : Ordinal.{u}} {A : Type v} {α : Type w} {n : Nat}
    (hr : ξ.val ≤ χ.val) (ht : η ≤ θ)
    (M : Interpretation (LowerRow χ) (EarlierRoot θ) A)
    (φ : (stageLanguage ξ η).BoundedFormula α n) (v : α → A) (xs : Fin n → A) :
    realize M ((stageMap hr ht).onBoundedFormula φ) v xs ↔
      realize (M.restrict (lowerRowInclusion hr) (earlierRootInclusion ht)) φ v xs :=
  realize_symbolMap M _ _ φ v xs

end OrdinalRow
