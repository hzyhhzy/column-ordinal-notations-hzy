import OrdinalFormal.GeneratedStagedReflection
import OrdinalFormal.Reachability

/-!
# Accessibility of actual generated-row expansion from semantic inputs

Generalized from the local `RPDSemanticWellFounded.lean`; that module is unchanged.
Actual block construction, representation lowering, and geometric validity are
proved by the imported executable-geometry modules, not assumed here. Remaining
inputs are precisely a well-founded semantic label order, its reflection and
lower-row laws, and initial representations. This is not an unconditional
well-ordering theorem for LRD or Omega-LRD2.
-/

namespace OrdinalFormal.GeneratedSemanticWellFounded

open Columns
set_option autoImplicit false
set_option maxHeartbeats 700000
universe u v
variable {Row : Type u} {Label : Type v}
variable (cmp : Row → Row → Ordering) (package : Package Row)

abbrev Step : Graph Row → Graph Row → Prop := FSStep [] (expand cmp package)

theorem empty_accessible : Acc (Step cmp package) [] :=
  Acc.intro [] (fun _ h => False.elim (h.1 rfl))

theorem accessible_of_last_label
    (rowLt : Row → Row → Prop)
    (lt : Label → Label → Prop) (D : Label → Prop)
    (R : Row → Label → Label → Label → Prop)
    (hTrans : ∀ {a b c}, lt a b → lt b c → lt a c)
    (hStrict : ∀ {k index a b}, R k index a b → lt a b)
    (hWeak : ∀ {k small large p c}, lt small large → R k large p c → R k small p c)
    (hLower : ReflectionTransport.LowerRows rowLt lt R)
    (hPackage : ∀ high b low, low ∈ package high b → rowLt low high)
    (laws : ColumnRepresentation.RowCompareSound cmp rowLt)
    (reflection : ReflectionTransport.FiniteReflection rowLt lt D R)
    (beta : Label) (hAcc : Acc lt beta) :
    ∀ (g : Graph Row), Valid g → ∀ f : Nat → Label,
      ColumnRepresentation.Holds lt D R g f → f (g.length - 1) = beta →
        Acc (Step cmp package) g := by
  induction hAcc with
  | intro beta _ ih =>
    intro g hg f hF hLast
    apply Acc.intro g
    intro a hstep
    obtain ⟨hn, n, rfl⟩ := hstep
    by_cases hzero : expand cmp package g n = []
    · rw [hzero]
      exact empty_accessible cmp package
    · obtain ⟨next, hNext, hBound⟩ :=
        GeneratedStagedReflection.fs_bounded cmp package rowLt lt D R
          hTrans hStrict hWeak hLower hPackage laws reflection hg hn f hF n
      have hPos : 0 < (expand cmp package g n).length := by
        cases h : expand cmp package g n <;> simp_all
      have hLowerLabel := hBound ((expand cmp package g n).length - 1) (by omega)
      rw [hLast] at hLowerLabel
      exact ih _ hLowerLabel (expand cmp package g n)
        (ExpansionValidity.expand_valid cmp package g n hg) next hNext rfl

theorem valid_accessible_of_semantics
    (rowLt : Row → Row → Prop)
    (lt : Label → Label → Prop) (D : Label → Prop)
    (R : Row → Label → Label → Label → Prop)
    (hWF : WellFounded lt)
    (hTrans : ∀ {a b c}, lt a b → lt b c → lt a c)
    (hStrict : ∀ {k index a b}, R k index a b → lt a b)
    (hWeak : ∀ {k small large p c}, lt small large → R k large p c → R k small p c)
    (hLower : ReflectionTransport.LowerRows rowLt lt R)
    (hPackage : ∀ high b low, low ∈ package high b → rowLt low high)
    (laws : ColumnRepresentation.RowCompareSound cmp rowLt)
    (reflection : ReflectionTransport.FiniteReflection rowLt lt D R)
    (initial : ∀ (g : Graph Row), Valid g →
      ∃ f : Nat → Label, ColumnRepresentation.Holds lt D R g f)
    (g : Graph Row) (hg : Valid g) : Acc (Step cmp package) g := by
  obtain ⟨f, hF⟩ := initial g hg
  exact accessible_of_last_label cmp package rowLt lt D R hTrans hStrict hWeak
    hLower hPackage laws reflection _ (hWF.apply _) g hg f hF rfl

/-- No seed accessibility, output validity, or expansion-decrease premise is
left here. In particular the predicate restricts geometry, not accessibility. -/
theorem valid_step_wellFounded_of_semantics
    (rowLt : Row → Row → Prop)
    (lt : Label → Label → Prop) (D : Label → Prop)
    (R : Row → Label → Label → Label → Prop)
    (hWF : WellFounded lt)
    (hTrans : ∀ {a b c}, lt a b → lt b c → lt a c)
    (hStrict : ∀ {k index a b}, R k index a b → lt a b)
    (hWeak : ∀ {k small large p c}, lt small large → R k large p c → R k small p c)
    (hLower : ReflectionTransport.LowerRows rowLt lt R)
    (hPackage : ∀ high b low, low ∈ package high b → rowLt low high)
    (laws : ColumnRepresentation.RowCompareSound cmp rowLt)
    (reflection : ReflectionTransport.FiniteReflection rowLt lt D R)
    (initial : ∀ (g : Graph Row), Valid g →
      ∃ f : Nat → Label, ColumnRepresentation.Holds lt D R g f) :
    WellFounded (fun a b : {g : Graph Row // Valid g} => Step cmp package a.val b.val) := by
  constructor
  intro g
  exact InvImage.accessible (fun g : {g : Graph Row // Valid g} => g.val)
    (valid_accessible_of_semantics cmp package rowLt lt D R hWF hTrans hStrict
      hWeak hLower hPackage laws reflection initial g.val g.property)

#check valid_step_wellFounded_of_semantics
#print axioms accessible_of_last_label
#print axioms valid_accessible_of_semantics
#print axioms valid_step_wellFounded_of_semantics

end OrdinalFormal.GeneratedSemanticWellFounded
