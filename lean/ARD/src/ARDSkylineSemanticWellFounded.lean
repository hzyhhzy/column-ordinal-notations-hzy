import ARDSkylineDomain

/-! A semantic descent adapter for the actual ARD fundamental sequence.
The final theorem instantiates all inputs with proved concrete results; this
adapter by itself is not an unconditional ARD well-ordering claim. -/

namespace OrdinalFormal.ARDSkyline
set_option autoImplicit false
universe u
variable {Label : Type u}

theorem empty_accessible : Acc Step [] :=
  Acc.intro [] (fun _ h => False.elim (h.1 rfl))

theorem accessible_of_bounded
    (lt : Label → Label → Prop) (D : Label → Prop)
    (R : Label → Label → Label → Label → Prop)
    (preserves : ∀ g n, Valid g → Valid (expand g n))
    (lowering : ∀ {g : Graph}, Valid g → g ≠ [] → ∀ f : Nat → Label,
      Holds lt D R g f → ∀ n,
      ∃ next, Holds lt D R (expand g n) next ∧
        ReflectionTransport.Bounded lt (expand g n).length next (f (g.length - 1)))
    (beta : Label) (hAcc : Acc lt beta) :
    ∀ g : Graph, Valid g → ∀ f : Nat → Label,
      Holds lt D R g f → f (g.length - 1) = beta → Acc Step g := by
  induction hAcc with
  | intro beta _ ih =>
    intro g hg f hF hLast
    apply Acc.intro g
    intro a hstep
    obtain ⟨hn, n, rfl⟩ := hstep
    by_cases hzero : expand g n = []
    · rw [hzero]
      exact empty_accessible
    · obtain ⟨next, hNext, hBound⟩ := lowering hg hn f hF n
      have hPos : 0 < (expand g n).length := by
        cases h : expand g n <;> simp_all
      have hLower := hBound ((expand g n).length - 1) (by omega)
      rw [hLast] at hLower
      exact ih _ hLower (expand g n) (preserves g n hg) next hNext rfl

theorem valid_accessible_of_bounded
    (lt : Label → Label → Prop) (D : Label → Prop)
    (R : Label → Label → Label → Label → Prop)
    (hWF : WellFounded lt)
    (preserves : ∀ g n, Valid g → Valid (expand g n))
    (lowering : ∀ {g : Graph}, Valid g → g ≠ [] → ∀ f : Nat → Label,
      Holds lt D R g f → ∀ n,
      ∃ next, Holds lt D R (expand g n) next ∧
        ReflectionTransport.Bounded lt (expand g n).length next (f (g.length - 1)))
    (initial : ∀ g : Graph, Valid g → ∃ f : Nat → Label, Holds lt D R g f)
    (g : Graph) (hg : Valid g) : Acc Step g := by
  obtain ⟨f, hF⟩ := initial g hg
  exact accessible_of_bounded lt D R preserves @lowering _ (hWF.apply _) g hg f hF rfl

theorem valid_step_wellFounded_of_accessible
    (accessible : ∀ g : Graph, Valid g → Acc Step g) :
    WellFounded (fun a b : {g : Graph // Valid g} => Step a.val b.val) := by
  constructor
  intro g
  exact InvImage.accessible (fun g : {g : Graph // Valid g} => g.val)
    (accessible g.val g.property)

#print axioms accessible_of_bounded
#print axioms valid_accessible_of_bounded
#print axioms valid_step_wellFounded_of_accessible

end OrdinalFormal.ARDSkyline


