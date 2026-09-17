import ARD2Final
import ARD2SkylineSemanticWellFounded
import ARD2SkylineOrderReduction

/-! Unconditional well-ordering of the skyline edition's actual finite rules
and reachable column-comparison domain. Ordinary Lean foundations only.
The old semantics is reused by a proved subdiagram bridge, not by identifying
new standard terms with raw legacy graphs. This file does not formalize the
paper order-type comparisons or the whole skyline quotient isomorphism. -/

namespace OrdinalFormal.ARD2Skyline
set_option autoImplicit false

theorem expand_bounded {g : Graph} (hg : Valid g) (hn : g ≠ [])
    (f : Nat → Ordinal.{0}) (hf : Holds (· < ·) ARD2Demand.domain ARD2Demand.relation g f)
    (n : Nat) : ∃ next,
      Holds (· < ·) ARD2Demand.domain ARD2Demand.relation (expand g n) next ∧
      ReflectionTransport.Bounded (· < ·) (expand g n).length next (f (g.length-1)) := by
  obtain ⟨next, hNext, hBound⟩ := ARD2.expand_bounded (· < ·)
    ARD2Demand.domain ARD2Demand.relation (fun h₁ h₂ => lt_trans h₁ h₂)
    (fun h₁ h₂ => ARD2Demand.root_weaken h₁.le h₂)
    ARD2.demand_lower_rows ARD2Demand.finite_reflection hg hn f hf n
  refine ⟨next, holds_restrict (· < ·) _ _ (expand_aligned g n) hNext, ?_⟩
  rwa [(expand_aligned g n).length_eq]

theorem valid_accessible (g : Graph) (hg : Valid g) : Acc Step g := by
  apply valid_accessible_of_bounded ((· < ·) : Ordinal.{0} → Ordinal.{0} → Prop)
    ARD2Demand.domain ARD2Demand.relation Ordinal.lt_wf
    (fun _ n hv => expand_valid hv n) @expand_bounded (fun G hv => ?_) g hg
  obtain ⟨f, hf, _⟩ := ARD2Demand.initial.{0} G hv
  exact ⟨f, hf⟩

theorem valid_step_wellFounded :
    WellFounded (fun a b : {g : Graph // Valid g} => Step a.val b.val) :=
  valid_step_wellFounded_of_accessible valid_accessible

theorem standard_wellFounded : WellFounded StandardLt :=
  standard_wellFounded_of_seed_accessible (fun n => valid_accessible (seed n) (seed_valid n))

theorem standard_total (a b : StandardDiagram) :
    a = b ∨ StandardLt a b ∨ StandardLt b a :=
  standard_total_of_seed_accessible (fun n => valid_accessible (seed n) (seed_valid n)) a b

theorem standard_strictWellOrder : IsWellOrder StandardDiagram StandardLt where
  wf := standard_wellFounded
  trichotomous := by
    intro a b hab hba
    rcases standard_total a b with h | h | h
    · exact h
    · exact False.elim (hab h)
    · exact False.elim (hba h)

theorem standard_with_top_strictWellOrder : IsWellOrder StandardTerm TermLt where
  wf := term_wellFounded_of_finite standard_wellFounded
  trichotomous := by
    intro a b hab hba
    rcases term_total_of_finite standard_total a b with h | h | h
    · exact h
    · exact False.elim (hab h)
    · exact False.elim (hba h)

-- Small kernel-reduced checks of the new singleton seeds and moved predecessor.
example : seed 3 = [[], [⟨1,0,1⟩], [⟨2,1,2⟩]] := rfl
example : expand (seed 3) 1 = [[], [⟨1,0,1⟩], [⟨2,1,1⟩, ⟨2,0,2⟩]] := by decide
example : expand (seed 2) 3 = [[], [⟨1,0,0⟩], [⟨2,1,1⟩], [⟨3,2,2⟩]] := by decide

#print axioms expand_bounded
#print axioms valid_accessible
#print axioms valid_step_wellFounded
#print axioms standard_wellFounded
#print axioms standard_total
#print axioms standard_strictWellOrder
#print axioms standard_with_top_strictWellOrder
end OrdinalFormal.ARD2Skyline
