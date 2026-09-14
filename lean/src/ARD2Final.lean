import ARD2InitialRepresentation
import ARD2StageProof
import ARD2SemanticWellFounded
import ARD2OrderReduction
import ARD2DefinitionFidelity

/-! Unconditional ARD2 well-ordering for the actual reachable standard domain.
This is an ordinary Lean proof, not a formal encoding of derivability in KP.
The actual finite-demand relation, closure supply, dynamic splice, and finite
rules are all instantiated; there is no remaining reflection, accessibility,
or well-ordering premise. -/

namespace OrdinalFormal.ARD2
set_option autoImplicit false

theorem demand_lower_rows :
    LowerRows ((· < ·) : Ordinal.{0} → Ordinal.{0} → Prop)
      ARD2Demand.relation := by
  intro low high theta eta a b hrow heta hR
  apply ARD2Demand.lower_rows hrow _ hR
  rcases heta with he | he
  · exact he.le
  · exact he.le

theorem valid_accessible (g : Graph) (hg : Valid g) : Acc Step g := by
  apply valid_accessible_of_bounded ((· < ·) : Ordinal.{0} → Ordinal.{0} → Prop)
    ARD2Demand.domain ARD2Demand.relation Ordinal.lt_wf
    (fun _ n hv => expand_valid hv n)
    (fun hv hn f hf n => expand_bounded (· < ·) ARD2Demand.domain ARD2Demand.relation
      (fun h₁ h₂ => lt_trans h₁ h₂)
      (fun h₁ h₂ => ARD2Demand.root_weaken h₁.le h₂)
      demand_lower_rows ARD2Demand.finite_reflection hv hn f hf n)
    (fun G hv => ?_) g hg
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

abbrev PaperStandardTerm := {a : Term // Fidelity.PaperStandard a}
def PaperLt (a b : PaperStandardTerm) : Prop := termCompare a.val b.val = .lt

theorem paper_standard_with_top_strictWellOrder : IsWellOrder PaperStandardTerm PaperLt := by
  have hp : Fidelity.PaperStandard = Standard :=
    funext (fun a => propext (Fidelity.paper_standard_iff a))
  change IsWellOrder {a : Term // Fidelity.PaperStandard a}
    (fun a b => termCompare a.val b.val = .lt)
  rw [hp]
  exact standard_with_top_strictWellOrder

#print axioms valid_accessible
#print axioms valid_step_wellFounded
#print axioms standard_wellFounded
#print axioms standard_total
#print axioms standard_strictWellOrder
#print axioms standard_with_top_strictWellOrder
#print axioms paper_standard_with_top_strictWellOrder

end OrdinalFormal.ARD2
