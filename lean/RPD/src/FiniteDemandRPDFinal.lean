import FiniteDemandColumnWellFounded
import OrdinalFormal.RPDTermOrder
import OrdinalFormal.RPDDefinitionFidelity

/-!
# Current column RPD via the finite-demand backend

This re-establishes the already known host-Lean result using the new backend,
without the old full truth-tower import. The actual top and the independently
specified finite-union standard domain are both retained. The separate paper
gives the weak-KP argument; a Lean object-theory certification is not claimed.
-/

namespace OrdinalFormal.RPDFiniteDemand

theorem valid_accessible_in_ambient (E : FiniteDemand.Ambient.{0})
    (g : RPD.Diagram) (hg : Columns.Valid g) : Acc RPD.Step g :=
  FiniteDemand.valid_accessible_in_ambient compare (fun _ _ => []) Nat.lt Nat.lt_wfRel.wf
    (fun h₁ h₂ => Nat.lt_trans h₁ h₂) (by intro _ _ _ h; cases h)
    ColumnRepresentation.natRowCompareSound E g hg

theorem valid_accessible (g : RPD.Diagram) (hg : Columns.Valid g) : Acc RPD.Step g :=
  valid_accessible_in_ambient FiniteDemand.HostAmbient.actual g hg

theorem standard_wellFounded : WellFounded RPDWellOrderingReduction.StandardLt :=
  RPDWellOrderingReduction.standard_wellFounded_of_seed_accessible
    (fun n => valid_accessible (RPD.seed n) (StandardValidity.rpd_seed_valid n))

theorem standard_total (a b : RPDWellOrderingReduction.StandardDiagram) :
    a = b ∨ RPDWellOrderingReduction.StandardLt a b ∨ RPDWellOrderingReduction.StandardLt b a :=
  RPDWellOrderingReduction.standard_total_of_seed_accessible
    (fun n => valid_accessible (RPD.seed n) (StandardValidity.rpd_seed_valid n)) a b

theorem standard_strictWellOrder :
    IsWellOrder RPDWellOrderingReduction.StandardDiagram RPDWellOrderingReduction.StandardLt where
  wf := standard_wellFounded
  trichotomous := by
    intro a b hab hba
    rcases standard_total a b with h | h | h
    · exact h
    · exact False.elim (hab h)
    · exact False.elim (hba h)

theorem standard_with_top_strictWellOrder :
    IsWellOrder RPDTermOrder.StandardTerm RPDTermOrder.Lt where
  wf := RPDTermOrder.wellFounded_of_finite standard_wellFounded
  trichotomous := by
    intro a b hab hba
    rcases RPDTermOrder.total_of_finite standard_total a b with h | h | h
    · exact h
    · exact False.elim (hab h)
    · exact False.elim (hba h)

abbrev PaperStandardTerm := {a : RPD.Term // RPDDefinitionFidelity.PaperStandard a}

def PaperLt (a b : PaperStandardTerm) : Prop := RPDTermOrder.cmp a.val b.val = .lt

theorem paper_standard_with_top_strictWellOrder :
    IsWellOrder PaperStandardTerm PaperLt := by
  have hp : RPDDefinitionFidelity.PaperStandard = RPD.Standard :=
    funext (fun a => propext (RPDDefinitionFidelity.paper_standard_iff a))
  change IsWellOrder {a : RPD.Term // RPDDefinitionFidelity.PaperStandard a}
    (fun a b => RPDTermOrder.cmp a.val b.val = .lt)
  rw [hp]
  exact standard_with_top_strictWellOrder

end OrdinalFormal.RPDFiniteDemand

#print axioms OrdinalFormal.RPDFiniteDemand.valid_accessible_in_ambient
#print axioms OrdinalFormal.RPDFiniteDemand.valid_accessible
#print axioms OrdinalFormal.RPDFiniteDemand.standard_strictWellOrder
#print axioms OrdinalFormal.RPDFiniteDemand.standard_with_top_strictWellOrder
#print axioms OrdinalFormal.RPDFiniteDemand.paper_standard_with_top_strictWellOrder
