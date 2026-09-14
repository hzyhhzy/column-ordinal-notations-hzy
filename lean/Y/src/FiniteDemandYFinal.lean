import FiniteDemandHostAmbient
import NatSemanticTransport
import OneY.Dynamics
import OrdinalFormal.Reachability

/-! The pinned actual Y expansion, with the SAME finite-demand semantic backend
as RPD, LRD and Omega-LRD3. This removes any dependence on the older truth-tower
existence theorem from this final Y proof. It remains a host-Lean proof, not an
object-language KP certificate or a proof about a JavaScript interpreter. -/

namespace OrdinalFormal.YFiniteDemand
open OneY.Numeric YesMetaZFC.BMS.StabilityFrame
set_option autoImplicit false

theorem expansion_wellFounded : WellFounded (ZeroY.ExpansionStep expand) := by
  apply OneY.RootIndexed.actual_expansion_wellFounded
    (α := FiniteDemand.Label.{0}) (· < ·) FiniteDemand.domain
    (FiniteDemand.relation Nat.lt Nat.lt_wfRel.wf) Ordinal.lt_wf
    (fun h₁ h₂ => lt_trans h₁ h₂) (fun h => FiniteDemand.strict h)
    (fun h₁ h₂ => FiniteDemand.root_weaken h₁.le h₂)
  · exact NatSemanticTransport.finiteReflection_toUp _ _ _
      (FiniteDemand.finite_reflection Nat.lt Nat.lt_wfRel.wf)
  · intro s
    obtain ⟨f, hf, _⟩ := FiniteDemand.initial_representation Nat.lt Nat.lt_wfRel.wf
      FiniteDemand.HostAmbient.actual
      (NatSemanticTransport.diagramToLocal (OneY.RootIndexed.exprDiagram s))
    exact ⟨f, (NatSemanticTransport.representation_toLocal_iff _ _ _ _ f).mp hf⟩

theorem generated_strictWellOrder : StrictWellOrder GeneratedExpr GeneratedLt :=
  OneY.Numeric.generated_strictWellOrder expansion_wellFounded

theorem descendants_strictWellOrder (s : ZeroY.Expr) :
    StrictWellOrder (Descendant s) DescendantLt :=
  OneY.Numeric.descendants_strictWellOrder expansion_wellFounded s

/-- Optional external maximum for the whole generated Y domain. This does
not alter the pinned finite expansion or substitute a different finite domain. -/
abbrev WithTop := Option GeneratedExpr
def WithTopLt : WithTop → WithTop → Prop := AdjoinTopLt GeneratedLt

theorem with_top_isWellOrder : IsWellOrder WithTop WithTopLt where
  wf := wellFounded_adjoinTop generated_strictWellOrder.wellFounded
  trichotomous := by
    intro a b hab hba
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some b => exact False.elim (hba trivial)
    | some a =>
      cases b with
      | none => exact False.elim (hab trivial)
      | some b =>
        rcases generated_strictWellOrder.trichotomy a b with h | h | h
        · exact congrArg some h
        · exact False.elim (hab h)
        · exact False.elim (hba h)

#print axioms expansion_wellFounded
#print axioms generated_strictWellOrder
#print axioms descendants_strictWellOrder
#print axioms with_top_isWellOrder
end OrdinalFormal.YFiniteDemand
