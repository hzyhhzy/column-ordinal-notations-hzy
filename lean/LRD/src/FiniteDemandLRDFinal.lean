import FiniteDemandColumnWellFounded
import LRDOrdinalRows
import OrdinalFormal.LRDWellOrderingReduction

/-!
# Unconditional well-ordering of the actual LRD standard domain (host Lean)

Uses the unchanged actual row comparator, generated packages, basic sequences,
single seed, and standard domain. No initial representation, reflection, seed
accessibility, or ambient enumeration hypothesis remains in the final exits.

This completes the semantic gap of the former LRD reduction at the host-Lean
level. It does NOT certify an object-language KP derivation. Bounded relation
tables and the transfer from L are justified in the separate paper.
-/

namespace OrdinalFormal.LRDFinal
open Columns LRDStructure LRDNormalLift LRDWellOrderingReduction

theorem normal_valid_accessible (g : Graph NormalRow) (hg : Valid g) :
    Acc (GeneratedSemanticWellFounded.Step normalRowCmp normalPackage) g :=
  FiniteDemand.valid_accessible normalRowCmp normalPackage normalLt
    LRDRowWellFounded.normalRowCmp_wellFounded (fun h₁ h₂ => normalLt_trans h₁ h₂)
    (fun _ _ _ h => normalPackage_lt h) normalRowCompareSound g hg

/-- Lifting is exact on every actual expansion; it preserves nonemptiness. -/
theorem step_lift {a b : LRD.Diagram} (h : LRD.Step a b) :
    GeneratedSemanticWellFounded.Step normalRowCmp normalPackage (liftGraph a) (liftGraph b) := by
  obtain ⟨hne, n, rfl⟩ := h
  refine ⟨?_, n, (fs_lift b n).symm⟩
  intro hz
  have hl := congrArg List.length hz
  simp only [liftGraph, ColumnMap.mapGraph, List.length_map, List.length_nil] at hl
  exact hne (List.length_eq_zero_iff.mp hl)

theorem valid_accessible (g : LRD.Diagram) (hg : Valid g) : Acc LRD.Step g := by
  apply Subrelation.accessible (r := InvImage
    (GeneratedSemanticWellFounded.Step normalRowCmp normalPackage) liftGraph)
  · intro a b hab
    exact step_lift hab
  · exact InvImage.accessible liftGraph
      (normal_valid_accessible (liftGraph g) ((valid_lift_iff g).mpr hg))

theorem seed_accessible : Acc LRD.Step LRD.seed :=
  valid_accessible LRD.seed StandardValidity.lrd_seed_valid

theorem standard_wellFounded : WellFounded StandardLt :=
  standard_wellFounded_of_seed_accessible seed_accessible

theorem standard_total (a b : StandardDiagram) :
    a = b ∨ StandardLt a b ∨ StandardLt b a :=
  standard_total_of_seed_accessible seed_accessible a b

theorem standard_isWellOrder : IsWellOrder StandardDiagram StandardLt where
  wf := standard_wellFounded
  trichotomous := by
    intro a b hab hba
    rcases standard_total a b with heq | hl | hr
    · exact heq
    · exact False.elim (hab hl)
    · exact False.elim (hba hr)

theorem standard_step_wellFounded :
    WellFounded (fun a b : StandardDiagram => LRD.Step a.val b.val) :=
  standard_step_wellFounded_of_seed_accessible seed_accessible

end OrdinalFormal.LRDFinal

#print axioms OrdinalFormal.LRDFinal.valid_accessible
#print axioms OrdinalFormal.LRDFinal.seed_accessible
#print axioms OrdinalFormal.LRDFinal.standard_wellFounded
#print axioms OrdinalFormal.LRDFinal.standard_isWellOrder
#print axioms OrdinalFormal.LRDFinal.standard_step_wellFounded
