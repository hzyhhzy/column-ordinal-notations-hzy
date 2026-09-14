import OrdinalFormal.RPDSortedColumns
import OrdinalFormal.ColumnReachability

/-!
The concrete RPD standard-domain conclusion, with ONLY the still-unproved
seed-accessibility obligation exposed. This file is a reduction, NOT a
completed RPD well-ordering proof. Comparator laws, nested seeds, and actual
one-step decrease are supplied by proved definitions, not caller hypotheses.
-/

namespace OrdinalFormal.RPDWellOrderingReduction
open Columns
set_option autoImplicit false
set_option maxHeartbeats 500000

abbrev StandardDiagram := {g : RPD.Diagram // RPD.Standard (.finite g)}
def StandardLt (a b : StandardDiagram) : Prop := RPD.cmp a.val b.val = .lt

theorem standard_total_of_seed_accessible
    (seedAcc : ∀ n, Acc RPD.Step (RPD.seed n)) (a b : StandardDiagram) :
    a = b ∨ StandardLt a b ∨ StandardLt b a := by
  have ht := ColumnReachability.standard_total compare (fun _ _ => []) RPD.seed
    seedAcc RPDGeometry.seed_reachable
    (fun _ _ _ hab hbc => Comparison.rpd_cmp_lt_trans hab hbc)
    (fun ha hstep => RPDSortedColumns.standard_step_lt ((RPD.standard_finite_iff _).mpr ha) hstep)
    ((RPD.standard_finite_iff _).mp a.property) ((RPD.standard_finite_iff _).mp b.property)
  rcases ht with heq | hl | hr
  · exact Or.inl (Subtype.ext heq)
  · exact Or.inr (Or.inl hl)
  · exact Or.inr (Or.inr hr)

theorem standard_wellFounded_of_seed_accessible
    (seedAcc : ∀ n, Acc RPD.Step (RPD.seed n)) : WellFounded StandardLt := by
  let P : RPD.Diagram → Prop := fun g => RPD.Standard (.finite g)
  have closed : ∀ {a b}, P a → ColumnReachability.Step compare (fun _ _ => []) b a → P b := by
    intro a b ha hstep
    obtain ⟨_, n, rfl⟩ := hstep
    exact RPD.Standard.child ha n
  exact ColumnReachability.covered_domain_wellFounded compare (fun _ _ => [])
    @closed RPD.seed (fun n => RPD.Standard.child RPD.Standard.top n)
    (fun g hg => (RPD.standard_finite_iff g).mp hg) seedAcc RPDGeometry.seed_reachable
    (fun _ _ _ hab hbc => Comparison.rpd_cmp_lt_trans hab hbc)
    (fun a _ => Comparison.rpd_cmp_lt_irrefl a)
    (fun ha hstep => RPDSortedColumns.standard_step_lt ha hstep)

theorem with_top_wellFounded_of_seed_accessible
    (seedAcc : ∀ n, Acc RPD.Step (RPD.seed n)) :
    WellFounded (AdjoinTopLt StandardLt) :=
  wellFounded_adjoinTop (standard_wellFounded_of_seed_accessible seedAcc)

end OrdinalFormal.RPDWellOrderingReduction
