import OrdinalFormal.LRDColumnDecrease
import OrdinalFormal.ColumnReachability

/-!
# Actual LRD standard-order reduction to its single seed

The definition has exactly one seed `LRD.seed`, and the seed itself belongs to
the standard domain. There is no extra external top. The only outstanding
premise here is accessibility of this actual seed under actual finite-index
expansion. All comparison, validity, closure and common-ancestor obligations
are supplied by proved executable/combinatorial lemmas.

This reduction is not an unconditional LRD well-ordering theorem.
-/

namespace OrdinalFormal.LRDWellOrderingReduction

open Columns
set_option autoImplicit false
set_option maxHeartbeats 600000

abbrev StandardDiagram := {g : LRD.Diagram // LRD.Standard g}

def StandardLt (a b : StandardDiagram) : Prop := LRD.cmp a.val b.val = .lt

theorem standard_closed {a b : LRD.Diagram} (ha : LRD.Standard a) (h : LRD.Step b a) :
    LRD.Standard b := by
  obtain ⟨_, n, rfl⟩ := h
  exact LRD.Standard.child ha n

theorem standard_total_of_seed_accessible
    (seedAcc : Acc LRD.Step LRD.seed) (a b : StandardDiagram) :
    a = b ∨ StandardLt a b ∨ StandardLt b a := by
  have h := ColumnReachability.covered_domain_total LRD.Row.cmp LRD.package
    (@standard_closed) (fun _ => LRD.seed) (fun _ => LRD.Standard.seed)
    (fun g hg => ⟨0, (LRD.standard_iff g).mp hg⟩) (fun _ => seedAcc)
    (fun _ => Reach.refl _)
    (fun _ _ _ hab hbc => LRDColumnDecrease.cmp_lt_trans hab hbc)
    (fun ha hstep => LRDColumnDecrease.standard_step_lt ha hstep)
    a.property b.property
  rcases h with heq | hl | hr
  · exact Or.inl (Subtype.ext heq)
  · exact Or.inr (Or.inl hl)
  · exact Or.inr (Or.inr hr)

theorem standard_wellFounded_of_seed_accessible
    (seedAcc : Acc LRD.Step LRD.seed) : WellFounded StandardLt :=
  ColumnReachability.covered_domain_wellFounded LRD.Row.cmp LRD.package
    (@standard_closed) (fun _ => LRD.seed) (fun _ => LRD.Standard.seed)
    (fun g hg => ⟨0, (LRD.standard_iff g).mp hg⟩) (fun _ => seedAcc)
    (fun _ => Reach.refl _)
    (fun _ _ _ hab hbc => LRDColumnDecrease.cmp_lt_trans hab hbc)
    (fun a _ => LRDColumnDecrease.cmp_lt_irrefl a)
    (fun ha hstep => LRDColumnDecrease.standard_step_lt ha hstep)

theorem standard_step_wellFounded_of_seed_accessible
    (seedAcc : Acc LRD.Step LRD.seed) :
    WellFounded (fun a b : StandardDiagram => LRD.Step a.val b.val) := by
  constructor
  intro a
  exact InvImage.accessible (fun a : StandardDiagram => a.val)
    (Reach.accessible seedAcc ((LRD.standard_iff a.val).mp a.property))

#check standard_wellFounded_of_seed_accessible
#print axioms standard_total_of_seed_accessible
#print axioms standard_wellFounded_of_seed_accessible

end OrdinalFormal.LRDWellOrderingReduction
