import Mathlib.Data.Nat.Pairing
import Mathlib.SetTheory.Cardinal.Aleph
import OrdinalFormal.Omega3RowPool

namespace OrdinalFormal.Omega3Countable
open OmegaLRD3
set_option autoImplicit false
set_option maxRecDepth 4096
mutual
  def diagramCode : Diagram → Nat
    | .nil => 0
    | .col previous incoming => Nat.pair (diagramCode previous) (edgesCode incoming) + 1
  def edgesCode : Edges → Nat
    | .nil => 0
    | .cons row parent root tail =>
      Nat.pair (diagramCode row) (Nat.pair parent (Nat.pair root (edgesCode tail))) + 1
end

mutual
  theorem diagramCode_inj (a b : Diagram) (h : diagramCode a = diagramCode b) : a = b := by
    cases a with
    | nil => cases b <;> simp_all [diagramCode]
    | col previous incoming =>
      cases b with
      | nil => simp [diagramCode] at h
      | col previous' incoming' =>
        have hh := Nat.pair_eq_pair.mp (Nat.add_right_cancel h)
        exact congrArg₂ Diagram.col (diagramCode_inj previous previous' hh.1)
          (edgesCode_inj incoming incoming' hh.2)
  termination_by sizeOf a
  theorem edgesCode_inj (a b : Edges) (h : edgesCode a = edgesCode b) : a = b := by
    cases a with
    | nil => cases b <;> simp_all [edgesCode]
    | cons row parent root tail =>
      cases b with
      | nil => simp [edgesCode] at h
      | cons row' parent' root' tail' =>
        have hh := Nat.pair_eq_pair.mp (Nat.add_right_cancel h)
        have hrest := Nat.pair_eq_pair.mp hh.2
        have hlast := Nat.pair_eq_pair.mp hrest.2
        have hr := diagramCode_inj row row' hh.1
        have ht := edgesCode_inj tail tail' hlast.2
        rw [hr, hrest.1, hlast.1, ht]
  termination_by sizeOf a
end

theorem diagramCode_injective : Function.Injective diagramCode := diagramCode_inj
theorem edgesCode_injective : Function.Injective edgesCode := edgesCode_inj

instance diagramCountable : Countable Diagram := diagramCode_injective.countable
instance edgesCountable : Countable Edges := edgesCode_injective.countable


#print axioms diagramCode_injective
#print axioms edgesCode_injective
end OrdinalFormal.Omega3Countable
