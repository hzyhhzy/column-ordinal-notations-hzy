import OrdinalFormal.Omega3RowDomain
import OrdinalFormal.StandardValidity

namespace OrdinalFormal.Omega3Validity
open Columns OmegaLRD3 StandardValidity ExpansionValidity
set_option autoImplicit false

theorem fs_valid {a : Diagram} (ha : Valid a.toGraph) (n : Nat) :
    Valid (fs a n).toGraph := by
  rw [fs_toGraph]
  exact expand_valid _ _ _ _ ha

theorem seed_valid (d : Nat) : Valid (seed d).toGraph := by
  induction d with
  | zero => exact valid_nil
  | succ d ih =>
    simp only [seed, Diagram.toGraph, Edges.toList_ofList]
    apply valid_append_column ih
    by_cases hd : d = 0
    · simp [hd]
    · simp only [hd, ↓reduceIte]
      apply normalizeColumn_bounds
      intro e he
      obtain rfl := List.mem_singleton.mp he
      simp only [seed_width]
      exact ⟨Nat.le_refl _, by omega⟩

theorem standard_valid {a : Diagram} (h : Standard (.finite a)) : Valid a.toGraph := by
  obtain ⟨n, hn⟩ := (standard_finite_iff a).mp h
  exact reach_preserves .nil fs (fun a => Valid a.toGraph)
    (fun _ ha n => fs_valid ha n) hn (seed_valid n)

#print axioms fs_valid
#print axioms seed_valid
#print axioms standard_valid
end OrdinalFormal.Omega3Validity
