import K11.FastPostprocess
import LaverLowerBounds.TripleCount

set_option autoImplicit false
namespace LaverLowerBounds.ParentBMS

/-- Row budget including the two finite output postprocessors. -/
def rowBudget (x : Nat) : Nat := x + 4 + Nat.log2 (x + 8)

theorem rowBudget_ge (x : Nat) : x + 4 ≤ rowBudget x := by
  unfold rowBudget
  omega

theorem rowBudget_le_four {x : Nat} (hx : 4 ≤ x) : rowBudget x ≤ 4 * x + 4 := by
  have hl := Nat.log2_le_self (x + 8)
  unfold rowBudget
  omega

/-- A real terminating triple supports an actual BMS FGH evaluation, with
enough numerical slack to rebuild the row budget after one logarithm. -/
theorem triple_realizes_buffered_fgh {h x n : Nat} (hx : 0 < x)
    (hb : rowBudget x ≤ h)
    (ht : PrefixDescent.Stops (fun a => expand a 1) (triple h) n) :
    ∃ y, LambdaEval x y ∧ 2 ^ (4 * y + 4) ≤ n := by
  let u := h - x - 3
  have hu : Nat.log2 (x + 8) < u := by dsimp [u]; dsimp [rowBudget] at hb; omega
  have hh : (x + 2) + u + 1 = h := by dsimp [u]; dsimp [rowBudget] at hb; omega
  have hpow : x + 8 < 2 ^ u := (Nat.log2_lt (by omega : x + 8 ≠ 0)).mp hu
  have hs := postCode_shape (by omega : 1 ≤ x + 1)
  have hl := leftward_of_shape hs
  have hn := postCode_nested (x + 1)
  have hg := append_zeros_graph hl hn x
  have hwidth : (sigma (postCode (x + 1) ++ List.replicate x [])).length ≤ 2 + 2 ^ u := by
    simp only [sigma_length, List.length_append, List.length_replicate,
      postCode, List.length_cons, List.length_nil]
    omega
  have hstops : PrefixDescent.Stops (fun a => expand a 1) (triple ((x + 2) + u + 1)) n := by
    rw [hh]; exact ht
  obtain ⟨k, hk, hkn⟩ := triple_compiler_envelope hstops
    (sigma_shape (shape_append_zeros hs x)) (sigma_nested hg.1 hg.2) hwidth
  obtain ⟨z, hz⟩ := hardy_exists_of_sigma_stops hk hl hn hx
  have hbound := hz.sigma_bound k hl hn hx hk
  have run := hz.to_fast_stack [seed (x + 1), [[]], [[]]] (postCode_eq (by omega))
  obtain ⟨y, hy, he⟩ := postprocess_extract run
  refine ⟨y, hy, ?_⟩
  rw [he] at hbound
  have hexp : 4 * y + 3 + 1 = 4 * y + 4 := by omega
  rw [hexp] at hbound
  omega

theorem buffered_fgh_of_fan {family : FiniteTable.BinaryFamily} {m h x : Nat}
    (fan : FiniteTable.ClosedFan family m h) (hx : 4 ≤ x)
    (hb : rowBudget x ≤ h) :
    ∃ y, LambdaEval x y ∧ rowBudget y ≤ Nat.log2 (tripleCount h) := by
  have hh : 3 ≤ h := by have := rowBudget_ge x; omega
  obtain ⟨n, hn, _⟩ := fan.counting_bound hh
  obtain ⟨y, hy, hpow⟩ := triple_realizes_buffered_fgh (by omega) hb hn
  have hg := FastEval.growth hy
  have hpos : n ≠ 0 := by have := Nat.two_pow_pos (4 * y + 4); omega
  have hlog : 4 * y + 4 ≤ Nat.log2 n := (Nat.le_log2 hpos).mpr hpow
  refine ⟨y, hy, ?_⟩
  rw [tripleCount_eq hn]
  exact Nat.le_trans (rowBudget_le_four (by omega)) hlog

#print axioms triple_realizes_buffered_fgh
#print axioms buffered_fgh_of_fan
end LaverLowerBounds.ParentBMS
