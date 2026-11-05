import LaverLowerBounds.ClosedFan
import LaverLowerBounds.DiagonalFGH

set_option autoImplicit false

namespace LaverLowerBounds

theorem PrefixDescent.length_le_steps {α : Type} {f : List α → List α}
    (hf : PrefixDescent.PreservesStem f) {s : List α} {n : Nat}
    (hs : PrefixDescent.Stops f s n) : s.length ≤ n := by
  induction hs with
  | done => simp
  | @step s n hne _ ih =>
      have hstem := (hf s).length_le
      have hp : 0 < s.length := by cases s <;> simp_all
      rw [List.length_dropLast] at hstem
      omega

namespace ParentBMS

/-- Totalized fixed-[1] count. Outside the terminating domain use the finite
envelope `countDefault`. Every finite-table fan application supplies an actual
termination witness, so this fallback never contributes to its budget.
Numeric BM4 fidelity is supplied by NumericExpansionFidelity.lean. -/
noncomputable def tripleCount (h : Nat) : Nat := by
  classical
  exact if ht : ∃ n, PrefixDescent.Stops (fun s => expand s 1) (triple h) n
    then Classical.choose ht else countDefault h

theorem tripleCount_eq {h n : Nat}
    (hn : PrefixDescent.Stops (fun s => expand s 1) (triple h) n) : tripleCount h = n := by
  classical
  have hex : ∃ k, PrefixDescent.Stops (fun s => expand s 1) (triple h) k := ⟨n, hn⟩
  simp only [tripleCount, dif_pos hex]
  exact PrefixDescent.stops_unique (Classical.choose_spec hex) hn

theorem tripleCount_ge_three (h : Nat) : 3 ≤ tripleCount h := by
  classical
  by_cases ht : ∃ n, PrefixDescent.Stops (fun s => expand s 1) (triple h) n
  · obtain ⟨n, hn⟩ := ht
    rw [tripleCount_eq hn]
    have he := PrefixDescent.length_le_steps (expand_preserves_stem 1) hn
    simpa only [triple, List.length_cons, List.length_nil] using he
  · simp only [tripleCount, dif_neg ht]
    exact countDefault_ge_three h

theorem triple_countingEstimate : CountingEstimate tripleCount diagonalFast := by
  intro x h hx hb
  classical
  by_cases ht : ∃ n, PrefixDescent.Stops (fun s => expand s 1) (triple h) n
  · obtain ⟨n, hn⟩ := ht
    rw [tripleCount_eq hn]
    exact (triple_diagonal_bound (by omega) hb hn).2
  · simp only [tripleCount, dif_neg ht]
    exact countDefault_covers (by dsimp [buffer] at hb; omega)

#print axioms triple_countingEstimate

end ParentBMS

namespace FiniteTable.ClosedFan

theorem tripleCount_lt {family : BinaryFamily} {m h : Nat}
    (fan : ClosedFan family m h) (hh : 3 ≤ h) : ParentBMS.tripleCount h < fan.endpoint := by
  obtain ⟨n, hn, hb⟩ := fan.counting_bound hh
  rw [ParentBMS.tripleCount_eq hn]
  exact hb

#print axioms tripleCount_lt

end FiniteTable.ClosedFan
end LaverLowerBounds
