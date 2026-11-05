import LaverLowerBounds.BandRepresentation

set_option autoImplicit false

namespace LaverLowerBounds.FiniteTable.BandRepresentation

open ParentBMS

variable {family : BinaryFamily} {m h : Nat}

theorem step_tail {stem : Matrix} {last : Column}
    (b : BandRepresentation family m h (stem ++ [last])) (hh : 3 ≤ h) :
    ∃ next : BandRepresentation family m h (expandTail stem last 1),
      BandBudget.Step (b.state hh) (next.state hh) := by
  cases he : last.getLast? with
  | none =>
      have hz : last = [] := List.getLast?_eq_none_iff.mp he
      subst last
      obtain ⟨next, hcost⟩ := b.delete_last
      refine ⟨next, BandBudget.Step.delete ?_ ?_⟩
      · change (stem ++ [[]]).length = stem.length + 1
        simp
      · change next.endpoint + 4 ≤ b.endpoint
        omega
  | some root =>
      obtain ⟨hlh, hlp⟩ := shape_last b.shape
      have hr : root < stem.length := by simpa using hlp root (List.mem_of_getLast? he)
      obtain ⟨next, hend⟩ := b.positive_copy he
      have hlen : (expandTail stem last 1).length = stem.length + (stem.length - root) := by
        rw [expandTail_one_positive he]
        simp only [List.length_append, copy_length]
      have hind : stem.length * (h + 1) + last.length + 1 ≤ (stem ++ [last]).length * (h + 1) := by
        simp only [List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul]
        omega
      have hbudget : next.endpoint ≤ b.endpoint := by
        rw [hend]
        exact b.points.mono hind (Nat.le_refl _)
      refine ⟨next, ?_⟩
      by_cases hw : stem.length - root = 1
      · apply BandBudget.Step.narrow
        · change (expandTail stem last 1).length = (stem ++ [last]).length
          simp [hlen, hw]
        · exact narrow_clears_ready b.shape he hw
        · exact hbudget
        · intro hnot
          have hlstrict : last.length < h := by
            by_cases heq : last.length = h
            · change ready h (stem ++ [last]) = false at hnot
              have he_root : root = stem.length - 1 := by omega
              rw [ready_append, heq, he, he_root] at hnot
              simp at hnot
            · omega
          change next.endpoint < b.endpoint
          rw [hend]
          apply b.points.strict
          · simp only [List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul]
            omega
          · exact Nat.le_refl _
      · apply BandBudget.Step.wide
        · change (stem ++ [last]).length < (expandTail stem last 1).length
          rw [hlen]
          simp only [List.length_append, List.length_singleton]
          omega
        · exact hbudget

theorem one_step {s : Matrix} (b : BandRepresentation family m h s) (hh : 3 ≤ h) (hne : s ≠ []) :
    ∃ next : BandRepresentation family m h (expand s 1),
      BandBudget.Step (b.state hh) (next.state hh) := by
  cases he : s.reverse with
  | nil =>
      have hz : s = [] := by simpa using congrArg List.reverse he
      exact False.elim (hne hz)
  | cons last rest =>
      have hz : s = rest.reverse ++ [last] := by simpa using congrArg List.reverse he
      subst s
      rw [expand_append]
      exact b.step_tail hh

/-- Every represented parent matrix terminates under the actual [1] algorithm.
This proof does not assume global BMS well-foundedness or a simulation oracle. -/
theorem terminates {s : Matrix} (b : BandRepresentation family m h s) (hh : 3 ≤ h) :
    ∃ n, PrefixDescent.Stops (fun a => expand a 1) s n ∧ n ≤ BandBudget.rank (b.state hh) := by
  have main : ∀ budget, ∀ s (b : BandRepresentation family m h s),
      BandBudget.rank (b.state hh) ≤ budget →
      ∃ n, PrefixDescent.Stops (fun a => expand a 1) s n ∧ n ≤ BandBudget.rank (b.state hh) := by
    intro budget
    induction budget using Nat.strongRecOn with
    | ind budget ih =>
        intro s b hb
        by_cases hz : s = []
        · subst s
          exact ⟨0, .done, Nat.zero_le _⟩
        · obtain ⟨next, hstep⟩ := b.one_step hh hz
          have hdec := BandBudget.rank_decreases hstep
          obtain ⟨n, hn, hnb⟩ := ih (BandBudget.rank (next.state hh)) (by omega)
            (expand s 1) next (Nat.le_refl _)
          exact ⟨n + 1, .step hz hn, by omega⟩
  exact main (BandBudget.rank (b.state hh)) s b (Nat.le_refl _)

theorem triple_stops_below_endpoint (b : BandRepresentation family m h (triple h)) (hh : 3 ≤ h) :
    ∃ n, PrefixDescent.Stops (fun a => expand a 1) (triple h) n ∧ n < b.endpoint := by
  obtain ⟨n, hn, hnb⟩ := b.terminates hh
  refine ⟨n, hn, Nat.lt_of_le_of_lt hnb ?_⟩
  exact BandBudget.triple_rank_lt_endpoint (by simp [state, triple])

theorem triple_count_below_endpoint (b : BandRepresentation family m h (triple h)) (hh : 3 ≤ h)
    {n : Nat} (hn : PrefixDescent.Stops (fun a => expand a 1) (triple h) n) : n < b.endpoint := by
  obtain ⟨k, hk, hkb⟩ := b.triple_stops_below_endpoint hh
  have he := PrefixDescent.stops_unique hn hk
  omega

#print axioms one_step
#print axioms terminates
#print axioms triple_count_below_endpoint

end LaverLowerBounds.FiniteTable.BandRepresentation
