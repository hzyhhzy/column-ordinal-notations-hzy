import Std

/-!
Finite trajectory comparison for prefix-preserving sequence expansions.
These theorems require no global well-foundedness and no input monotonicity.
They are used to turn mixed indices into subtrajectories of a fixed index.
-/

set_option autoImplicit false

namespace LaverLowerBounds.PrefixDescent

variable {α : Type}

def PreservesStem (f : List α → List α) : Prop :=
  ∀ s : List α, s.dropLast.IsPrefix (f s)

/-- Exactly n nonempty-source steps, ending for the first time at the empty list. -/
inductive Stops (f : List α → List α) : List α → Nat → Prop
  | done : Stops f [] 0
  | step {s n} : s ≠ [] → Stops f (f s) n → Stops f s (n + 1)

theorem stops_next {f : List α → List α} {s : List α} {n : Nat}
    (hn : Stops f s n) (hs : s ≠ []) : ∃ k, Stops f (f s) k ∧ n = k + 1 := by
  cases hn with
  | done => exact False.elim (hs rfl)
  | @step _ k _ hnext => exact ⟨k, hnext, rfl⟩

theorem proper_prefix_stem {p s : List α} (hp : p.IsPrefix s) (hne : p ≠ s) :
    p.IsPrefix s.dropLast := by
  obtain ⟨tail, htail⟩ := hp
  have ht : tail ≠ [] := by
    intro h
    subst tail
    simp only [List.append_nil] at htail
    exact hne htail
  rw [← htail, List.dropLast_append_of_ne_nil ht]
  exact ⟨tail.dropLast, rfl⟩

theorem stops_unique {f : List α → List α} {s : List α} {n k : Nat}
    (hn : Stops f s n) (hk : Stops f s k) : n = k := by
  induction hn generalizing k with
  | done =>
      cases hk with
      | done => rfl
      | step hne _ => exact False.elim (hne rfl)
  | step hne hnext ih =>
      cases hk with
      | done => exact False.elim (hne rfl)
      | step _ hnext' => exact congrArg Nat.succ (ih hnext')

/-- Every prefix of a terminating sequence also terminates within its budget. -/
theorem stops_prefix {f : List α → List α} (hf : PreservesStem f)
    {s : List α} {n : Nat} (hn : Stops f s n) {p : List α} (hp : p.IsPrefix s) :
    ∃ k, Stops f p k ∧ k ≤ n := by
  induction hn with
  | done =>
      have he : p = [] := hp.eq_of_length_le (by simp)
      subst p
      exact ⟨0, .done, Nat.le_refl _⟩
  | @step s n hne hnext ih =>
      by_cases he : p = s
      · subst p
        exact ⟨n + 1, .step hne hnext, Nat.le_refl _⟩
      · have hp' := (proper_prefix_stem hp he).trans (hf s)
        obtain ⟨k, hk, hkn⟩ := ih hp'
        exact ⟨k, hk, by omega⟩

/-- Truncating the result of a genuine step spends at least one fixed-index step. -/
theorem stops_after_truncation {f : List α → List α} (hf : PreservesStem f)
    {s t : List α} {n : Nat} (hn : Stops f s n) (hne : s ≠ [])
    (ht : t.IsPrefix (f s)) : ∃ k, Stops f t k ∧ k < n := by
  cases hn with
  | done => exact False.elim (hne rfl)
  | @step _ k _ hnext =>
      obtain ⟨j, hj, hjk⟩ := stops_prefix hf hnext ht
      exact ⟨j, hj, by omega⟩

/-- Each mixed step may truncate an arbitrary suffix after one application of f. -/
inductive MixedRun (f : List α → List α) : List α → List α → Nat → Prop
  | refl (s) : MixedRun f s s 0
  | step {s t u n} : s ≠ [] → t.IsPrefix (f s) →
      MixedRun f t u n → MixedRun f s u (n + 1)

/-- The number of genuine mixed steps plus the remaining budget never increases. -/
theorem mixed_run_budget {f : List α → List α} (hf : PreservesStem f)
    {s t : List α} {k n : Nat} (hrun : MixedRun f s t k) (hn : Stops f s n) :
    ∃ rest, Stops f t rest ∧ k + rest ≤ n := by
  induction hrun generalizing n with
  | refl s => exact ⟨n, hn, by omega⟩
  | @step s t u k hne hp htail ih =>
      obtain ⟨mid, hmid, hmn⟩ := stops_after_truncation hf hn hne hp
      obtain ⟨rest, hrest, hkr⟩ := ih hmid
      exact ⟨rest, hrest, by omega⟩

theorem mixed_run_length_le {f : List α → List α} (hf : PreservesStem f)
    {s t : List α} {k n : Nat} (hrun : MixedRun f s t k) (hn : Stops f s n) :
    k ≤ n := by
  obtain ⟨rest, _, h⟩ := mixed_run_budget hf hrun hn
  omega

#print axioms stops_prefix
#print axioms mixed_run_budget

end LaverLowerBounds.PrefixDescent
