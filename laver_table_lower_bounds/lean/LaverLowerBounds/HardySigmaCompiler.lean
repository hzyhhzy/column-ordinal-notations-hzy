import LaverLowerBounds.SigmaLimitBudget

set_option autoImplicit false

namespace LaverLowerBounds.ParentBMS

theorem sigma_successor_parameter (s : Matrix) (x : Nat) :
    sigma ((s ++ [[]]) ++ List.replicate x []) = sigma (s ++ List.replicate (x + 1) []) := by
  simp only [List.replicate_succ, List.append_assoc, List.singleton_append]

/-- Every finite Hardy evaluation is bounded by the actual fixed-[1] count
of its diagonal-row encoding. The only surplus used is exponential. -/
theorem HardyEval.sigma_bound {s : Matrix} {x y : Nat} (he : HardyEval s x y) :
    ∀ n, Leftward s → Nested s → 0 < x →
      PrefixDescent.Stops (fun a => expand a 1) (sigma (s ++ List.replicate x [])) n →
      2 ^ (y + 1) ≤ n + 1 := by
  induction he with
  | done x =>
      intro n _ _ _ ht
      exact sigma_zeros_exponential (by simpa only [List.nil_append] using ht)
  | @step s x y hs _ ih =>
      intro n hl hn hx ht
      obtain ⟨stem, last, rfl⟩ := exists_last hs
      by_cases hz : last = []
      · subst last
        simp only [hardyNext_append, ↓reduceIte, Prod.fst, Prod.snd] at ih
        rw [sigma_successor_parameter] at ht
        exact ih n (leftward_prefix ⟨[[]], rfl⟩ hl) (nested_prefix ⟨[[]], rfl⟩ hl hn) (by omega) ht
      · simp only [hardyNext_append, if_neg hz, Prod.fst, Prod.snd] at ih
        obtain ⟨k, hk, _, hkn⟩ := sigma_limit_budget ⟨stem, last, rfl, hz⟩ hl hn hx ht
        have hg := expand_graph_all hl hn x
        have hh := ih k hg.1 hg.2 hx hk
        omega

/-- A finite encoded budget itself proves Hardy termination. No global
well-ordering theorem is needed to manufacture this particular evaluation. -/
theorem hardy_exists_of_sigma_stops {s : Matrix} {x n : Nat}
    (ht : PrefixDescent.Stops (fun a => expand a 1) (sigma (s ++ List.replicate x [])) n)
    (hl : Leftward s) (hn : Nested s) (hx : 0 < x) : ∃ y, HardyEval s x y := by
  induction n using Nat.strongRecOn generalizing s x with
  | ind n ih =>
      -- Successor steps keep the same encoding but shorten the source matrix.
      induction hlen : s.length generalizing s x with
      | zero =>
          have he : s = [] := List.eq_nil_of_length_eq_zero hlen
          subst s
          exact ⟨x, .done x⟩
      | succ len lengthIH =>
          have hs : s ≠ [] := by intro he; simp [he] at hlen
          obtain ⟨stem, last, rfl⟩ := exists_last hs
          by_cases hz : last = []
          · subst last
            rw [sigma_successor_parameter] at ht
            have hstem : stem.length = len := by simp only [List.length_append, List.length_singleton] at hlen; omega
            obtain ⟨y, hy⟩ := lengthIH ht (leftward_prefix ⟨[[]], rfl⟩ hl)
              (nested_prefix ⟨[[]], rfl⟩ hl hn) (by omega) hstem
            exact ⟨y, .successor hy⟩
          · obtain ⟨k, hk, _, hkn⟩ := sigma_limit_budget ⟨stem, last, rfl, hz⟩ hl hn hx ht
            have hg := expand_graph_all hl hn x
            obtain ⟨y, hy⟩ := ih k hkn hk hg.1 hg.2 hx
            exact ⟨y, .limit ⟨stem, last, rfl, hz⟩ hy⟩

#print axioms HardyEval.sigma_bound
#print axioms hardy_exists_of_sigma_stops

end LaverLowerBounds.ParentBMS
