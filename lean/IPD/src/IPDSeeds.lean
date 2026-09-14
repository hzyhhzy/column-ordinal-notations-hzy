import IPDProfileIdentity

/-! The actual zero-start seeds, their finite validity and one-step nesting. -/

namespace IPD
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem seed_valid (n : Nat) : Valid (seed n) := by
  intro j e he
  cases j with
  | zero => simp [seed] at he
  | succ j =>
    cases j with
    | zero =>
      have heq : e = ⟨0,⟨n,Layer.seed 0 1 0 n⟩⟩ := by simpa [seed] using he
      subst e
      exact ⟨by change 0 < 1; decide,Layer.seed_all (fun i => i ≤ 0 ∨ i = 1) 0 1 0
        (.inl le_rfl) (.inr rfl) n⟩
    | succ j => simp [seed] at he

theorem seed_canonical (n : Nat) : Canonical (seed n) := by
  intro c hc
  simp only [seed,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl <;> simp

theorem lower_seed_succ (n : Nat) :
    lowerProfile 0 1 0 ⟨n+1,Layer.seed 0 1 0 (n+1)⟩ = some ⟨n,Layer.seed 0 1 0 n⟩ := by
  simp [lowerProfile,Layer.seed,Layer.lower,Tree.lower]

theorem seed_succ_one (n : Nat) : expand (seed (n+1)) 1 = seed n := by
  simp [expand,seed,controller,block,seam,moveEdge_zero,shift_zero,normalize,insertEdge,lower_seed_succ]

theorem seed_nonempty (n : Nat) : seed n ≠ [] := by simp [seed]

end IPD

#print axioms IPD.seed_valid
#print axioms IPD.seed_succ_one
