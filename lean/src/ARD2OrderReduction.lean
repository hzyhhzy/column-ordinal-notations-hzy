import ARD2Domain
import ARD2Decrease

/-! The actual standard-domain order, reduced only to seed accessibility.
All finite-rule, closure, prefix, and comparison obligations are discharged. -/

namespace OrdinalFormal.ARD2
set_option autoImplicit false

theorem standard_valid {g : Graph} (hg : Standard (.finite g)) : Valid g :=
  standard_invariant Valid seed_valid
    (fun hv h => by obtain ⟨_, n, rfl⟩ := h; exact expand_valid hv n) hg

theorem standard_canonical {g : Graph} (hg : Standard (.finite g)) : Canonical g :=
  standard_invariant Canonical seed_canonical
    (fun hv h => by obtain ⟨_, n, rfl⟩ := h; exact expand_canonical hv n) hg

theorem standard_step_lt {g h : Graph} (hg : Standard (.finite g))
    (hstep : Step h g) : CompareLt h g := by
  obtain ⟨hn, n, rfl⟩ := hstep
  exact expand_lt (standard_valid hg) (standard_canonical hg) hn n

theorem prefix_reachable {a b : Graph} (hab : a.IsPrefix b) : Reach Step b a := by
  apply reach_of_list_prefix (hprefix := hab)
  intro g hg
  exact ⟨hg, 0, by rw [expand_zero, List.dropLast_eq_take]⟩

theorem childJoin : ChildJoin Step := by
  apply childJoin_of_list_fs expand
  · intro g
    rw [expand_zero, List.dropLast_eq_take]
  · exact fun g _ _ h => expand_prefix g h

theorem seed_reachable (n : Nat) : Reach Step (seed (n+1)) (seed n) := by
  apply Reach.single
  refine ⟨?_, 0, seed_succ_zero n⟩
  intro he
  have hlen := congrArg List.length he
  simp only [seed_length, List.length_nil] at hlen
  omega

theorem standard_total_of_seed_accessible
    (hacc : ∀ n, Acc Step (seed n)) (a b : StandardDiagram) :
    a = b ∨ StandardLt a b ∨ StandardLt b a := by
  have h := PrefixOrder.covered_total (lt := CompareLt) @standard_closed seed standard_seed
    (fun g hg => (standard_finite_iff g).mp hg) childJoin hacc seed_reachable
    (fun _ _ _ hab hbc => compareLt_trans hab hbc) @standard_step_lt
    a.property b.property
  rcases h with h | h | h
  · exact .inl (Subtype.ext h)
  · exact .inr (.inl h)
  · exact .inr (.inr h)

theorem standard_wellFounded_of_seed_accessible
    (hacc : ∀ n, Acc Step (seed n)) : WellFounded StandardLt :=
  PrefixOrder.covered_wellFounded @standard_closed seed standard_seed
    (fun g hg => (standard_finite_iff g).mp hg) childJoin hacc seed_reachable
    (fun _ _ _ hab hbc => compareLt_trans hab hbc)
    (fun g _ => compareLt_irrefl g) @standard_step_lt

#print axioms standard_valid
#print axioms standard_canonical
#print axioms childJoin
#print axioms standard_step_lt
#print axioms standard_total_of_seed_accessible
#print axioms standard_wellFounded_of_seed_accessible

end OrdinalFormal.ARD2
