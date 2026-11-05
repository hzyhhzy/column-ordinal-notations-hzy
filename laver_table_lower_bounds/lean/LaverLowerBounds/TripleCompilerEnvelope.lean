import LaverLowerBounds.RowWidthTrade

set_option autoImplicit false

namespace LaverLowerBounds.ParentBMS

theorem triple_parent_iff {h q p i : Nat} :
    parent (triple h) q i = some p ↔ (i = 1 ∨ i = 2) ∧ q < h ∧ p = 0 := by
  cases i with
  | zero => simp [parent, triple]
  | succ i =>
      cases i with
      | zero =>
          simp only [parent, triple, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.bind_some,
            List.getElem?_replicate]
          by_cases hq : q < h <;> simp [hq, eq_comm]
      | succ i =>
          cases i with
          | zero =>
              simp only [parent, triple, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.bind_some,
                List.getElem?_replicate]
              by_cases hq : q < h <;> simp [hq, eq_comm]
          | succ i => simp [parent, triple]

theorem triple_leftward (h : Nat) : Leftward (triple h) := by
  intro q i p hp
  obtain ⟨hi, _, rfl⟩ := triple_parent_iff.mp hp
  rcases hi with hi | hi <;> omega

theorem triple_nested (h : Nat) : Nested (triple h) := by
  intro q i p hp
  obtain ⟨hi, hq, rfl⟩ := triple_parent_iff.mp hp
  exact .direct (triple_parent_iff.mpr ⟨hi, by omega, rfl⟩)

theorem expand_triple_succ (h : Nat) :
    expand (triple (h + 1)) 1 =
      [[], List.replicate (h + 1) 0, List.replicate h 0, List.replicate (h + 1) 2] := by
  change expandTail [[], List.replicate (h + 1) 0] (List.replicate (h + 1) 0) 1 = _
  simp [expandTail, List.getLast?_replicate, copy, shift, List.take_replicate, List.range_succ]

def triple_diagonal_cover (h : Nat) : Cover (diagonal h 3) (expand (triple (h + 1)) 1) where
  column i := if i = 0 then 0 else i + 1
  bounded i hi := by
    rw [expand_triple_succ]
    simp only [List.length_cons, List.length_nil, diagonal_length] at *
    split <;> omega
  strict i j hij hj := by
    simp only [diagonal_length] at hj
    split <;> split <;> omega
  edge q p i hp := by
    obtain ⟨hi, hpos, hq, rfl⟩ := diagonal_parent_iff.mp hp
    by_cases hone : i = 1
    · subst i
      apply Ancestor.direct
      simp [expand_triple_succ, parent, List.getElem?_replicate_of_lt hq]
    · have he : i = 2 := by omega
      subst i
      apply Ancestor.direct
      simp [expand_triple_succ, parent, List.getElem?_replicate_of_lt (by omega : q < h + 1)]
  last _ := by simp [diagonal_length, expand_triple_succ]

theorem triple_to_diagonal {h n : Nat}
    (ht : PrefixDescent.Stops (fun a => expand a 1) (triple (h + 1)) n) :
    ∃ k, PrefixDescent.Stops (fun a => expand a 1) (diagonal h 3) k ∧ k < n := by
  obtain ⟨j, hj, hnjeq⟩ := PrefixDescent.stops_next ht (by simp [triple])
  have hn := expand_graph (triple_leftward (h + 1)) (triple_nested (h + 1))
  obtain ⟨k, hk, hkj⟩ := (triple_diagonal_cover h).stops hj
    (diagonal_leftward _ _) (diagonal_nested _ _) hn.1 hn.2
  exact ⟨k, hk, by omega⟩

theorem iterated_row_width_trade (u : Nat) {h n : Nat}
    (ht : PrefixDescent.Stops (fun a => expand a 1) (diagonal (h + u) 3) n) :
    ∃ k, PrefixDescent.Stops (fun a => expand a 1) (diagonal h (2 + 2 ^ u)) k ∧ k ≤ n := by
  induction u generalizing h n with
  | zero => exact ⟨n, by simpa using ht, Nat.le_refl _⟩
  | succ u ih =>
      have hin : PrefixDescent.Stops (fun a => expand a 1) (diagonal ((h + 1) + u) 3) n := by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht
      obtain ⟨j, hj, hjn⟩ := ih hin
      have hin' : PrefixDescent.Stops (fun a => expand a 1) (diagonal (h + 1) ((1 + 2 ^ u) + 1)) j := by
        simpa only [show 1 + 2 ^ u + 1 = 2 + 2 ^ u by omega] using hj
      have hw : 0 < 1 + (2 : Nat) ^ u := by simpa only [Nat.succ_eq_add_one, Nat.add_comm] using Nat.succ_pos ((2 : Nat) ^ u)
      obtain ⟨k, hk, hkj⟩ := row_width_trade hw hin'
      refine ⟨k, ?_, by omega⟩
      have he : 2 * (1 + 2 ^ u) = 2 + 2 ^ (u + 1) := by rw [Nat.pow_succ]; omega
      rwa [he] at hk

/-- A terminating three-column table controls every nested leftward table
inside an exponentially wider, slightly shorter rectangle. -/
theorem triple_compiler_envelope {h u n : Nat} {s : Matrix}
    (ht : PrefixDescent.Stops (fun a => expand a 1) (triple (h + u + 1)) n)
    (hs : Shape h 0 s) (hsn : Nested s) (hw : s.length ≤ 2 + 2 ^ u) :
    ∃ k, PrefixDescent.Stops (fun a => expand a 1) s k ∧ k < n := by
  obtain ⟨j, hj, hjn⟩ := triple_to_diagonal ht
  obtain ⟨l, hl, hlj⟩ := iterated_row_width_trade u hj
  obtain ⟨k, hk, hkl⟩ := (diagonal_cover hs hw).stops hl
    (leftward_of_shape hs) hsn (diagonal_leftward _ _) (diagonal_nested _ _)
  exact ⟨k, hk, by omega⟩

#print axioms triple_compiler_envelope

end LaverLowerBounds.ParentBMS
