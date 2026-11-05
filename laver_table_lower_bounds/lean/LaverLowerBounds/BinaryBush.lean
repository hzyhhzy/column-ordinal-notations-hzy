import LaverLowerBounds.HierarchyEvaluation

set_option autoImplicit false

namespace LaverLowerBounds.ParentBMS

theorem attached_nonempty (front : Matrix) {tail : Matrix} (ht : tail ≠ []) : attached front tail ≠ [] := by
  intro he
  have hh := congrArg List.length he
  simp only [attached, List.length_append, translated_length, List.length_nil] at hh
  have hlen : 0 < tail.length := by cases tail <;> simp_all
  omega

theorem stops_attached {front tail : Matrix} {n k index : Nat}
    (hf : PrefixDescent.Stops (fun s => expand s index) front n)
    (ht : PrefixDescent.Stops (fun s => expand s index) tail k) :
    PrefixDescent.Stops (fun s => expand s index) (attached front tail) (n + k) := by
  induction ht with
  | done => simpa only [attached_empty, Nat.add_zero] using hf
  | @step tail k hne _ ih =>
      have hn : PrefixDescent.Stops (fun s => expand s index)
          (expand (attached front tail) index) (n + k) := by
        rw [attached_expand front tail hne index]
        exact ih
      simpa only [Nat.add_assoc] using PrefixDescent.Stops.step (attached_nonempty front hne) hn

/-- One root with x leaves, rather than an arbitrary finite forest. -/
def bush (x : Nat) : Matrix := liftW (List.replicate x [])

theorem bush_eq (x : Nat) : bush x = [] :: List.replicate x [0] := by
  simp [bush, liftW, raiseColumn]

@[simp] theorem bush_length (x : Nat) : (bush x).length = x + 1 := by simp [bush]

theorem bush_expand_succ (x : Nat) : expand (bush (x + 1)) 1 = attached (bush x) (bush x) := by
  rw [bush, List.replicate_succ', liftW_expand_successor, blockCopies_succ]
  have he : blockCopies (liftW (List.replicate x [])) 1 = bush x := by
    simp [blockCopies, List.range_succ, translated_zero, bush]
  rw [he]
  rfl

/-- Exact total fixed-[1] step count for the binary bush. -/
theorem bush_stops (x : Nat) :
    PrefixDescent.Stops (fun s => expand s 1) (bush x) (2 ^ (x + 1) - 1) := by
  induction x with
  | zero =>
      have hs : PrefixDescent.Stops (fun s => expand s 1) [[]] 1 :=
        .step (by simp) (by exact .done)
      simpa only [bush, List.replicate_zero, liftW, List.map_nil] using hs
  | succ x ih =>
      have hnext := stops_attached ih ih
      have hnext' : PrefixDescent.Stops (fun s => expand s 1) (expand (bush (x + 1)) 1)
          ((2 ^ (x + 1) - 1) + (2 ^ (x + 1) - 1)) := by rw [bush_expand_succ]; exact hnext
      have he : (2 ^ (x + 1) - 1) + (2 ^ (x + 1) - 1) + 1 = 2 ^ ((x + 1) + 1) - 1 := by
        rw [Nat.pow_succ]
        have := Nat.two_pow_pos (x + 1)
        omega
      rw [← he]
      exact .step (by rw [bush_eq]; simp) hnext'

theorem zeros_shape (h x : Nat) : Shape h 0 (List.replicate x ([] : Column)) := by
  intro i c hc
  have he : c = [] := List.eq_of_mem_replicate (List.mem_of_getElem? hc)
  subst c
  simp

theorem zeros_nested (x : Nat) : Nested (List.replicate x ([] : Column)) := by
  intro q i p hp
  obtain ⟨c, hc, hcp⟩ := parent_some_iff.mp hp
  have he : c = [] := List.eq_of_mem_replicate (List.mem_of_getElem? hc)
  simp [he] at hcp

theorem bush_shape (x : Nat) : Shape 1 0 (bush x) := liftW_shape (zeros_shape 1 x) (by decide)
theorem bush_nested (x : Nat) : Nested (bush x) := liftW_nested (zeros_nested x)

def bush_chain_cover (x : Nat) : Cover (bush x) (sigma (List.replicate x [])) where
  column := id
  bounded i hi := by simpa only [bush_length, sigma_length, List.length_replicate, id_eq] using hi
  strict _ _ hij _ := hij
  edge q p i hp := by
    obtain ⟨c, hc, hcp⟩ := parent_some_iff.mp hp
    obtain ⟨height, parents⟩ := bush_shape x i c hc
    have hq := (List.getElem?_eq_some_iff.mp hcp).1
    have hqi : q = 0 := by omega
    subst q
    have hpi := parents p (List.mem_of_getElem? hcp)
    change Ancestor (sigma (List.replicate x [])) 0 p i
    apply sigma_chain (by omega)
    have hi := (List.getElem?_eq_some_iff.mp hc).1
    simpa only [bush_length, sigma_length, List.length_replicate] using hi
  last _ := by simp

/-- Only exponential surplus is needed at the end of the Hardy compiler.
This avoids needing the exact tower-valued evaluation of arbitrary forests. -/
theorem sigma_zeros_exponential {x n : Nat}
    (ht : PrefixDescent.Stops (fun s => expand s 1) (sigma (List.replicate x [])) n) :
    2 ^ (x + 1) ≤ n + 1 := by
  have hleft := leftward_of_shape (zeros_shape 0 x)
  obtain ⟨k, hk, hkn⟩ := (bush_chain_cover x).stops ht
    (leftward_of_shape (bush_shape x)) (bush_nested x)
    (sigma_leftward hleft) (sigma_nested hleft (zeros_nested x))
  have he := PrefixDescent.stops_unique hk (bush_stops x)
  have hp := Nat.two_pow_pos (x + 1)
  omega

#print axioms bush_stops
#print axioms sigma_zeros_exponential

end LaverLowerBounds.ParentBMS
