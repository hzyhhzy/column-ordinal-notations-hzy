import LaverLowerBounds.FastHardyEquivalence
import LaverLowerBounds.Numerical

set_option autoImplicit false

namespace LaverLowerBounds.ParentBMS

theorem seed_diagonal (r : Nat) : seed r = diagonal r 2 := by
  simp [seed, diagonal, List.range_succ]

theorem seed_shape (r : Nat) : Shape r 0 (seed r) := by rw [seed_diagonal]; exact diagonal_shape _ _
theorem seed_nested (r : Nat) : Nested (seed r) := by rw [seed_diagonal]; exact diagonal_nested _ _

theorem shape_append_zeros {s : Matrix} {h : Nat} (hs : Shape h 0 s) (x : Nat) :
    Shape h 0 (s ++ List.replicate x []) := by
  apply shape_append hs
  intro i c hc
  have he : c = [] := List.eq_of_mem_replicate (List.mem_of_getElem? hc)
  subst c
  simp

def fghEncoding (r x : Nat) := sigma (liftW (seed r) ++ List.replicate x [])

theorem fghEncoding_shape {r : Nat} (hr : 1 ≤ r) (x : Nat) :
    Shape (r + 1) 0 (fghEncoding r x) :=
  sigma_shape (shape_append_zeros (liftW_shape (seed_shape r) hr) x)

theorem fghEncoding_nested {r : Nat} (hr : 1 ≤ r) (x : Nat) : Nested (fghEncoding r x) := by
  have hg := append_zeros_graph (leftward_of_shape (liftW_shape (seed_shape r) hr)) (liftW_nested (seed_nested r)) x
  exact sigma_nested hg.1 hg.2

theorem fghEncoding_length (r x : Nat) : (fghEncoding r x).length = x + 4 := by
  simp [fghEncoding, seed]
  omega

/-- A single actual finite three-column budget both realizes the BMS-diagonal
FGH computation and bounds its result. No globally total FGH is presupposed. -/
theorem triple_realizes_fgh {h x n : Nat} (hx : 0 < x) (hb : buffer x ≤ h)
    (ht : PrefixDescent.Stops (fun a => expand a 1) (triple h) n) :
    ∃ y, FastEval (seed (x + 1)) x y ∧ 2 ^ (y + 1) ≤ n := by
  let u := h - x - 3
  have hu : x + 1 ≤ u := by dsimp [u]; dsimp [buffer] at hb; omega
  have hh : (x + 2) + u + 1 = h := by dsimp [u]; dsimp [buffer] at hb; omega
  have hpow : u < 2 ^ u := Nat.lt_two_pow_self
  have hwidth : (fghEncoding (x + 1) x).length ≤ 2 + 2 ^ u := by rw [fghEncoding_length]; omega
  have hstops : PrefixDescent.Stops (fun a => expand a 1) (triple ((x + 2) + u + 1)) n := by rw [hh]; exact ht
  obtain ⟨k, hk, hkn⟩ := triple_compiler_envelope hstops
    (fghEncoding_shape (by omega : 1 ≤ x + 1) x) (fghEncoding_nested (by omega : 1 ≤ x + 1) x) hwidth
  have hl := leftward_of_shape (liftW_shape (seed_shape (x + 1)) (by omega))
  have hn := liftW_nested (seed_nested (x + 1))
  obtain ⟨y, hy⟩ := hardy_exists_of_sigma_stops hk hl hn hx
  have hbound := hy.sigma_bound k hl hn hx hk
  exact ⟨y, hy.to_fast, by omega⟩

/-- Total notation for a partial evaluator. The fallback is never used at
arguments realized by an actual triple budget. -/
noncomputable def diagonalFast (x : Nat) : Nat := by
  classical
  exact if he : ∃ y, FastEval (seed (x + 1)) x y then Classical.choose he else x + 1

theorem diagonalFast_eq {x y : Nat} (he : FastEval (seed (x + 1)) x y) : diagonalFast x = y := by
  classical
  have hex : ∃ z, FastEval (seed (x + 1)) x z := ⟨y, he⟩
  simp only [diagonalFast, dif_pos hex]
  exact (Classical.choose_spec hex).unique he

theorem diagonalFast_grows : Grows diagonalFast := by
  intro x _
  classical
  by_cases he : ∃ y, FastEval (seed (x + 1)) x y
  · obtain ⟨y, hy⟩ := he
    rw [diagonalFast_eq hy]
    exact hy.growth
  · simp only [diagonalFast, dif_neg he]
    omega

theorem triple_diagonal_bound {h x n : Nat} (hx : 0 < x) (hb : buffer x ≤ h)
    (ht : PrefixDescent.Stops (fun a => expand a 1) (triple h) n) :
    FastEval (seed (x + 1)) x (diagonalFast x) ∧ 2 ^ (diagonalFast x + 1) ≤ n := by
  obtain ⟨y, hy, hbnd⟩ := triple_realizes_fgh hx hb ht
  rw [diagonalFast_eq hy]
  exact ⟨hy, hbnd⟩

/-- Off the terminating domain, use a finite envelope as a technical
totalization of D. Actual fan applications always identify D with a real count. -/
noncomputable def countDefault : Nat → Nat
  | 0 => max 3 (2 ^ (diagonalFast 0 + 1))
  | h + 1 => max (countDefault h) (2 ^ (diagonalFast (h + 1) + 1))

theorem countDefault_ge_three (h : Nat) : 3 ≤ countDefault h := by
  induction h with
  | zero => exact Nat.le_max_left _ _
  | succ h ih => exact Nat.le_trans ih (Nat.le_max_left _ _)

theorem countDefault_covers {x h : Nat} (hx : x ≤ h) : 2 ^ (diagonalFast x + 1) ≤ countDefault h := by
  induction h with
  | zero =>
      have he : x = 0 := by omega
      subst x
      exact Nat.le_max_right _ _
  | succ h ih =>
      by_cases he : x = h + 1
      · subst x; exact Nat.le_max_right _ _
      · exact Nat.le_trans (ih (by omega)) (Nat.le_max_left _ _)

#print axioms triple_realizes_fgh
#print axioms triple_diagonal_bound

end LaverLowerBounds.ParentBMS
