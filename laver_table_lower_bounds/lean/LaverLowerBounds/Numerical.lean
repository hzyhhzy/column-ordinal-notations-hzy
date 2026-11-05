import LaverLowerBounds.Iteration

/-!
The complete *numerical* part of the Lambda+omega+1 comparison.

This file does not assert the concrete BMS counting estimate or the finite
Laver-table budget. Both are explicit hypotheses of the final interface theorem.
The row buffer is 4(x+1), replacing the logarithmic buffer of the paper.
Only an exponential lower bound on D is needed, rather than a full power tower.
-/

set_option autoImplicit false

namespace LaverLowerBounds

def tower : Nat → Nat
  | 0 => 1
  | n + 1 => 2 ^ tower n

theorem exponential_le_tower (n : Nat) (hn : 3 ≤ n) : 2 ^ (n + 1) ≤ tower n := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases h : 3 ≤ n
      · have hi := ih h
        have hp : n + 1 < 2 ^ (n + 1) := Nat.lt_two_pow_self
        have he : n + 1 + 1 ≤ tower n := by omega
        exact Nat.pow_le_pow_right (by decide) he
      · have he : n = 2 := by omega
        subst n
        decide

theorem buffer_le_exp_add_two (n : Nat) (hn : 3 ≤ n) :
    buffer n ≤ 2 ^ (n + 1) + 2 := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases h : 3 ≤ n
      · have hi := ih h
        have hp : 2 ^ (n + 1) ≥ 4 := by
          have hp' := Nat.pow_le_pow_right (n := 2) (by decide)
            (show 2 ≤ n + 1 by omega)
          exact hp'
        simp only [buffer, Nat.pow_succ] at hi ⊢
        omega
      · have he : n = 2 := by omega
        subst n
        decide

/-- The one substantive BMS numerical input required below. -/
def CountingEstimate (D g : Nat → Nat) : Prop :=
  ∀ x h, 2 ≤ x → buffer x ≤ h → 2 ^ (g x + 1) ≤ D h

theorem countingEstimate_of_tower {D g : Nat → Nat} (hg : Grows g)
    (hD : ∀ x h, 2 ≤ x → buffer x ≤ h → tower (g x) ≤ D h) :
    CountingEstimate D g := by
  intro x h hx hh
  have hge := hg x hx
  exact Nat.le_trans (exponential_le_tower (g x) (by omega)) (hD x h hx hh)

def base (D : Nat → Nat) (h : Nat) : Nat := D h + 2

def upgrade (D f : Nat → Nat) (h : Nat) : Nat :=
  iter f (D (f h) + 1) h

def stage (D : Nat → Nat) : Nat → Nat → Nat
  | 0 => base D
  | n + 1 => upgrade D (stage D n)

def depth (D : Nat → Nat) (h : Nat) : Nat := Nat.log2 (D (base D h))

def dynamic (D : Nat → Nat) (h : Nat) : Nat := stage D (depth D h) h

def finalHeight (D : Nat → Nat) : Nat → Nat := upgrade D (dynamic D)

theorem count_gt_input {D g : Nat → Nat} (hg : Grows g)
    (hD : CountingEstimate D g) {x h : Nat} (hx : 2 ≤ x) (hh : buffer x ≤ h) :
    x < D h := by
  have h₁ := hD x h hx hh
  have h₂ := hg x hx
  have h₃ : g x + 1 < 2 ^ (g x + 1) := Nat.lt_two_pow_self
  omega

theorem base_simulates {D g : Nat → Nat} (hg : Grows g)
    (hD : CountingEstimate D g) : Simulates (base D) g := by
  intro x h hx hh
  have h₁ := hD x h hx hh
  have h₂ := hg x hx
  have h₃ := buffer_le_exp_add_two (g x) (by omega)
  unfold base
  omega

theorem upgrade_simulates {D g f j : Nat → Nat}
    (hg : Grows g) (hD : CountingEstimate D g)
    (hj : Grows j) (hs : Simulates f j) :
    Simulates (upgrade D f) (fun x => iter j (x + 1) x) := by
  intro x h hx hh
  have hsim := hs x h hx hh
  have hjx := hj x hx
  have hcount := count_gt_input hg hD (by omega : 2 ≤ j x) hsim
  have hn : x + 1 ≤ D (f h) + 1 := by omega
  exact iter_simulates_of_le hj hs hn hx hh

theorem stage_simulates {D g : Nat → Nat} (hg : Grows g)
    (hD : CountingEstimate D g) (n : Nat) :
    Simulates (stage D n) (level g n) := by
  induction n with
  | zero => exact base_simulates hg hD
  | succ n ih => exact upgrade_simulates hg hD (level_grows g hg n) ih

theorem depth_ge {D g : Nat → Nat} (hg : Grows g)
    (hD : CountingEstimate D g) {x h : Nat} (hx : 2 ≤ x) (hh : buffer x ≤ h) :
    x + 1 ≤ depth D h := by
  have hT := base_simulates hg hD x h hx hh
  have hx₁ := hg x hx
  have hx₂ := hg (g x) (by omega)
  have hb := hD (g x) (base D h) (by omega) hT
  have hp : 2 ^ (x + 1) ≤ 2 ^ (g (g x) + 1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hn : D (base D h) ≠ 0 := by
    have hpos : 0 < 2 ^ (g (g x) + 1) := Nat.two_pow_pos _
    omega
  exact (Nat.le_log2 hn).mpr (Nat.le_trans hp hb)

theorem dynamic_simulates {D g : Nat → Nat} (hg : Grows g)
    (hD : CountingEstimate D g) : Simulates (dynamic D) (diagonal g) := by
  intro x h hx hh
  have hn := depth_ge hg hD hx hh
  have hl := level_mono g hg x hx hn
  exact Nat.le_trans (buffer_mono hl) (stage_simulates hg hD (depth D h) x h hx hh)

theorem finalHeight_simulates {D g : Nat → Nat} (hg : Grows g)
    (hD : CountingEstimate D g) : Simulates (finalHeight D) (omegaSuccessor g) :=
  upgrade_simulates hg hD (diagonal_grows g hg) (dynamic_simulates hg hD)

/-- Generic numerical interface. The concrete CountingEstimate and the finite
Laver-table budget are supplied in FiniteFGHBound.lean; OriginalBMSBound.lean
states the resulting theorem for the original numeric BM4 evaluator.
-/
theorem numerical_bound {D g : Nat → Nat} (hg : Grows g)
    (hD : CountingEstimate D g) {m x h : Nat} (hx : 2 ≤ x)
    (hh : buffer x ≤ h) (hbudget : D (finalHeight D h) < m) :
    omegaSuccessor g x < m := by
  have hsim := finalHeight_simulates hg hD x h hx hh
  have hx' := omegaSuccessor_grows g hg x hx
  have hlast := count_gt_input hg hD (by omega) hsim
  omega

theorem numerical_bound_at_100 {D g : Nat → Nat} (hg : Grows g)
    (hD : CountingEstimate D g) {m : Nat}
    (hbudget : D (finalHeight D 404) < m) : omegaSuccessor g 100 < m :=
  numerical_bound hg hD (by decide) (by decide) hbudget

/-- The short 16-line initialization gives initial fan height 18, once the
fan insertion bridge has been supplied. It supports input 3 (buffer 3 = 16). -/
theorem numerical_bound_at_three {D g : Nat → Nat} (hg : Grows g)
    (hD : CountingEstimate D g) {m : Nat}
    (hbudget : D (finalHeight D 18) < m) : omegaSuccessor g 3 < m :=
  numerical_bound hg hD (by decide) (by decide) hbudget

#print axioms countingEstimate_of_tower
#print axioms stage_simulates
#print axioms dynamic_simulates
#print axioms numerical_bound_at_100
#print axioms numerical_bound_at_three

end LaverLowerBounds
