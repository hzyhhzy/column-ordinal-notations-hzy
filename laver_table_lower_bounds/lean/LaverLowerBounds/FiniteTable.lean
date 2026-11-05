import Std

/-!
Finite Laver tables, specified by the two defining equations: left
self-distributivity and a*1 = a+1 modulo the size. The carrier is Fin size.
No period, projection, or capped critical-point laws are included as fields.
Those are theorems to be proved from this definition.
-/

set_option autoImplicit false

namespace LaverLowerBounds

structure FiniteTable (size : Nat) where
  positive : 0 < size
  op : Fin size → Fin size → Fin size
  left_distrib : ∀ a b c, op a (op b c) = op (op a b) (op a c)
  right_one : ∀ a,
    op a ⟨1 % size, Nat.mod_lt 1 positive⟩ =
      ⟨(a.val + 1) % size, Nat.mod_lt _ positive⟩

namespace FiniteTable

variable {size : Nat} (T : FiniteTable size)

def numeral (n : Nat) : Fin size := ⟨n % size, Nat.mod_lt _ T.positive⟩

def mul (a b : Nat) : Nat := (T.op (T.numeral a) (T.numeral b)).val

theorem numeral_val (a : Fin size) : T.numeral a.val = a := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt a.isLt

theorem numeral_mul (a b : Nat) :
    T.numeral (T.mul a b) = T.op (T.numeral a) (T.numeral b) := T.numeral_val _

theorem mul_lt (a b : Nat) : T.mul a b < size := (T.op _ _).isLt

@[simp] theorem numeral_mod (a : Nat) : T.numeral (a % size) = T.numeral a := by
  apply Fin.ext
  simp [numeral]

@[simp] theorem mul_mod_left (a b : Nat) : T.mul (a % size) b = T.mul a b := by
  simp only [mul, numeral_mod]

@[simp] theorem mul_mod_right (a b : Nat) : T.mul a (b % size) = T.mul a b := by
  simp only [mul, numeral_mod]

theorem mul_one (a : Nat) : T.mul a 1 = (a + 1) % size := by
  unfold mul
  have h := congrArg Fin.val (T.right_one (T.numeral a))
  simpa [numeral, Nat.add_mod] using h

theorem mul_distrib (a b c : Nat) :
    T.mul a (T.mul b c) = T.mul (T.mul a b) (T.mul a c) := by
  unfold mul
  rw [T.numeral_val, T.numeral_val, T.numeral_val, T.left_distrib]

theorem row_recurrence (a b : Nat) : T.mul a (b + 1) = T.mul (T.mul a b) (a + 1) := by
  calc
    T.mul a (b + 1) = T.mul a (T.mul b 1) := by rw [T.mul_one, T.mul_mod_right]
    _ = T.mul (T.mul a b) (T.mul a 1) := T.mul_distrib a b 1
    _ = T.mul (T.mul a b) (a + 1) := by rw [T.mul_one, T.mul_mod_right]

theorem zero_mul_succ (b : Nat) : T.mul 0 (b + 1) = (b + 1) % size := by
  induction b with
  | zero => exact T.mul_one 0
  | succ b ih =>
      rw [T.row_recurrence, T.mul_one, ih]
      exact Nat.mod_add_mod (b + 1) size 1

theorem zero_mul (b : Nat) : T.mul 0 b = b % size := by
  cases b with
  | zero =>
      have h := T.zero_mul_succ (size - 1)
      have he : size - 1 + 1 = size := by have := T.positive; omega
      rw [he] at h
      have hmod := T.mul_mod_right 0 size
      simpa using hmod.trans h
  | succ b => exact T.zero_mul_succ b

/-- Positive values in row a are strictly larger than a.
This is the elementary decreasing-row construction invariant. -/
theorem row_grows (a b : Nat) (ha : a < size) : T.mul a b = 0 ∨ a < T.mul a b := by
  suffices h : ∀ k a, size - a = k → a < size →
      ∀ b, T.mul a b = 0 ∨ a < T.mul a b from h (size - a) a rfl ha b
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
      intro a hka ha
      have hfirst : (a + 1) % size = 0 ∨ a < (a + 1) % size := by
        by_cases h : a + 1 = size
        · rw [h, Nat.mod_self]
          exact Or.inl rfl
        · have hlt : a + 1 < size := by omega
          rw [Nat.mod_eq_of_lt hlt]
          exact Or.inr (Nat.lt_succ_self a)
      have hpos : ∀ b, T.mul a (b + 1) = 0 ∨ a < T.mul a (b + 1) := by
        intro b
        induction b with
        | zero => simpa only [T.mul_one] using hfirst
        | succ b hb =>
            rw [T.row_recurrence]
            rcases hb with hz | hgt
            · rw [hz, T.zero_mul]
              exact hfirst
            · have hc : T.mul a (b + 1) < size := T.mul_lt _ _
              have hk : size - T.mul a (b + 1) < k := by omega
              have hh := ih _ hk _ rfl hc (a + 1)
              rcases hh with hz | hgt'
              · exact Or.inl hz
              · exact Or.inr (Nat.lt_trans hgt hgt')
      intro b
      cases b with
      | zero =>
          have h := hpos (size - 1)
          have he : size - 1 + 1 = size := by have := T.positive; omega
          rw [he, ← T.mul_mod_right a size, Nat.mod_self] at h
          exact h
      | succ b => exact hpos b

/-- Column zero is zero. This is derived, not an extra table axiom. -/
theorem mul_zero (a : Nat) : T.mul a 0 = 0 := by
  have ha : a % size < size := Nat.mod_lt _ T.positive
  have h := T.row_grows (a % size) 0 ha
  rw [T.mul_mod_left] at h
  rcases h with hz | hgt
  · exact hz
  · have hc := T.mul_lt a 0
    have hnext := T.row_recurrence a 0
    rw [T.mul_one] at hnext
    have hrow := T.row_grows (T.mul a 0) (a + 1) hc
    rw [← hnext] at hrow
    have hsucc : (a + 1) % size = (a % size + 1) % size :=
      (Nat.mod_add_mod a size 1).symm
    rw [hsucc] at hrow
    by_cases htop : a % size + 1 = size
    · have : T.mul a 0 ≥ size := by omega
      omega
    · have hlt : a % size + 1 < size := by omega
      rw [Nat.mod_eq_of_lt hlt] at hrow
      rcases hrow with hzero | hlarge <;> omega

/-- The defining equations determine the operation uniquely. -/
theorem mul_unique (U : FiniteTable size) (a b : Nat) : T.mul a b = U.mul a b := by
  suffices h : ∀ k a, size - a = k → a < size → ∀ b, T.mul a b = U.mul a b by
    have h' := h (size - a % size) (a % size) rfl (Nat.mod_lt _ T.positive) b
    simpa only [T.mul_mod_left, U.mul_mod_left] using h'
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
      intro a hka ha b
      induction b with
      | zero => rw [T.mul_zero, U.mul_zero]
      | succ b hb =>
          rw [T.row_recurrence, U.row_recurrence, hb]
          rcases U.row_grows a b ha with hz | hgt
          · rw [hz, T.zero_mul, U.zero_mul]
          · have hc := U.mul_lt a b
            exact ih (size - U.mul a b) (by omega) (U.mul a b) rfl hc (a + 1)

theorem op_unique (U : FiniteTable size) : T.op = U.op := by
  funext a b
  apply Fin.ext
  have h := T.mul_unique U a.val b.val
  simpa only [mul, numeral_val] using h

/-- Reduction modulo a divisor is automatically a homomorphism whenever the
smaller defining table exists. No projection law is assumed as a field. -/
theorem projection {small : Nat} (U : FiniteTable small) (hdiv : small ∣ size)
    (a b : Nat) : T.mul a b % small = U.mul a b := by
  suffices h : ∀ k a, size - a = k → a < size →
      ∀ b, T.mul a b % small = U.mul a b by
    have h' := h (size - a % size) (a % size) rfl (Nat.mod_lt _ T.positive) b
    rw [T.mul_mod_left] at h'
    have he : U.mul (a % size) b = U.mul a b := by
      rw [← U.mul_mod_left (a % size) b, Nat.mod_mod_of_dvd a hdiv, U.mul_mod_left]
    exact h'.trans he
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
      intro a hka ha b
      induction b with
      | zero => simp only [T.mul_zero, U.mul_zero, Nat.zero_mod]
      | succ b hb =>
          rw [T.row_recurrence, U.row_recurrence]
          have hrow : T.mul (T.mul a b) (a + 1) % small = U.mul (T.mul a b) (a + 1) := by
            rcases T.row_grows a b ha with hz | hgt
            · rw [hz, T.zero_mul, U.zero_mul, Nat.mod_mod_of_dvd _ hdiv]
            · have hc := T.mul_lt a b
              exact ih (size - T.mul a b) (by omega) (T.mul a b) rfl hc (a + 1)
          rw [hrow, ← U.mul_mod_left (T.mul a b), hb]

def FirstZero (a p : Nat) : Prop :=
  0 < p ∧ T.mul a p = 0 ∧ ∀ b, 0 < b → b < p → T.mul a b ≠ 0

theorem exists_firstZero (a : Nat) : ∃ p, T.FirstZero a p := by
  have aux : ∀ n, 0 < n → T.mul a n = 0 → ∃ p, T.FirstZero a p := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro hn hz
        by_cases hsmall : ∃ k, 0 < k ∧ k < n ∧ T.mul a k = 0
        · obtain ⟨k, hk, hkn, hzero⟩ := hsmall
          exact ih k hkn hk hzero
        · refine ⟨n, hn, hz, ?_⟩
          intro b hb hbn hzero
          exact hsmall ⟨b, hb, hbn, hzero⟩
  apply aux size T.positive
  rw [← T.mul_mod_right a size, Nat.mod_self, T.mul_zero]

/-- A zero starts the row again; no power-of-two fact is used here. -/
theorem periodic_of_zero {a p : Nat} (hp : T.mul a p = 0) (b : Nat) :
    T.mul a (p + b) = T.mul a b := by
  induction b with
  | zero => simpa only [Nat.add_zero, T.mul_zero] using hp
  | succ b ih =>
      rw [Nat.add_succ, T.row_recurrence a (p + b), T.row_recurrence a b, ih]

theorem periodic_multiple {a p : Nat} (hp : T.mul a p = 0) (q b : Nat) :
    T.mul a (p * q + b) = T.mul a b := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Nat.mul_succ]
      have he : p * q + p + b = p + (p * q + b) := by omega
      rw [he, T.periodic_of_zero hp, ih]

theorem reduce_period {a p : Nat} (hp : T.mul a p = 0) (b : Nat) :
    T.mul a b = T.mul a (b % p) := by
  have h := T.periodic_multiple hp (b / p) (b % p)
  have he : p * (b / p) + b % p = b := Nat.div_add_mod b p
  rw [he] at h
  exact h

theorem firstZero_iff_mod {a p : Nat} (hp : T.FirstZero a p) (b : Nat) :
    T.mul a b = 0 ↔ b % p = 0 := by
  obtain ⟨hpos, hz, hmin⟩ := hp
  rw [T.reduce_period hz b]
  constructor
  · intro h
    by_cases hn : b % p = 0
    · exact hn
    · exact False.elim (hmin (b % p) (by omega) (Nat.mod_lt _ hpos) h)
  · intro h
    rw [h, T.mul_zero]

theorem firstZero_dvd_size {a p : Nat} (hp : T.FirstZero a p) : p ∣ size := by
  apply Nat.dvd_of_mod_eq_zero
  apply (T.firstZero_iff_mod hp size).mp
  rw [← T.mul_mod_right a size, Nat.mod_self, T.mul_zero]

/-- The least zero is the ordinary least positive period of the row. -/
theorem firstZero_is_period {a p : Nat} (hp : T.FirstZero a p) :
    (∀ b, T.mul a (p + b) = T.mul a b) ∧
      ∀ k, 0 < k → (∀ b, T.mul a (k + b) = T.mul a b) → p ≤ k := by
  refine ⟨T.periodic_of_zero hp.2.1, ?_⟩
  intro k hk hperiod
  have hz : T.mul a k = 0 := by simpa only [Nat.add_zero, T.mul_zero] using hperiod 0
  by_cases h : p ≤ k
  · exact h
  · exact False.elim (hp.2.2 k hk (by omega) hz)

/-- Composition is defined by the table; it is not a new primitive operation. -/
def comp (a b : Nat) : Nat := (T.mul a (b + 1) + size - 1) % size

include T in
theorem predecessor_successor (a : Nat) :
    ((a + 1) % size + size - 1) % size = a % size := by
  have hpos := T.positive
  have h₁ : (a + 1) % size + size - 1 = (a + 1) % size + (size - 1) := by omega
  rw [h₁, Nat.mod_add_mod]
  have h₂ : a + 1 + (size - 1) = a + size := by have := T.positive; omega
  rw [h₂, Nat.add_mod_right]

theorem comp_zero (a : Nat) : T.comp a 0 = a % size := by
  unfold comp
  rw [T.mul_one]
  exact T.predecessor_successor a

theorem zero_comp (a : Nat) : T.comp 0 a = a % size := by
  unfold comp
  rw [T.zero_mul]
  exact T.predecessor_successor a

theorem comp_mod_left (a b : Nat) : T.comp (a % size) b = T.comp a b := by
  simp only [comp, T.mul_mod_left]

theorem comp_mod_right (a b : Nat) : T.comp a (b % size) = T.comp a b := by
  have he : T.mul a (b % size + 1) = T.mul a (b + 1) := by
    rw [← T.mul_mod_right a (b % size + 1), Nat.mod_add_mod, T.mul_mod_right]
  simp only [comp, he]

theorem comp_swap (a b : Nat) : T.comp a b = T.comp (T.mul a b) a := by
  unfold comp
  rw [T.row_recurrence a b]

theorem comp_one (a b : Nat) : T.mul (T.comp a b) 1 = T.mul a (b + 1) := by
  rw [T.mul_one]
  unfold comp
  rw [Nat.mod_add_mod]
  have he : T.mul a (b + 1) + size - 1 + 1 = T.mul a (b + 1) + size := by
    have := T.positive
    omega
  rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (T.mul_lt _ _)]

/-- Left translation by a composition is composition of left translations. -/
theorem comp_mul (a b c : Nat) : T.mul (T.comp a b) c = T.mul a (T.mul b c) := by
  induction c with
  | zero => rw [T.mul_zero, T.mul_zero, T.mul_zero]
  | succ c ih =>
      rw [T.row_recurrence (T.comp a b) c]
      calc
        T.mul (T.mul (T.comp a b) c) (T.comp a b + 1) =
            T.mul (T.mul (T.comp a b) c) (T.mul (T.comp a b) 1) := by
              rw [T.mul_one, T.mul_mod_right]
        _ = T.mul (T.mul a (T.mul b c)) (T.mul a (b + 1)) := by rw [ih, T.comp_one]
        _ = T.mul a (T.mul (T.mul b c) (b + 1)) := (T.mul_distrib _ _ _).symm
        _ = T.mul a (T.mul b (c + 1)) := by rw [T.row_recurrence b c]

/-- The final LL identity. Decreasing-row induction avoids cancellation of
point actions or a spurious injectivity assumption at the finite cap.
Proof pattern: Dougherty--Jech, finite-algebra construction (Section 3). -/
theorem mul_comp (a b c : Nat) :
    T.mul a (T.comp b c) = T.comp (T.mul a b) (T.mul a c) := by
  have zero_case : ∀ a c,
      T.mul a (T.comp 0 c) = T.comp (T.mul a 0) (T.mul a c) := by
    intro a c
    rw [T.zero_comp, T.mul_mod_right, T.mul_zero, T.zero_comp,
      Nat.mod_eq_of_lt (T.mul_lt a c)]
  suffices h : ∀ k b, size - b = k → b < size → ∀ a c,
      T.mul a (T.comp b c) = T.comp (T.mul a b) (T.mul a c) by
    have h' := h (size - b % size) (b % size) rfl (Nat.mod_lt _ T.positive) a c
    simpa only [T.comp_mod_left, T.mul_mod_right] using h'
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
      intro b hkb hb a c
      have hd : T.mul a (T.comp (T.mul b c) b) =
          T.comp (T.mul a (T.mul b c)) (T.mul a b) := by
        rcases T.row_grows b c hb with hz | hgt
        · rw [hz]
          exact zero_case a b
        · have hc := T.mul_lt b c
          exact ih (size - T.mul b c) (by omega) (T.mul b c) rfl hc a b
      calc
        T.mul a (T.comp b c) = T.mul a (T.comp (T.mul b c) b) := by rw [T.comp_swap b c]
        _ = T.comp (T.mul a (T.mul b c)) (T.mul a b) := hd
        _ = T.comp (T.mul (T.mul a b) (T.mul a c)) (T.mul a b) := by rw [T.mul_distrib]
        _ = T.comp (T.mul a b) (T.mul a c) := (T.comp_swap _ _).symm

/-- Positive entries before the first zero are strictly increasing. -/
theorem firstZero_strict {a p : Nat} (hp : T.FirstZero a p)
    {b c : Nat} (hb : 0 < b) (hbc : b < c) (hc : c < p) :
    T.mul a b < T.mul a c := by
  have single : ∀ k, 0 < k → k + 1 < p → T.mul a k < T.mul a (k + 1) := by
    intro k hk hkp
    have hg := T.row_grows (T.mul a k) (a + 1) (T.mul_lt _ _)
    rw [← T.row_recurrence] at hg
    rcases hg with hz | hlt
    · exact False.elim (hp.2.2 (k + 1) (by omega) hkp hz)
    · exact hlt
  induction c with
  | zero => omega
  | succ c ih =>
      by_cases he : b = c
      · subst b
        exact single c hb hc
      · have hbc' : b < c := by omega
        have h₁ := ih hbc' (by omega)
        have h₂ := single c (by omega) hc
        exact Nat.lt_trans h₁ h₂

#print axioms row_recurrence
#print axioms zero_mul
#print axioms row_grows
#print axioms mul_zero
#print axioms op_unique
#print axioms projection
#print axioms firstZero_dvd_size
#print axioms firstZero_is_period
#print axioms comp_mul
#print axioms mul_comp
#print axioms firstZero_strict

end FiniteTable
end LaverLowerBounds
