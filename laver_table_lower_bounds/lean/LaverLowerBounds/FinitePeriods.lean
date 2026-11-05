import LaverLowerBounds.FiniteTable

set_option autoImplicit false

namespace LaverLowerBounds.FiniteTable

theorem multiple_below_twice {v n : Nat} (hv : v < n * 2) (hmod : v % n = 0) :
    v = 0 ∨ v = n := by
  by_cases hlt : v < n
  · rw [Nat.mod_eq_of_lt hlt] at hmod
    exact Or.inl hmod
  · have hle : n ≤ v := by omega
    rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt (by omega : v - n < n)] at hmod
    exact Or.inr (by omega)

variable {size : Nat}

theorem firstZero_le_of_zero (T : FiniteTable size) {a p b : Nat}
    (hp : T.FirstZero a p) (hb : 0 < b) (hz : T.mul a b = 0) : p ≤ b := by
  by_cases h : p ≤ b
  · exact h
  · exact False.elim (hp.2.2 b hb (by omega) hz)

/-- On doubling the table size, a row's least period stays fixed or doubles.
This is derived from projection and strict increase before the first zero. -/
theorem period_stays_or_doubles (T : FiniteTable (size * 2)) (U : FiniteTable size)
    {a p q : Nat} (hp : T.FirstZero a p) (hq : U.FirstZero a q) :
    p = q ∨ p = 2 * q := by
  have hdiv : size ∣ size * 2 := ⟨2, rfl⟩
  have hpzero : U.mul a p = 0 := by
    rw [← T.projection U hdiv, hp.2.1, Nat.zero_mod]
  have hqp : q ≤ p := U.firstZero_le_of_zero hq hp.1 hpzero
  have hqdiv : p % q = 0 := (U.firstZero_iff_mod hq p).mp hpzero
  have htwo : p ≤ 2 * q := by
    by_cases h : p ≤ 2 * q
    · exact h
    · have hqz : T.mul a q % size = 0 := by rw [T.projection U hdiv, hq.2.1]
      have h2qz : T.mul a (2 * q) % size = 0 := by
        rw [T.projection U hdiv]
        apply (U.firstZero_iff_mod hq (2 * q)).mpr
        simp
      have hqne := hp.2.2 q hq.1 (by omega)
      have h2qne := hp.2.2 (2 * q) (by have := hq.1; omega) (by omega)
      have hqvalue : T.mul a q = size := by
        rcases multiple_below_twice (T.mul_lt a q) hqz with hz | he
        · exact False.elim (hqne hz)
        · exact he
      have h2qvalue : T.mul a (2 * q) = size := by
        rcases multiple_below_twice (T.mul_lt a (2 * q)) h2qz with hz | he
        · exact False.elim (h2qne hz)
        · exact he
      have hstrict := T.firstZero_strict hp hq.1 (by have := hq.1; omega)
        (by omega : 2 * q < p)
      rw [hqvalue, h2qvalue] at hstrict
      omega
  by_cases he : p = 2 * q
  · exact Or.inr he
  · have hlt : p < q * 2 := by omega
    rcases multiple_below_twice hlt hqdiv with hz | heq
    · have := hp.1
      omega
    · exact Or.inl heq

abbrev BinaryFamily := ∀ n : Nat, FiniteTable (2 ^ n)

theorem period_is_power_two (family : BinaryFamily) (m a p : Nat)
    (hp : (family m).FirstZero a p) : ∃ k, k ≤ m ∧ p = 2 ^ k := by
  induction m generalizing p with
  | zero =>
      have hle := (family 0).firstZero_le_of_zero hp (by decide : 0 < 2 ^ 0)
        (by rw [← (family 0).mul_mod_right a (2 ^ 0), Nat.mod_self, (family 0).mul_zero])
      have hpos := hp.1
      exact ⟨0, Nat.le_refl _, by omega⟩
  | succ m ih =>
      obtain ⟨q, hq⟩ := (family m).exists_firstZero a
      obtain ⟨k, hkm, hk⟩ := ih q hq
      have hd := period_stays_or_doubles (family (m + 1)) (family m) hp hq
      rcases hd with heq | hdouble
      · exact ⟨k, by omega, heq.trans hk⟩
      · refine ⟨k + 1, by omega, ?_⟩
        rw [hdouble, hk, Nat.pow_succ, Nat.mul_comm]

/-- Ordinary first-row period at least 32, without assuming q(5) exists. -/
def PeriodAtLeast32 (T : FiniteTable size) : Prop :=
  ∀ p, T.FirstZero 1 p → 32 ≤ p

theorem periodAtLeast32_iff (family : BinaryFamily) (m : Nat) :
    PeriodAtLeast32 (family m) ↔ (family m).mul 1 16 ≠ 0 := by
  constructor
  · intro h hz
    obtain ⟨p, hp⟩ := (family m).exists_firstZero 1
    have hlarge := h p hp
    exact hp.2.2 16 (by decide) (by omega) hz
  · intro h p hp
    obtain ⟨k, _, hk⟩ := period_is_power_two family m 1 p hp
    by_cases hlarge : 5 ≤ k
    · have hpow := Nat.pow_le_pow_right (n := 2) (by decide) hlarge
      simpa only [← hk] using hpow
    · have hkle : k ≤ 4 := by omega
      have hpowdiv : 2 ^ k ∣ 2 ^ 4 := Nat.pow_dvd_pow 2 hkle
      have hmod : 16 % p = 0 := by
        rw [hk]
        exact Nat.mod_eq_zero_of_dvd hpowdiv
      have hz := ((family m).firstZero_iff_mod hp 16).mpr hmod
      exact False.elim (h hz)

/-- q(5)=m is a conditional least-threshold assertion, not a total function. -/
def Q5At (family : BinaryFamily) (m : Nat) : Prop :=
  PeriodAtLeast32 (family m) ∧ ∀ k, k < m → ¬ PeriodAtLeast32 (family k)

#print axioms period_stays_or_doubles
#print axioms period_is_power_two
#print axioms periodAtLeast32_iff

end LaverLowerBounds.FiniteTable
