import LaverLowerBounds.FinitePeriods

set_option autoImplicit false

namespace LaverLowerBounds.FiniteTable

/-- Capped 2-adic valuation, including signature m 0 = m. -/
def signature : Nat → Nat → Nat
  | 0, _ => 0
  | m + 1, a => if a % (2 ^ (m + 1)) = 0 then m + 1 else signature m a

theorem signature_le (m a : Nat) : signature m a ≤ m := by
  induction m with
  | zero => exact Nat.le_refl _
  | succ m ih =>
      simp only [signature]
      split <;> omega

theorem le_signature (m a r : Nat) (hr : r ≤ m) :
    r ≤ signature m a ↔ a % (2 ^ r) = 0 := by
  induction m generalizing r with
  | zero =>
      have he : r = 0 := by omega
      subst r
      simp [signature, Nat.mod_one]
  | succ m ih =>
      by_cases hz : a % (2 ^ (m + 1)) = 0
      · rw [signature, if_pos hz]
        have hd : 2 ^ r ∣ a := Nat.dvd_trans (Nat.pow_dvd_pow 2 hr)
          (Nat.dvd_of_mod_eq_zero hz)
        exact ⟨fun _ => Nat.mod_eq_zero_of_dvd hd, fun _ => hr⟩
      · rw [signature, if_neg hz]
        by_cases hrm : r ≤ m
        · exact ih r hrm
        · have he : r = m + 1 := by omega
          subst r
          constructor
          · intro h
            have := signature_le m a
            omega
          · intro h
            exact False.elim (hz h)

theorem signature_zero (m : Nat) : signature m 0 = m := by
  apply Nat.le_antisymm (signature_le m 0)
  exact (le_signature m 0 m (Nat.le_refl _)).mpr (by simp)

theorem signature_ext {m a b : Nat}
    (h : ∀ r, r ≤ m → (a % 2 ^ r = 0 ↔ b % 2 ^ r = 0)) :
    signature m a = signature m b := by
  apply Nat.le_antisymm
  · apply (le_signature m b _ (signature_le m a)).mpr
    apply (h _ (signature_le m a)).mp
    exact (le_signature m a _ (signature_le m a)).mp (Nat.le_refl _)
  · apply (le_signature m a _ (signature_le m b)).mpr
    apply (h _ (signature_le m b)).mpr
    exact (le_signature m b _ (signature_le m b)).mp (Nat.le_refl _)

theorem signature_mod_eq {m a b : Nat} (h : a % 2 ^ m = b % 2 ^ m) :
    signature m a = signature m b := by
  apply signature_ext
  intro r hr
  have hd := Nat.pow_dvd_pow 2 hr
  have he := congrArg (fun x => x % 2 ^ r) h
  simp only [Nat.mod_mod_of_dvd _ hd] at he
  rw [he]

theorem pow_mod_zero_iff (x r : Nat) : 2 ^ x % 2 ^ r = 0 ↔ r ≤ x := by
  constructor
  · intro h
    exact (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 2)).mp (Nat.dvd_of_mod_eq_zero h)
  · intro h
    exact Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 h)

def act (family : BinaryFamily) (m a x : Nat) : Nat :=
  signature m ((family m).mul a (2 ^ x))

theorem act_le (family : BinaryFamily) (m a x : Nat) : act family m a x ≤ m :=
  signature_le _ _

theorem le_act_iff (family : BinaryFamily) (m a x r : Nat) (hr : r ≤ m) :
    r ≤ act family m a x ↔ (family r).mul a (2 ^ x) = 0 := by
  unfold act
  rw [le_signature _ _ _ hr, (family m).projection (family r) (Nat.pow_dvd_pow 2 hr)]

theorem le_act (family : BinaryFamily) (m a x : Nat) (hx : x ≤ m) :
    x ≤ act family m a x := by
  apply (le_act_iff family m a x x hx).mpr
  rw [← (family x).mul_mod_right a (2 ^ x), Nat.mod_self, (family x).mul_zero]

theorem signature_mul (family : BinaryFamily) (m a b : Nat) :
    signature m ((family m).mul a b) = act family m a (signature m b) := by
  apply signature_ext
  intro r hr
  rw [(family m).projection (family r) (Nat.pow_dvd_pow 2 hr)]
  rw [(family m).projection (family r) (Nat.pow_dvd_pow 2 hr)]
  obtain ⟨p, hp⟩ := (family r).exists_firstZero a
  obtain ⟨k, hkr, hk⟩ := period_is_power_two family r a p hp
  rw [(family r).firstZero_iff_mod hp, (family r).firstZero_iff_mod hp, hk,
    pow_mod_zero_iff]
  exact (le_signature m b k (Nat.le_trans hkr hr)).symm

theorem act_application (family : BinaryFamily) (m a b x : Nat) :
    act family m ((family m).mul a b) (act family m a x) =
      act family m a (act family m b x) := by
  change act family m ((family m).mul a b)
    (signature m ((family m).mul a (2 ^ x))) = _
  rw [← signature_mul, ← (family m).mul_distrib, signature_mul]
  rfl

theorem act_composition (family : BinaryFamily) (m a b x : Nat) :
    act family m ((family m).comp a b) x = act family m a (act family m b x) := by
  unfold act
  rw [(family m).comp_mul, signature_mul]
  rfl

theorem act_mono (family : BinaryFamily) (m a : Nat) {x y : Nat} (hxy : x ≤ y) :
    act family m a x ≤ act family m a y := by
  let r := act family m a x
  have hr : r ≤ m := act_le family m a x
  have hx : (family r).mul a (2 ^ x) = 0 :=
    (le_act_iff family m a x r hr).mp (Nat.le_refl _)
  obtain ⟨p, hp⟩ := (family r).exists_firstZero a
  have hd : p ∣ 2 ^ x := Nat.dvd_of_mod_eq_zero (((family r).firstZero_iff_mod hp _).mp hx)
  have hd' : p ∣ 2 ^ y := Nat.dvd_trans hd (Nat.pow_dvd_pow 2 hxy)
  apply (le_act_iff family m a y r hr).mpr
  exact ((family r).firstZero_iff_mod hp _).mpr (Nat.mod_eq_zero_of_dvd hd')

/-- Successive inputs move at least one level unless already saturated. -/
theorem act_next (family : BinaryFamily) (m a x : Nat) (hx : act family m a x < m) :
    act family m a x + 1 ≤ act family m a (x + 1) := by
  let r := act family m a x
  have hr : r ≤ m := act_le family m a x
  have hr' : r + 1 ≤ m := by omega
  have hz : (family r).mul a (2 ^ x) = 0 :=
    (le_act_iff family m a x r hr).mp (Nat.le_refl _)
  obtain ⟨q, hq⟩ := (family r).exists_firstZero a
  obtain ⟨p, hp⟩ := (family (r + 1)).exists_firstZero a
  have hdiv : q ∣ 2 ^ x := Nat.dvd_of_mod_eq_zero (((family r).firstZero_iff_mod hq _).mp hz)
  have hnext : p ∣ 2 ^ (x + 1) := by
    rcases period_stays_or_doubles (family (r + 1)) (family r) hp hq with he | he
    · rw [he]
      exact Nat.dvd_trans hdiv (Nat.pow_dvd_pow 2 (by omega))
    · rw [he, Nat.pow_succ, Nat.mul_comm (2 ^ x) 2]
      exact Nat.mul_dvd_mul_left 2 hdiv
  apply (le_act_iff family m a (x + 1) (r + 1) hr').mpr
  exact ((family (r + 1)).firstZero_iff_mod hp _).mpr (Nat.mod_eq_zero_of_dvd hnext)

theorem act_strict_below_cap (family : BinaryFamily) (m a x y : Nat)
    (hxy : x < y) (hy : act family m a y < m) :
    act family m a x < act family m a y := by
  have hmono := act_mono family m a (Nat.le_of_lt hxy)
  have hnext := act_next family m a x (by omega)
  have htail := act_mono family m a (show x + 1 ≤ y by omega)
  omega

#print axioms signature_mul
#print axioms act_application
#print axioms act_composition
#print axioms act_strict_below_cap

end LaverLowerBounds.FiniteTable
