import LaverLowerBounds.FiniteLines

set_option autoImplicit false

namespace LaverLowerBounds.FiniteTable

theorem residue_at_signature {m a r : Nat} (hr : r < m) (hs : signature m a = r) :
    a % 2 ^ (r + 1) = 2 ^ r := by
  have hz : a % 2 ^ r = 0 := (le_signature m a r (by omega)).mp (by omega)
  have hn : a % 2 ^ (r + 1) ≠ 0 := by
    intro he
    have hb := (le_signature m a (r + 1) (by omega)).mpr he
    omega
  let y := a % 2 ^ (r + 1)
  have hy : y < 2 ^ (r + 1) := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hymod : y % 2 ^ r = 0 := by
    dsimp [y]
    rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (show r ≤ r + 1 by omega)), hz]
  have hlo : 2 ^ r ≤ y := by
    by_cases hl : y < 2 ^ r
    · rw [Nat.mod_eq_of_lt hl] at hymod
      exact False.elim (hn hymod)
    · omega
  have hsub : y - 2 ^ r < 2 ^ r := by rw [Nat.pow_succ] at hy; omega
  rw [Nat.mod_eq_sub_mod hlo, Nat.mod_eq_of_lt hsub] at hymod
  change y = 2 ^ r
  omega

/-- An actor strictly moves its own signature, including the case where its
image is the saturation cap. -/
theorem signature_lt_act (family : BinaryFamily) (m a : Nat) (ha : signature m a < m) :
    signature m a < act family m a (signature m a) := by
  let r := signature m a
  change r < act family m a r
  have hlo := le_act family m a r (Nat.le_of_lt ha)
  by_cases he : act family m a r = r
  · have hsig : signature m ((family m).mul a a) = r := by rw [signature_mul]; exact he
    have hprod : (family m).mul a a % 2 ^ (r + 1) = 2 ^ r := residue_at_signature ha hsig
    have hares : a % 2 ^ (r + 1) = 2 ^ r := residue_at_signature ha rfl
    have hh : 2 ^ r < 2 ^ (r + 1) := Nat.pow_lt_pow_succ (by decide)
    rw [(family m).projection (family (r + 1)) (Nat.pow_dvd_pow 2 (by omega)),
      ← (family (r + 1)).mul_mod_left a a,
      ← (family (r + 1)).mul_mod_right (a % 2 ^ (r + 1)) a, hares] at hprod
    have hg := (family (r + 1)).row_grows (a := 2 ^ r) (b := 2 ^ r) hh
    rcases hg with hz | hlt
    · rw [hprod] at hz
      have hp := Nat.two_pow_pos r
      omega
    · rw [hprod] at hlt
      omega
  · omega

#print axioms signature_lt_act

end LaverLowerBounds.FiniteTable
