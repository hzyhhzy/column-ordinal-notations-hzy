import LaverLowerBounds.FiniteCapped

set_option autoImplicit false

namespace LaverLowerBounds.FiniteTable

theorem mod_succ_injective {a b d : Nat} (hd : 0 < d)
    (h : (a + 1) % d = (b + 1) % d) : a % d = b % d := by
  have he := Nat.add_mod_eq_add_mod_right (d - 1) h
  have ha : a + 1 + (d - 1) = a + d := by omega
  have hb : b + 1 + (d - 1) = b + d := by omega
  simpa only [ha, hb, Nat.add_mod_right] using he

theorem comp_projection {big small : Nat} (T : FiniteTable big) (U : FiniteTable small)
    (hd : small ∣ big) (a b : Nat) : T.comp a b % small = U.comp a b := by
  have he := congrArg (fun v => v % small) (T.comp_one a b)
  rw [T.projection U hd, T.projection U hd, ← U.comp_one a b, U.mul_one, U.mul_one] at he
  have he' := mod_succ_injective U.positive he
  have hb : U.comp a b < small := Nat.mod_lt _ U.positive
  simpa only [Nat.mod_eq_of_lt hb] using he'

theorem congruent_refl (m r a : Nat) : congruent m r a a := rfl

theorem congruent_symm {m r a b : Nat} (h : congruent m r a b) : congruent m r b a := h.symm

theorem congruent_trans {m r a b c : Nat} (hab : congruent m r a b)
    (hbc : congruent m r b c) : congruent m r a c := hab.trans hbc

theorem congruent_lower {m r s a b : Nat} (hab : congruent m r a b) (hs : s ≤ r) :
    congruent m s a b := residue_agree_lower hab (by omega)

theorem congruent_mul (family : BinaryFamily) (m : Nat) {r a b c d : Nat}
    (hab : congruent m r a b) (hcd : congruent m r c d) :
    congruent m r ((family m).mul a c) ((family m).mul b d) := by
  let k := min r m
  change a % 2 ^ k = b % 2 ^ k at hab
  change c % 2 ^ k = d % 2 ^ k at hcd
  change (family m).mul a c % 2 ^ k = (family m).mul b d % 2 ^ k
  have hk : k ≤ m := Nat.min_le_right _ _
  rw [(family m).projection (family k) (Nat.pow_dvd_pow 2 hk),
    (family m).projection (family k) (Nat.pow_dvd_pow 2 hk),
    ← (family k).mul_mod_left a c, ← (family k).mul_mod_left b d,
    ← (family k).mul_mod_right (a % 2 ^ k) c,
    ← (family k).mul_mod_right (b % 2 ^ k) d, hab, hcd]

theorem congruent_comp (family : BinaryFamily) (m : Nat) {r a b c d : Nat}
    (hab : congruent m r a b) (hcd : congruent m r c d) :
    congruent m r ((family m).comp a c) ((family m).comp b d) := by
  let k := min r m
  change a % 2 ^ k = b % 2 ^ k at hab
  change c % 2 ^ k = d % 2 ^ k at hcd
  change (family m).comp a c % 2 ^ k = (family m).comp b d % 2 ^ k
  have hk : k ≤ m := Nat.min_le_right _ _
  rw [(family m).comp_projection (family k) (Nat.pow_dvd_pow 2 hk),
    (family m).comp_projection (family k) (Nat.pow_dvd_pow 2 hk),
    ← (family k).comp_mod_left a c, ← (family k).comp_mod_left b d,
    ← (family k).comp_mod_right (a % 2 ^ k) c,
    ← (family k).comp_mod_right (b % 2 ^ k) d, hab, hcd]

theorem app_critical (family : BinaryFamily) (m a b : Nat) :
    congruent m (signature m a) ((family m).mul a b) b := by
  have hr := signature_le m a
  have hz := (le_signature m a (signature m a) hr).mp (Nat.le_refl _)
  unfold congruent
  rw [Nat.min_eq_left hr, (family m).projection (family (signature m a)) (Nat.pow_dvd_pow 2 hr),
    ← (family (signature m a)).mul_mod_left a b, hz, (family (signature m a)).zero_mul]

theorem comp_critical_left (family : BinaryFamily) (m a b : Nat) :
    congruent m (signature m a) ((family m).comp a b) b := by
  have hr := signature_le m a
  have hz := (le_signature m a (signature m a) hr).mp (Nat.le_refl _)
  unfold congruent
  rw [Nat.min_eq_left hr, (family m).comp_projection (family (signature m a)) (Nat.pow_dvd_pow 2 hr),
    ← (family (signature m a)).comp_mod_left a b, hz, (family (signature m a)).zero_comp]

theorem comp_critical_right (family : BinaryFamily) (m a b : Nat) :
    congruent m (signature m b) ((family m).comp a b) a := by
  have hr := signature_le m b
  have hz := (le_signature m b (signature m b) hr).mp (Nat.le_refl _)
  unfold congruent
  rw [Nat.min_eq_left hr, (family m).comp_projection (family (signature m b)) (Nat.pow_dvd_pow 2 hr),
    ← (family (signature m b)).comp_mod_right a b, hz, (family (signature m b)).comp_zero]

/-- Saturated outputs are allowed in this cutoff statement. -/
theorem app_comp_congruent (family : BinaryFamily) (m a b : Nat) :
    congruent m (act family m ((family m).mul a b) (signature m a))
      ((family m).mul a b) ((family m).comp a b) := by
  rw [(family m).comp_swap a b, (family m).comp_swap ((family m).mul a b) a]
  have he := comp_critical_left family m ((family m).mul ((family m).mul a b) a) ((family m).mul a b)
  rw [signature_mul] at he
  exact congruent_symm he

theorem congruent_action_ge (family : BinaryFamily) (m : Nat) {r a b x : Nat}
    (hab : congruent m r a b) (ha : r ≤ act family m a x) : r ≤ act family m b x := by
  by_cases hb : act family m b x < r
  · have he := congruent_read family m (congruent_symm hab) hb
    omega
  · omega

/-- One step of the guarded flattening induction. The guard concerns the
actual intermediate left-associated word, not an assumed equal word. -/
theorem flatten_step (family : BinaryFamily) (m : Nat) {r a word tail c : Nat}
    (hprefix : congruent m r word ((family m).mul a tail))
    (hcut : r ≤ act family m word (signature m a)) :
    congruent m r ((family m).mul word c) ((family m).mul a ((family m).mul tail c)) := by
  have hcut' := congruent_action_ge family m hprefix hcut
  have hcomp := congruent_lower (app_comp_congruent family m a tail) hcut'
  have hword := congruent_trans hprefix hcomp
  have hfinal := congruent_mul family m hword (congruent_refl m r c)
  rw [(family m).comp_mul] at hfinal
  exact hfinal

#print axioms comp_projection
#print axioms app_comp_congruent
#print axioms flatten_step

end LaverLowerBounds.FiniteTable
