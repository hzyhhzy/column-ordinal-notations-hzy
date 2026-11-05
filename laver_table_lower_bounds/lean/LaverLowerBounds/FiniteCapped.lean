import LaverLowerBounds.Signature
import LaverLowerBounds.CappedAlgebra

set_option autoImplicit false

namespace LaverLowerBounds.FiniteTable

theorem residue_agree_lower {a b r s : Nat} (h : a % 2 ^ r = b % 2 ^ r) (hs : s ≤ r) :
    a % 2 ^ s = b % 2 ^ s := by
  have he := congrArg (fun x => x % 2 ^ s) h
  simpa only [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hs)] using he

theorem signature_agree_below {m a b r : Nat} (hr : r ≤ m)
    (h : a % 2 ^ r = b % 2 ^ r) (ha : signature m a < r) :
    signature m a = signature m b := by
  let s := signature m a
  have hs : s ≤ m := signature_le m a
  have hs' : s + 1 ≤ m := by omega
  have hzero : a % 2 ^ s = 0 := (le_signature m a s hs).mp (Nat.le_refl _)
  have he := residue_agree_lower h (show s ≤ r by omega)
  have hbs : s ≤ signature m b := (le_signature m b s hs).mpr (he ▸ hzero)
  have hnot : ¬ s + 1 ≤ signature m b := by
    intro hmore
    have hbzero := (le_signature m b (s + 1) hs').mp hmore
    have he' := residue_agree_lower h (show s + 1 ≤ r by omega)
    have hazero : a % 2 ^ (s + 1) = 0 := he'.trans hbzero
    have hbad := (le_signature m a (s + 1) hs').mpr hazero
    omega
  omega

def congruent (m r a b : Nat) : Prop := a % 2 ^ min r m = b % 2 ^ min r m

theorem congruent_transport (family : BinaryFamily) (m : Nat) {r a b : Nat}
    (h : congruent m r a b) (e : Nat) :
    congruent m (act family m e r) ((family m).mul e a) ((family m).mul e b) := by
  by_cases hr : r ≤ m
  · have hab : a % 2 ^ r = b % 2 ^ r := by simpa only [congruent, Nat.min_eq_left hr] using h
    let k := act family m e r
    have hk : k ≤ m := act_le family m e r
    have hz : (family k).mul e (2 ^ r) = 0 :=
      (le_act_iff family m e r k hk).mp (Nat.le_refl _)
    obtain ⟨p, hp⟩ := (family k).exists_firstZero e
    have hd : p ∣ 2 ^ r := Nat.dvd_of_mod_eq_zero (((family k).firstZero_iff_mod hp _).mp hz)
    have he := congrArg (fun x => x % p) hab
    simp only [Nat.mod_mod_of_dvd _ hd] at he
    change (family m).mul e a % 2 ^ min k m = (family m).mul e b % 2 ^ min k m
    rw [Nat.min_eq_left hk, (family m).projection (family k) (Nat.pow_dvd_pow 2 hk),
      (family m).projection (family k) (Nat.pow_dvd_pow 2 hk),
      (family k).reduce_period hp.2.1 a, (family k).reduce_period hp.2.1 b, he]
  · have hab : a % 2 ^ m = b % 2 ^ m := by
      simpa only [congruent, Nat.min_eq_right (by omega : m ≤ r)] using h
    have he : (family m).mul e a = (family m).mul e b := by
      rw [← (family m).mul_mod_right e a, ← (family m).mul_mod_right e b, hab]
    unfold congruent
    rw [he]

theorem congruent_read (family : BinaryFamily) (m : Nat) {r a b x : Nat}
    (h : congruent m r a b) (ha : act family m a x < r) :
    act family m a x = act family m b x := by
  by_cases hr : r ≤ m
  · have hab : a % 2 ^ r = b % 2 ^ r := by simpa only [congruent, Nat.min_eq_left hr] using h
    have he : (family m).mul a (2 ^ x) % 2 ^ r = (family m).mul b (2 ^ x) % 2 ^ r := by
      rw [(family m).projection (family r) (Nat.pow_dvd_pow 2 hr),
        (family m).projection (family r) (Nat.pow_dvd_pow 2 hr),
        ← (family r).mul_mod_left a, ← (family r).mul_mod_left b, hab]
    exact signature_agree_below hr he ha
  · have hab : a % 2 ^ m = b % 2 ^ m := by
      simpa only [congruent, Nat.min_eq_right (by omega : m ≤ r)] using h
    have he : (family m).mul a (2 ^ x) = (family m).mul b (2 ^ x) := by
      rw [← (family m).mul_mod_left a, ← (family m).mul_mod_left b, hab]
    unfold act
    rw [he]

/-- The previously abstract capped algebra is now constructed from the two
defining equations of finite Laver tables. No large-cardinal assumption occurs.
The family supplies the smaller finite tables, not unbounded row periods. -/
def cappedAlgebra (family : BinaryFamily) (m : Nat) : CappedAlgebra Nat where
  cap := m
  app := (family m).mul
  comp := (family m).comp
  act := act family m
  act_le := act_le family m
  le_act := le_act family m
  strict_below_cap := act_strict_below_cap family m
  act_app := act_application family m
  act_comp := act_composition family m
  app_comp := (family m).mul_comp
  congruent := congruent m
  transport := congruent_transport family m
  read_below := congruent_read family m

/-- Concrete finite-table version of the guarded double-action lemma. -/
theorem guarded_double (family : BinaryFamily) (m e β : Nat)
    (hsquare : congruent m 3 3 ((family m).comp 1 1))
    (hsmall : act family m 3 1 = 3) (he : act family m e 3 < m)
    (hβ : β < act family m e 1) :
    act family m ((family m).mul e 1) (act family m ((family m).mul e 1) β) <
      act family m e 3 :=
  (cappedAlgebra family m).guarded_double_action 1 3 e hsquare hsmall he hβ

#print axioms cappedAlgebra
#print axioms guarded_double

end LaverLowerBounds.FiniteTable
