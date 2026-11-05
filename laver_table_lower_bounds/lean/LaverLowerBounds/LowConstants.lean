import LaverLowerBounds.LowProducts

set_option autoImplicit false

namespace LaverLowerBounds.FiniteTable

open LowProducts

theorem signature_lift {r m a : Nat} (hr : r ≤ m) (hs : signature r a < r) :
    signature m a = signature r a := by
  let s := signature r a
  have hsr : s ≤ r := signature_le r a
  have hsm : s ≤ m := Nat.le_trans hsr hr
  have hz : a % 2 ^ s = 0 := (le_signature r a s hsr).mp (Nat.le_refl _)
  have hlo : s ≤ signature m a := (le_signature m a s hsm).mpr hz
  have hnot : ¬ s + 1 ≤ signature m a := by
    intro h
    have hsr' : s + 1 ≤ r := by omega
    have hz' := (le_signature m a (s + 1) (Nat.le_trans hsr' hr)).mp h
    have hbad := (le_signature r a (s + 1) hsr').mpr hz'
    omega
  omega

theorem act_from_low (family : BinaryFamily) (m a x v y : Nat) (hm : 9 ≤ m)
    (hvalue : (family 9).mul a (2 ^ x) = v)
    (hsig : signature 9 v = y) (hy : y < 9) : act family m a x = y := by
  have hv : v < 2 ^ 9 := hvalue ▸ (family 9).mul_lt a (2 ^ x)
  have hproj : (family m).mul a (2 ^ x) % 2 ^ 9 = v % 2 ^ 9 := by
    rw [(family m).projection (family 9) (Nat.pow_dvd_pow 2 hm), hvalue,
      Nat.mod_eq_of_lt hv]
  have hs9 : signature 9 ((family m).mul a (2 ^ x)) = y :=
    (signature_mod_eq hproj).trans hsig
  have hlift := signature_lift hm (show signature 9 ((family m).mul a (2 ^ x)) < 9 by omega)
  exact hlift.trans hs9

theorem threshold_gt_nine (family : BinaryFamily) (m : Nat)
    (hm : PeriodAtLeast32 (family m)) : 9 < m := by
  have hnonzero := (periodAtLeast32_iff family m).mp hm
  by_cases h : 9 < m
  · exact h
  · have hle : m ≤ 9 := by omega
    have hproj := (family 9).projection (family m) (Nat.pow_dvd_pow 2 hle) 1 16
    rw [v1_16 (family 9), Nat.zero_mod] at hproj
    exact False.elim (hnonzero hproj.symm)

theorem threshold_unsaturated (family : BinaryFamily) (m : Nat)
    (hm : PeriodAtLeast32 (family m)) : act family m 1 4 < m := by
  have hz := (periodAtLeast32_iff family m).mp hm
  have hle := act_le family m 1 4
  have hnot : ¬ m ≤ act family m 1 4 := by
    intro h
    have hbad := (le_act_iff family m 1 4 m (Nat.le_refl _)).mp h
    exact hz hbad
  omega

theorem low_square (family : BinaryFamily) (m : Nat) (hm : 9 ≤ m) :
    congruent m 3 3 ((family m).comp 1 1) := by
  let c := (family m).comp 1 1
  have hproj := (family m).projection (family 9) (Nat.pow_dvd_pow 2 hm) c 1
  have hprod : (family 9).mul c 1 = 12 := by
    rw [← hproj]
    change (family m).mul ((family m).comp 1 1) 1 % 2 ^ 9 = 12
    rw [(family m).comp_one, (family m).projection (family 9) (Nat.pow_dvd_pow 2 hm)]
    exact v1_2 (family 9)
  rw [(family 9).mul_one] at hprod
  have hpred := (family 9).predecessor_successor c
  rw [hprod] at hpred
  have hc : c % 512 = 11 := hpred.symm
  have hc' : c % 8 = 3 := by
    have he := residue_agree_lower (show c % 2 ^ 9 = 11 % 2 ^ 9 from hc) (by decide : 3 ≤ 9)
    exact he
  unfold congruent
  rw [Nat.min_eq_left (by omega : 3 ≤ m)]
  exact hc'.symm

theorem low_mu (family : BinaryFamily) (m : Nat) (hm : 9 ≤ m) :
    9 ≤ act family m 7 2 := by
  apply (le_act_iff family m 7 2 9 hm).mpr
  exact v7_4 (family 9)

theorem act_cyclic (family : BinaryFamily) (m n x : Nat) :
    (cappedAlgebra family m).act (n % 2 ^ m) x = act family m n x := by
  change signature m ((family m).mul (n % 2 ^ m) (2 ^ x)) = _
  rw [(family m).mul_mod_left]
  rfl

/-- All low data required for the first endpoint lemma are now supplied by
kernel-checked fixed products and proved projection laws. -/
theorem lowData (family : BinaryFamily) (m : Nat) (hm : 9 ≤ m) :
    (cappedAlgebra family m).LowData (fun n => n % 2 ^ m) where
  next := by
    intro n
    change (n + 1) % 2 ^ m = (family m).mul (n % 2 ^ m) (1 % 2 ^ m)
    rw [(family m).mul_mod_left, (family m).mul_mod_right, (family m).mul_one]
  j11 := (act_cyclic family m 1 1).trans
    (act_from_low family m 1 1 12 2 hm (v1_2 (family 9)) (by decide) (by decide))
  j12 := (act_cyclic family m 1 2).trans
    (act_from_low family m 1 2 240 4 hm (v1_4 (family 9)) (by decide) (by decide))
  j13 := (act_cyclic family m 1 3).trans
    (act_from_low family m 1 3 256 8 hm (v1_8 (family 9)) (by decide) (by decide))
  j22 := (act_cyclic family m 2 2).trans
    (act_from_low family m 2 2 304 4 hm (v2_4 (family 9)) (by decide) (by decide))
  j31 := (act_cyclic family m 3 1).trans
    (act_from_low family m 3 1 8 3 hm (v3_2 (family 9)) (by decide) (by decide))
  j32 := (act_cyclic family m 3 2).trans
    (act_from_low family m 3 2 464 4 hm (v3_4 (family 9)) (by decide) (by decide))
  j42 := (act_cyclic family m 4 2).trans
    (act_from_low family m 4 2 8 3 hm (v4_4 (family 9)) (by decide) (by decide))
  j51 := (act_cyclic family m 5 1).trans
    (act_from_low family m 5 1 504 3 hm (v5_2 (family 9)) (by decide) (by decide))
  j61 := (act_cyclic family m 6 1).trans
    (act_from_low family m 6 1 504 3 hm (v6_2 (family 9)) (by decide) (by decide))
  j71 := (act_cyclic family m 7 1).trans
    (act_from_low family m 7 1 496 4 hm (v7_2 (family 9)) (by decide) (by decide))
  j83 := (act_cyclic family m 8 3).trans
    (act_from_low family m 8 3 496 4 hm (v8_8 (family 9)) (by decide) (by decide))
  square := by
    change congruent m 3 (3 % 2 ^ m) ((family m).comp (1 % 2 ^ m) (1 % 2 ^ m))
    rw [(family m).comp_mod_left, (family m).comp_mod_right]
    unfold congruent
    rw [Nat.min_eq_left (by omega : 3 ≤ m),
      Nat.mod_mod_of_dvd 3 (Nat.pow_dvd_pow 2 (show 3 ≤ m by omega))]
    simpa only [congruent, Nat.min_eq_left (show 3 ≤ m by omega)] using low_square family m hm
  mu_lower := by
    rw [act_cyclic]
    exact low_mu family m hm

/-- A concrete theorem about ordinary finite tables. The only table assumptions
are the defining LD/successor equations and the first-row period threshold. -/
theorem first_endpoint (family : BinaryFamily) (m : Nat)
    (hm : PeriodAtLeast32 (family m)) : act family m 9 4 < act family m 1 4 := by
  have h9 : 9 ≤ m := Nat.le_of_lt (threshold_gt_nine family m hm)
  have hs : (cappedAlgebra family m).act (1 % 2 ^ m) 4 < m := by
    rw [act_cyclic]
    exact threshold_unsaturated family m hm
  have he := (cappedAlgebra family m).j9_four_below (fun n => n % 2 ^ m)
    (lowData family m h9) hs
  simpa only [act_cyclic] using he

/-- Minimality of the period-32 threshold identifies the upper critical index. -/
theorem q5_upper_index (family : BinaryFamily) (m : Nat) (hm : Q5At family m) :
    act family m 1 4 = m - 1 := by
  have hbig := threshold_gt_nine family m hm.1
  have hlt := threshold_unsaturated family m hm.1
  have hprev : ¬ PeriodAtLeast32 (family (m - 1)) := hm.2 (m - 1) (by omega)
  have hzero : (family (m - 1)).mul 1 16 = 0 := by
    by_cases hz : (family (m - 1)).mul 1 16 = 0
    · exact hz
    · exact False.elim (hprev ((periodAtLeast32_iff family (m - 1)).mpr hz))
  have hlo : m - 1 ≤ act family m 1 4 :=
    (le_act_iff family m 1 4 (m - 1) (by omega)).mpr hzero
  omega

#print axioms threshold_gt_nine
#print axioms lowData
#print axioms first_endpoint
#print axioms q5_upper_index

end LaverLowerBounds.FiniteTable
