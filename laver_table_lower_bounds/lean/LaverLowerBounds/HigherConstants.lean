import LaverLowerBounds.ShortInitialization
import LaverLowerBounds.FiniteCongruence

set_option autoImplicit false

namespace LaverLowerBounds.FiniteTable

theorem mul_next_small (family : BinaryFamily) (m n : Nat) (hm : 9 ≤ m) (hn : n < 12) :
    (family m).mul n 1 = n + 1 := by
  have hpow : 512 ≤ 2 ^ m := Nat.pow_le_pow_right (n := 2) (by decide) hm
  rw [(family m).mul_one, Nat.mod_eq_of_lt (by omega)]

/-- The finite high-point data needed for the explicit fan and feedback terms.
Every field is proved below from the ordinary finite table and threshold 32. -/
structure HigherData (family : BinaryFamily) (m : Nat) : Prop where
  square : congruent m (act family m 7 2) 11 ((family m).comp 1 1)
  mu_lower : 9 ≤ act family m 7 2
  k0 : act family m 11 0 = 2
  k1 : act family m 11 1 = 4
  k2 : act family m 11 2 = act family m 7 2
  k_mu : act family m 11 (act family m 7 2) = act family m 10 4
  mu_lt_five : act family m 7 2 < act family m 11 4
  five_lt_six : act family m 11 4 < act family m 10 4
  six_lt_seven : act family m 10 4 < act family m 11 (act family m 11 4)
  seven_lt_eight : act family m 11 (act family m 11 4) < act family m 9 4
  eight_lt_upper : act family m 9 4 < act family m 1 4
  upper_below : act family m 1 4 < m

theorem higherData (family : BinaryFamily) (m : Nat) (hm : PeriodAtLeast32 (family m)) :
    HigherData family m := by
  have h9 : 9 ≤ m := Nat.le_of_lt (threshold_gt_nine family m hm)
  have next := mul_next_small family m
  have n1 := next 1 h9 (by decide)
  have n2 := next 2 h9 (by decide)
  have n3 := next 3 h9 (by decide)
  have n4 := next 4 h9 (by decide)
  have n5 := next 5 h9 (by decide)
  have n6 := next 6 h9 (by decide)
  have n7 := next 7 h9 (by decide)
  have n8 := next 8 h9 (by decide)
  have n9 := next 9 h9 (by decide)
  have n10 := next 10 h9 (by decide)
  have p11 := act_from_low family m 1 1 12 2 h9 (LowProducts.v1_2 (family 9)) (by decide) (by decide)
  have p12 := act_from_low family m 1 2 240 4 h9 (LowProducts.v1_4 (family 9)) (by decide) (by decide)
  have p22 := act_from_low family m 2 2 304 4 h9 (LowProducts.v2_4 (family 9)) (by decide) (by decide)
  have p31 := act_from_low family m 3 1 8 3 h9 (LowProducts.v3_2 (family 9)) (by decide) (by decide)
  have p32 := act_from_low family m 3 2 464 4 h9 (LowProducts.v3_4 (family 9)) (by decide) (by decide)
  have p42 := act_from_low family m 4 2 8 3 h9 (LowProducts.v4_4 (family 9)) (by decide) (by decide)
  have p51 := act_from_low family m 5 1 504 3 h9 (LowProducts.v5_2 (family 9)) (by decide) (by decide)
  have p61 := act_from_low family m 6 1 504 3 h9 (LowProducts.v6_2 (family 9)) (by decide) (by decide)
  have p71 := act_from_low family m 7 1 496 4 h9 (LowProducts.v7_2 (family 9)) (by decide) (by decide)
  have p82 := act_from_low family m 8 2 12 2 h9 (LowProducts.v8_4 (family 9)) (by decide) (by decide)
  have p91 := act_from_low family m 9 1 508 2 h9 (LowProducts.v9_2 (family 9)) (by decide) (by decide)
  have p101 := act_from_low family m 10 1 508 2 h9 (LowProducts.v10_2 (family 9)) (by decide) (by decide)
  have k0 := act_from_low family m 11 0 12 2 h9 (LowProducts.v11_1 (family 9)) (by decide) (by decide)
  have k1 := act_from_low family m 11 1 496 4 h9 (LowProducts.v11_2 (family 9)) (by decide) (by decide)
  have sig2 : signature m 2 = 1 := signature_from_nine m 2 1 h9 (by decide) (by decide)
  have sig4 : signature m 4 = 2 := signature_from_nine m 4 2 h9 (by decide) (by decide)
  have sig8 : signature m 8 = 3 := signature_from_nine m 8 3 h9 (by decide) (by decide)
  let mu := act family m 7 2
  have hmu : 9 ≤ mu := low_mu family m h9
  have hs : act family m 1 4 < m := threshold_unsaturated family m hm
  have h94 : act family m 9 4 < act family m 1 4 := first_endpoint family m hm
  have p24 : act family m 2 4 = act family m 1 4 := by
    simpa only [p12] using next_small family m 1 2 h9 (by decide)
  have p34 : act family m 3 4 = act family m 1 4 := by
    simpa only [p22, p12, p24] using next_small family m 2 2 h9 (by decide)
  have p44 : act family m 4 4 = act family m 1 4 := by
    simpa only [p32, p12, p34] using next_small family m 3 2 h9 (by decide)
  have p53 : act family m 5 3 = act family m 1 4 := by
    simpa only [p42, p12, p44] using next_small family m 4 2 h9 (by decide)
  have p63 : act family m 6 3 = act family m 5 2 := by
    simpa only [p51, p11] using next_small family m 5 1 h9 (by decide)
  have h52 : act family m 5 2 < act family m 1 4 := by
    have he := act_strict_below_cap family m 5 2 3 (by decide) (by omega)
    omega
  have h77 : act family m 7 mu < act family m 5 2 := by
    have he := guarded_double family m 6 2 (low_square family m h9) p31 (by omega)
      (by rw [p61]; decide)
    rw [n6, p63] at he
    exact he
  have hmu_cap : mu ≤ m := act_le family m 7 2
  have hmu52 : mu ≤ act family m 5 2 := by
    have he := le_act family m 7 mu hmu_cap
    omega
  have p62 : act family m 6 2 = act family m 7 3 := by
    symm
    simpa only [p61, p11] using next_small family m 6 1 h9 (by decide)
  have hmu62 : mu ≤ act family m 6 2 := by
    rw [p62]
    exact act_mono family m 7 (by decide : 2 ≤ 3)
  have p84 : act family m 8 4 = mu := by
    simpa only [p71, p11] using next_small family m 7 1 h9 (by decide)
  have p92 : act family m 9 2 = mu := by
    simpa only [p82, p12, p84] using next_small family m 8 2 h9 (by decide)
  have p102 : act family m 10 2 = mu := by
    simpa only [p91, p11, p92] using next_small family m 9 1 h9 (by decide)
  have k2 : act family m 11 2 = mu := by
    simpa only [p101, p11, p102] using next_small family m 10 1 h9 (by decide)
  have p10mu : act family m 10 mu = act family m 9 4 := by
    simpa only [p92, p12] using next_small family m 9 2 h9 (by decide)
  have kmu : act family m 11 mu = act family m 10 4 := by
    simpa only [p102, p12] using next_small family m 10 2 h9 (by decide)
  have p124 : act family m 12 4 = mu := by
    simpa only [k1, p11, k2] using next_small family m 11 1 h9 (by decide)
  have p12mu : act family m 12 mu = act family m 11 4 := by
    simpa only [k2, p12] using next_small family m 11 2 h9 (by decide)
  have h104 : act family m 10 4 < act family m 9 4 := by
    have he := act_strict_below_cap family m 10 4 mu (by omega) (by omega)
    omega
  have hk4 : act family m 11 4 < act family m 10 4 := by
    have he := act_strict_below_cap family m 11 4 mu (by omega) (by omega)
    omega
  have hmu_k4 : mu < act family m 11 4 := by
    have he := act_strict_below_cap family m 12 4 mu (by omega) (by omega)
    omega
  have c10 : congruent m mu 10 ((family m).mul 8 2) := by
    have he := flatten_step family m (r := mu) (a := 8) (word := 9) (tail := 1) (c := 1)
      (by rw [n8]; rfl) (by rw [sig8]; have := act_mono family m 9 (show 2 ≤ 3 by decide); omega)
    simpa only [n9, n1] using he
  have c11 : congruent m mu 11 ((family m).mul 8 3) := by
    have he := flatten_step family m (c := 1) c10
      (by rw [sig8]; have := act_mono family m 10 (show 2 ≤ 3 by decide); omega)
    simpa only [n10, n2] using he
  have c6 : congruent m mu 6 ((family m).mul 4 2) := by
    have he := flatten_step family m (r := mu) (a := 4) (word := 5) (tail := 1) (c := 1)
      (by rw [n4]; rfl) (by simpa only [sig4] using hmu52)
    simpa only [n5, n1] using he
  have c7 : congruent m mu 7 ((family m).mul 4 3) := by
    have he := flatten_step family m (c := 1) c6 (by simpa only [sig4] using hmu62)
    simpa only [n6, n2] using he
  have c8 : congruent m mu 8 ((family m).mul 4 4) := by
    have he := flatten_step family m (c := 1) c7 (by rw [sig4]; exact Nat.le_refl _)
    simpa only [n7, n3] using he
  have ueq : (family m).mul 4 4 = (family m).mul 3 2 := by
    have he := (family m).mul_distrib 3 1 1
    rw [n1, n3] at he
    exact he.symm
  rw [ueq] at c8
  let U := (family m).mul 3 2
  let V := (family m).mul U 3
  have cv : congruent m mu 11 V :=
    congruent_trans c11 (congruent_mul family m c8 (congruent_refl m mu 3))
  have sigU : signature m U = 3 := by dsimp [U]; rw [signature_mul, sig2, p31]
  have u2 : act family m U 2 = 2 := fixes_below_signature family m U 2 (by rw [sigU]; decide)
  have u4 : act family m U 4 = act family m 1 4 := by
    have he := act_application family m 3 2 2
    simpa only [p32, p22, p34] using he
  have v2 : act family m V 2 = act family m 1 4 := by
    have he := act_application family m U 3 2
    simpa only [u2, p32, u4] using he
  have hvcut : mu ≤ act family m V (signature m U) := by
    rw [sigU]
    have he := act_mono family m V (show 2 ≤ 3 by decide)
    omega
  have cc := congruent_lower (app_comp_congruent family m U 3) hvcut
  have e1 : (family m).comp U 3 = (family m).comp 3 2 := ((family m).comp_swap 3 2).symm
  have e2 : (family m).comp 3 2 = (family m).comp 2 1 := by
    simpa only [n2] using ((family m).comp_swap 2 1).symm
  have e3 : (family m).comp 2 1 = (family m).comp 1 1 := by
    simpa only [n1] using ((family m).comp_swap 1 1).symm
  rw [e1, e2, e3] at cc
  have ksquare : congruent m mu 11 ((family m).comp 1 1) := congruent_trans cv cc
  let Q := (family m).mul 10 11
  have cq := congruent_transport family m ksquare 10
  rw [(family m).mul_comp, n10, p10mu] at cq
  have qmu : act family m Q mu = act family m 9 4 := by
    have he := act_application family m 10 11 2
    simpa only [p102, k2, p10mu] using he
  have q2 : act family m Q 2 = act family m 10 4 := by
    have he := act_application family m 10 11 1
    simpa only [p101, k1] using he
  have q4lt : act family m Q 4 < act family m 9 4 := by
    have he := act_strict_below_cap family m Q 4 mu (by omega) (by omega)
    omega
  have q2lt : act family m 10 4 < act family m Q 4 := by
    have he := act_strict_below_cap family m Q 2 4 (by decide) (by omega)
    omega
  have q4eq : act family m Q 4 = act family m 11 (act family m 11 4) := by
    have he := congruent_read family m cq q4lt
    rw [act_composition] at he
    exact he
  exact ⟨ksquare, hmu, k0, k1, k2, kmu, hmu_k4, hk4, by omega, by omega, h94, hs⟩

#print axioms higherData

end LaverLowerBounds.FiniteTable
