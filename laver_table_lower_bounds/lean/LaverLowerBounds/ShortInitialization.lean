import LaverLowerBounds.LowConstants
import LaverLowerBounds.FiniteLines

/-!
An explicit 16-segment initialization, avoiding the BLP evaluation theorem.
The smaller input constant is sufficient for the unchanged Lambda+omega+1
level; the later fan insertion theorem still has to be formalized.
-/

set_option autoImplicit false

namespace LaverLowerBounds.FiniteTable

theorem signature_from_nine (m a y : Nat) (hm : 9 ≤ m)
    (h : signature 9 a = y) (hy : y < 9) : signature m a = y := by
  exact (signature_lift hm (show signature 9 a < 9 by omega)).trans h

theorem next_small (family : BinaryFamily) (m n x : Nat) (hm : 9 ≤ m) (hn : n < 12) :
    act family m (n + 1) (act family m n x) =
      act family m n (act family m 1 x) := by
  have hpow : 512 ≤ 2 ^ m := Nat.pow_le_pow_right (n := 2) (by decide) hm
  have he : (family m).mul n 1 = n + 1 := by
    rw [(family m).mul_one, Nat.mod_eq_of_lt (by omega : n + 1 < 2 ^ m)]
  rw [← he]
  exact act_application family m n 1 x

theorem k_four_unsaturated (family : BinaryFamily) (m : Nat)
    (hm : PeriodAtLeast32 (family m)) : act family m 11 4 < m := by
  have h9 : 9 ≤ m := Nat.le_of_lt (threshold_gt_nine family m hm)
  have p11 := act_from_low family m 1 1 12 2 h9 (LowProducts.v1_2 (family 9)) (by decide) (by decide)
  have p12 := act_from_low family m 1 2 240 4 h9 (LowProducts.v1_4 (family 9)) (by decide) (by decide)
  have p71 := act_from_low family m 7 1 496 4 h9 (LowProducts.v7_2 (family 9)) (by decide) (by decide)
  have p82 := act_from_low family m 8 2 12 2 h9 (LowProducts.v8_4 (family 9)) (by decide) (by decide)
  have p91 := act_from_low family m 9 1 508 2 h9 (LowProducts.v9_2 (family 9)) (by decide) (by decide)
  have p101 := act_from_low family m 10 1 508 2 h9 (LowProducts.v10_2 (family 9)) (by decide) (by decide)
  let mu := act family m 7 2
  have hmu : 9 ≤ mu := low_mu family m h9
  have p84 : act family m 8 4 = mu := by
    simpa only [p71, p11] using next_small family m 7 1 h9 (by decide)
  have p92 : act family m 9 2 = mu := by
    simpa only [p82, p12, p84] using next_small family m 8 2 h9 (by decide)
  have p102 : act family m 10 2 = mu := by
    simpa only [p91, p11, p92] using next_small family m 9 1 h9 (by decide)
  have p10mu : act family m 10 mu = act family m 9 4 := by
    simpa only [p92, p12] using next_small family m 9 2 h9 (by decide)
  have p11mu : act family m 11 mu = act family m 10 4 := by
    simpa only [p102, p12] using next_small family m 10 2 h9 (by decide)
  have h94 : act family m 9 4 < m :=
    Nat.lt_trans (first_endpoint family m hm) (threshold_unsaturated family m hm)
  have h104 : act family m 10 4 < m := by
    have h := act_strict_below_cap family m 10 4 mu (by omega) (by omega)
    omega
  have h114 := act_strict_below_cap family m 11 4 mu (by omega) (by omega)
  omega

/-- A 16-line (0;1;K(4)), with K=j_11, entirely inside the finite cap. -/
theorem short_initial_line (family : BinaryFamily) (m : Nat)
    (hm : PeriodAtLeast32 (family m)) : Lined family m 0 16 1 (act family m 11 4) := by
  have h9 : 9 ≤ m := Nat.le_of_lt (threshold_gt_nine family m hm)
  have sig1 : signature m 1 = 0 := signature_from_nine m 1 0 h9 (by decide) (by decide)
  have sig2 : signature m 2 = 1 := signature_from_nine m 2 1 h9 (by decide) (by decide)
  have sig3 : signature m 3 = 0 := signature_from_nine m 3 0 h9 (by decide) (by decide)
  have p10 := act_from_low family m 1 0 2 1 h9 (LowProducts.v1_1 (family 9)) (by decide) (by decide)
  have p11 := act_from_low family m 1 1 12 2 h9 (LowProducts.v1_2 (family 9)) (by decide) (by decide)
  have p30 := act_from_low family m 3 0 4 2 h9 (LowProducts.v3_1 (family 9)) (by decide) (by decide)
  have p32 := act_from_low family m 3 2 464 4 h9 (LowProducts.v3_4 (family 9)) (by decide) (by decide)
  have p21 := act_from_low family m 2 1 12 2 h9 (LowProducts.v2_2 (family 9)) (by decide) (by decide)
  have p22 := act_from_low family m 2 2 304 4 h9 (LowProducts.v2_4 (family 9)) (by decide) (by decide)
  have k0 := act_from_low family m 11 0 12 2 h9 (LowProducts.v11_1 (family 9)) (by decide) (by decide)
  have k1 := act_from_low family m 11 1 496 4 h9 (LowProducts.v11_2 (family 9)) (by decide) (by decide)
  have one : Lined family m 0 1 1 2 :=
    .cons 1 sig1 p10 p11 (by decide) (.nil (by omega))
  have two : Lined family m 0 2 1 4 :=
    .cons 1 sig1 p10 p11 (by decide)
      (.cons 3 sig3 p30 p32 (by decide) (.nil (by omega)))
  have middle : Lined family m 1 1 2 4 :=
    .cons 2 sig2 p21 p22 (by decide) (.nil (by omega))
  have high := two.map 11 (k_four_unsaturated family m hm)
  rw [k0, k1] at high
  have four := middle.multiply high (by decide : 1 < 2)
  have sixteen := one.multiply four (by decide : 0 < 1)
  exact sixteen

#print axioms k_four_unsaturated
#print axioms short_initial_line

end LaverLowerBounds.FiniteTable
