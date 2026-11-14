import LaverLowerBounds.HigherConstants

set_option autoImplicit false
namespace LaverLowerBounds.FiniteTable.K11

/-- Only the low profiles actually used in the k11 construction. No
unsaturated value for row 1, or any endpoint above k11, is required. -/
structure LocalData (family : BinaryFamily) (m : Nat) : Prop where
  mu_lower : 9 ≤ act family m 7 2
  k0 : act family m 11 0 = 2
  k1 : act family m 11 1 = 4
  k2 : act family m 11 2 = act family m 7 2
  mu_lt_five : act family m 7 2 < act family m 11 4

theorem localData (family : BinaryFamily) (m : Nat) (h9 : 9 ≤ m)
    (ht : act family m 11 4 < m) : LocalData family m := by
  have p11 := act_from_low family m 1 1 12 2 h9 (LowProducts.v1_2 (family 9)) (by decide) (by decide)
  have p12 := act_from_low family m 1 2 240 4 h9 (LowProducts.v1_4 (family 9)) (by decide) (by decide)
  have p71 := act_from_low family m 7 1 496 4 h9 (LowProducts.v7_2 (family 9)) (by decide) (by decide)
  have p82 := act_from_low family m 8 2 12 2 h9 (LowProducts.v8_4 (family 9)) (by decide) (by decide)
  have p91 := act_from_low family m 9 1 508 2 h9 (LowProducts.v9_2 (family 9)) (by decide) (by decide)
  have p101 := act_from_low family m 10 1 508 2 h9 (LowProducts.v10_2 (family 9)) (by decide) (by decide)
  have k0 := act_from_low family m 11 0 12 2 h9 (LowProducts.v11_1 (family 9)) (by decide) (by decide)
  have k1 := act_from_low family m 11 1 496 4 h9 (LowProducts.v11_2 (family 9)) (by decide) (by decide)
  have p84 : act family m 8 4 = act family m 7 2 := by
    simpa only [p71, p11] using next_small family m 7 1 h9 (by decide)
  have p92 : act family m 9 2 = act family m 7 2 := by
    simpa only [p82, p12, p84] using next_small family m 8 2 h9 (by decide)
  have p102 : act family m 10 2 = act family m 7 2 := by
    simpa only [p91, p11, p92] using next_small family m 9 1 h9 (by decide)
  have k2 : act family m 11 2 = act family m 7 2 := by
    simpa only [p101, p11, p102] using next_small family m 10 1 h9 (by decide)
  have lower := act_strict_below_cap family m 11 2 4 (by decide) ht
  rw [k2] at lower
  exact ⟨low_mu family m h9, k0, k1, k2, lower⟩

#print axioms localData
end LaverLowerBounds.FiniteTable.K11
