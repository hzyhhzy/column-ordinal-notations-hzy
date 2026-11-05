import LaverLowerBounds.FirstFanInsertion

set_option autoImplicit false

namespace LaverLowerBounds.FiniteTable

/-- Low data for one line-segment actor Q and the previous segment U (or the
identity, whose signature is m). This is OLD 6.2 with finite saturation guards. -/
structure InsertionLowData (family : BinaryFamily) (m Q U : Nat) : Prop where
  T_signature : signature m ((family m).mul Q 10) = 1
  T_one : act family m ((family m).mul Q 10) 1 = act family m Q 2
  X_signature : signature m ((family m).mul ((family m).mul Q 10) ((family m).mul U 1)) = 0
  X_zero : act family m ((family m).mul ((family m).mul Q 10) ((family m).mul U 1)) 0 = act family m Q 2
  X_one : act family m ((family m).mul ((family m).mul Q 10) ((family m).mul U 1)) 1 = act family m Q 4
  Z_signature : signature m ((family m).mul Q 3) = 0
  Z_zero : act family m ((family m).mul Q 3) 0 = act family m Q 2
  Z_one : act family m ((family m).mul Q 3) 1 = act family m Q 3
  Z_next : act family m ((family m).mul Q 3) (act family m Q 2) = act family m Q 4
  common : congruent m (act family m Q 3)
    ((family m).mul ((family m).mul Q 10) ((family m).mul U 1)) ((family m).mul Q 3)
  gap : act family m Q 2 < act family m Q 3 ∧ act family m Q 3 < act family m Q 4

theorem insertionLowData (family : BinaryFamily) (m : Nat) (hm : PeriodAtLeast32 (family m))
    (Q U : Nat) (hQ : signature m Q = 2) (hU : 2 ≤ signature m U)
    (hcap : act family m Q 4 < m) : InsertionLowData family m Q U := by
  have h9 : 9 ≤ m := Nat.le_of_lt (threshold_gt_nine family m hm)
  have hd := higherData family m hm
  have sig1 : signature m 1 = 0 := signature_from_nine m 1 0 h9 (by decide) (by decide)
  have sig3 : signature m 3 = 0 := signature_from_nine m 3 0 h9 (by decide) (by decide)
  have j0 := act_from_low family m 1 0 2 1 h9 (LowProducts.v1_1 (family 9)) (by decide) (by decide)
  have j1 := act_from_low family m 1 1 12 2 h9 (LowProducts.v1_2 (family 9)) (by decide) (by decide)
  have j30 := act_from_low family m 3 0 4 2 h9 (LowProducts.v3_1 (family 9)) (by decide) (by decide)
  have j31 := act_from_low family m 3 1 8 3 h9 (LowProducts.v3_2 (family 9)) (by decide) (by decide)
  have j32 := act_from_low family m 3 2 464 4 h9 (LowProducts.v3_4 (family 9)) (by decide) (by decide)
  obtain ⟨sig10, ten1, _⟩ := ten_low family m hm
  have n10 := mul_next_small family m 10 h9 (by decide)
  have q0 : act family m Q 0 = 0 := fixes_below_signature family m Q 0 (by omega)
  have q1 : act family m Q 1 = 1 := fixes_below_signature family m Q 1 (by omega)
  have u0 : act family m U 0 = 0 := fixes_below_signature family m U 0 (by omega)
  have u1 : act family m U 1 = 1 := fixes_below_signature family m U 1 (by omega)
  let T := (family m).mul Q 10
  let X := (family m).mul T ((family m).mul U 1)
  let Z := (family m).mul Q 3
  let KQ := (family m).mul Q 11
  let Tj := (family m).mul T 1
  have Tsig : signature m T = 1 := by dsimp [T]; rw [signature_mul, sig10, q1]
  have T0 : act family m T 0 = 0 := fixes_below_signature family m T 0 (by omega)
  have T1 : act family m T 1 = act family m Q 2 := application_at family m Q 10 q1 ten1
  have T1gt : 1 < act family m T 1 := by
    have he := signature_lt_act family m T (by omega)
    rwa [Tsig] at he
  have ukcong : congruent m 2 ((family m).mul U 1) 1 := congruent_lower (app_critical family m U 1) hU
  have cX : congruent m (act family m T 2) X Tj := congruent_transport family m ukcong T
  have cq : congruent m 2 ((family m).mul Q 1) 1 := by simpa only [hQ] using app_critical family m Q 1
  have qK_eq : (family m).mul T ((family m).mul Q 1) = KQ := by
    have he := (family m).mul_distrib Q 10 1
    rw [n10] at he
    exact he.symm
  have cK : congruent m (act family m T 2) KQ Tj := by
    have he := congruent_transport family m cq T
    rw [qK_eq] at he
    exact he
  have KQ1 : act family m KQ 1 = act family m Q 4 := application_at family m Q 11 q1 hd.k1
  have TjT1 : act family m Tj (act family m T 1) = act family m T 2 :=
    application_at family m T 1 rfl j1
  -- If T(2) saturates, first use the known nonsaturated QK(1) to read the
  -- congruence. Global strictness at the saturated endpoint is not assumed.
  have Tj1lt : act family m Tj 1 < act family m T 2 := by
    by_cases hc : act family m T 2 < m
    · have he := act_strict_below_cap family m Tj 1 (act family m T 1) T1gt
        (by rw [TjT1]; exact hc)
      rwa [TjT1] at he
    · have heq : act family m T 2 = m := Nat.le_antisymm (act_le family m T 2) (by omega)
      have hk : act family m KQ 1 < act family m T 2 := by rw [KQ1, heq]; exact hcap
      have he := congruent_read family m cK hk
      omega
  have Tj1 : act family m Tj 1 = act family m Q 4 := by
    have he := congruent_read family m (congruent_symm cK) Tj1lt
    exact he.trans KQ1
  have q3ltq4 : act family m Q 3 < act family m Q 4 := act_strict_below_cap family m Q 3 4 (by decide) hcap
  have q2ltq3 : act family m Q 2 < act family m Q 3 := act_strict_below_cap family m Q 2 3 (by decide) (by omega)
  have q3cut : act family m Q 3 ≤ act family m T 2 := by omega
  have k3 : congruent m 3 11 3 := congruent_trans
    (congruent_lower hd.square (by have := hd.mu_lower; omega))
    (congruent_symm (low_square family m h9))
  have cKZ : congruent m (act family m Q 3) KQ Z := congruent_transport family m k3 Q
  have cTjZ : congruent m (act family m Q 3) Tj Z :=
    congruent_trans (congruent_symm (congruent_lower cK q3cut)) cKZ
  have cXZ : congruent m (act family m Q 3) X Z := congruent_trans (congruent_lower cX q3cut) cTjZ
  have X1 : act family m X 1 = act family m Q 4 := by
    have he := congruent_read family m (congruent_symm cX) Tj1lt
    exact he.symm.trans Tj1
  have Usig : signature m ((family m).mul U 1) = 0 := by rw [signature_mul, sig1, u0]
  have Uj0 : act family m ((family m).mul U 1) 0 = 1 := (application_at family m U 1 u0 j0).trans u1
  have Xsig : signature m X = 0 := by dsimp [X]; rw [signature_mul, Usig, T0]
  have X0 : act family m X 0 = act family m Q 2 :=
    (application_at family m T ((family m).mul U 1) T0 Uj0).trans T1
  have Zsig : signature m Z = 0 := by dsimp [Z]; rw [signature_mul, sig3, q0]
  have Z0 : act family m Z 0 = act family m Q 2 := application_at family m Q 3 q0 j30
  have Z1 : act family m Z 1 = act family m Q 3 := application_at family m Q 3 q1 j31
  have Znext : act family m Z (act family m Q 2) = act family m Q 4 := application_at family m Q 3 rfl j32
  exact ⟨Tsig, T1, Xsig, X0, X1, Zsig, Z0, Z1, Znext, cXZ, q2ltq3, q3ltq4⟩

#print axioms insertionLowData

end LaverLowerBounds.FiniteTable
