import LaverLowerBounds.InsertionBackground

set_option autoImplicit false

namespace LaverLowerBounds.FiniteTable.InsertionBackground

variable {family : BinaryFamily} {m : Nat}

structure LowData (bg : InsertionBackground family m) (Q U : Nat) : Prop where
  T_signature : signature m ((family m).mul Q bg.j10) = 1
  T_one : act family m ((family m).mul Q bg.j10) 1 = act family m Q bg.k
  X_zero : act family m ((family m).mul ((family m).mul Q bg.j10) ((family m).mul U bg.j)) 0 = act family m Q bg.k
  X_one : act family m ((family m).mul ((family m).mul Q bg.j10) ((family m).mul U bg.j)) 1 = act family m Q bg.r
  Z_signature : signature m ((family m).mul Q bg.j3) = 0
  Z_zero : act family m ((family m).mul Q bg.j3) 0 = act family m Q bg.k
  Z_one : act family m ((family m).mul Q bg.j3) 1 = act family m Q bg.sigma
  Z_next : act family m ((family m).mul Q bg.j3) (act family m Q bg.k) = act family m Q bg.r
  common : congruent m (act family m Q bg.sigma)
    ((family m).mul ((family m).mul Q bg.j10) ((family m).mul U bg.j)) ((family m).mul Q bg.j3)
  gap : act family m Q bg.k < act family m Q bg.sigma ∧ act family m Q bg.sigma < act family m Q bg.r

theorem lowData (bg : InsertionBackground family m) (Q U : Nat)
    (hQ : signature m Q = bg.k) (hU : bg.k ≤ signature m U)
    (hcap : act family m Q bg.r < m) : LowData bg Q U := by
  have hk := bg.k_lower
  have hkc : bg.k < m := by
    have := bg.k_sigma; have := bg.sigma_r; have := bg.r_mu
    have := bg.mu_a; have := bg.a_c; have := bg.c_cap
    omega
  have q0 : act family m Q 0 = 0 := fixes_below_signature family m Q 0 (by omega)
  have q1 : act family m Q 1 = 1 := fixes_below_signature family m Q 1 (by omega)
  have u0 : act family m U 0 = 0 := fixes_below_signature family m U 0 (by omega)
  have u1 : act family m U 1 = 1 := fixes_below_signature family m U 1 (by omega)
  let T := (family m).mul Q bg.j10
  let X := (family m).mul T ((family m).mul U bg.j)
  let Z := (family m).mul Q bg.j3
  let KQ := (family m).mul Q bg.K
  let Tj := (family m).mul T bg.j
  have Tsig : signature m T = 1 := by dsimp [T]; rw [signature_mul, bg.j10_signature, q1]
  have T0 : act family m T 0 = 0 := fixes_below_signature family m T 0 (by omega)
  have T1 : act family m T 1 = act family m Q bg.k := application_at family m Q bg.j10 q1 bg.j10_one
  have T1gt : 1 < act family m T 1 := by
    have he := signature_lt_act family m T (by omega)
    rwa [Tsig] at he
  have ukcong : congruent m bg.k ((family m).mul U bg.j) bg.j := congruent_lower (app_critical family m U bg.j) hU
  have cX : congruent m (act family m T bg.k) X Tj := congruent_transport family m ukcong T
  have cq : congruent m bg.k ((family m).mul Q bg.j) bg.j := by simpa only [hQ] using app_critical family m Q bg.j
  have qK_eq : (family m).mul T ((family m).mul Q bg.j) = KQ := by
    have he := (family m).mul_distrib Q bg.j10 bg.j
    rw [bg.j10_j] at he
    exact he.symm
  have cK : congruent m (act family m T bg.k) KQ Tj := by
    have he := congruent_transport family m cq T
    rw [qK_eq] at he
    exact he
  have KQ1 : act family m KQ 1 = act family m Q bg.r := application_at family m Q bg.K q1 bg.K_one
  have TjT1 : act family m Tj (act family m T 1) = act family m T bg.k :=
    application_at family m T bg.j rfl bg.j_one
  have Tj1lt : act family m Tj 1 < act family m T bg.k := by
    by_cases hc : act family m T bg.k < m
    · have he := act_strict_below_cap family m Tj 1 (act family m T 1) T1gt
        (by rw [TjT1]; exact hc)
      rwa [TjT1] at he
    · have heq : act family m T bg.k = m := Nat.le_antisymm (act_le family m T bg.k) (by omega)
      have hk : act family m KQ 1 < act family m T bg.k := by rw [KQ1, heq]; exact hcap
      have he := congruent_read family m cK hk
      omega
  have Tj1 : act family m Tj 1 = act family m Q bg.r := by
    have he := congruent_read family m (congruent_symm cK) Tj1lt
    exact he.trans KQ1
  have qr : act family m Q bg.sigma < act family m Q bg.r :=
    act_strict_below_cap family m Q _ _ bg.sigma_r hcap
  have qk : act family m Q bg.k < act family m Q bg.sigma :=
    act_strict_below_cap family m Q _ _ bg.k_sigma (Nat.lt_trans qr hcap)
  have qcut : act family m Q bg.sigma ≤ act family m T bg.k := by omega
  have cKZ : congruent m (act family m Q bg.sigma) KQ Z := congruent_transport family m bg.K_j3 Q
  have cTjZ : congruent m (act family m Q bg.sigma) Tj Z :=
    congruent_trans (congruent_symm (congruent_lower cK qcut)) cKZ
  have cXZ : congruent m (act family m Q bg.sigma) X Z := congruent_trans (congruent_lower cX qcut) cTjZ
  have X1 : act family m X 1 = act family m Q bg.r := by
    have he := congruent_read family m (congruent_symm cX) Tj1lt
    exact he.symm.trans Tj1
  have Uj0 : act family m ((family m).mul U bg.j) 0 = 1 :=
    (application_at family m U bg.j u0 bg.j_zero).trans u1
  have X0 : act family m X 0 = act family m Q bg.k :=
    (application_at family m T ((family m).mul U bg.j) T0 Uj0).trans T1
  have Zsig : signature m Z = 0 := by dsimp [Z]; rw [signature_mul, bg.j3_signature, q0]
  have Z0 : act family m Z 0 = act family m Q bg.k := application_at family m Q bg.j3 q0 bg.j3_zero
  have Z1 : act family m Z 1 = act family m Q bg.sigma := application_at family m Q bg.j3 q1 bg.j3_one
  have Znext : act family m Z (act family m Q bg.k) = act family m Q bg.r := application_at family m Q bg.j3 rfl bg.j3_next
  exact ⟨Tsig, T1, X0, X1, Zsig, Z0, Z1, Znext, cXZ, qk, qr⟩

theorem segment_actor (bg : InsertionBackground family m) {Q a b C : Nat}
    (hsig : signature m Q = bg.k) (ha : act family m Q bg.k = a)
    (hb : act family m Q a = b) (hstart : bg.a ≤ a) (hC : C < a) (hcap : b < m) :
    signature m ((family m).mul Q bg.j10) = 1 ∧ act family m ((family m).mul Q bg.j10) C < b := by
  have hk := bg.k_lower
  have q1 : act family m Q 1 = 1 := fixes_below_signature family m Q 1 (by omega)
  have tsig : signature m ((family m).mul Q bg.j10) = 1 := by rw [signature_mul, bg.j10_signature, q1]
  have ta : act family m ((family m).mul Q bg.j10) a = act family m Q bg.mu :=
    application_at family m Q bg.j10 ha bg.j10_next
  have hab : act family m Q bg.mu < b := by
    have he := act_strict_below_cap family m Q _ a (Nat.lt_of_lt_of_le bg.mu_a hstart)
      (by rw [hb]; exact hcap)
    rwa [hb] at he
  have ht := act_strict_below_cap family m ((family m).mul Q bg.j10) C a hC (by rw [ta]; omega)
  exact ⟨tsig, Nat.lt_trans ht (by rw [ta]; exact hab)⟩

#print axioms lowData
#print axioms segment_actor

end LaverLowerBounds.FiniteTable.InsertionBackground
