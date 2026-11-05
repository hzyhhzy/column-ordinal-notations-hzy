import LaverLowerBounds.DynamicFeedback

set_option autoImplicit false

namespace LaverLowerBounds.FiniteTable

def promoter (family : BinaryFamily) (m : Nat) : Nat := (family m).mul 9 4

structure UpperWindowData (family : BinaryFamily) (m : Nat) : Prop where
  c_nu : theta family m 7 < act family m 9 3
  nu_eight : act family m 9 3 < theta family m 8
  S_signature : signature m (promoter family m) = theta family m 4
  S_first : act family m (promoter family m) (theta family m 4) = act family m 9 3
  S_next : act family m (promoter family m) (act family m 9 3) = theta family m 8

/-- The strict upper feedback window, including the nontrivial c<j9(3) guard. -/
theorem upperWindowData (family : BinaryFamily) (m : Nat) (hm : PeriodAtLeast32 (family m)) :
    UpperWindowData family m := by
  have hd := higherData family m hm
  have h9 : 9 ≤ m := Nat.le_of_lt (threshold_gt_nine family m hm)
  have n1 := mul_next_small family m 1 h9 (by decide)
  have n2 := mul_next_small family m 2 h9 (by decide)
  have n9 := mul_next_small family m 9 h9 (by decide)
  have n10 := mul_next_small family m 10 h9 (by decide)
  have p11 := act_from_low family m 1 1 12 2 h9 (LowProducts.v1_2 (family 9)) (by decide) (by decide)
  have p12 := act_from_low family m 1 2 240 4 h9 (LowProducts.v1_4 (family 9)) (by decide) (by decide)
  have p31 := act_from_low family m 3 1 8 3 h9 (LowProducts.v3_2 (family 9)) (by decide) (by decide)
  have p42 := act_from_low family m 4 2 8 3 h9 (LowProducts.v4_4 (family 9)) (by decide) (by decide)
  have p43 := act_from_low family m 4 3 496 4 h9 (LowProducts.v4_8 (family 9)) (by decide) (by decide)
  have p91 := act_from_low family m 9 1 508 2 h9 (LowProducts.v9_2 (family 9)) (by decide) (by decide)
  obtain ⟨sig10, ten1, ten2⟩ := ten_low family m hm
  have p92 : act family m 9 2 = act family m 7 2 := by
    have he := next_small family m 9 1 h9 (by decide)
    rw [p91, p11, ten2] at he
    exact he.symm
  have tenMu : act family m 10 (act family m 7 2) = act family m 9 4 := by
    have he := next_small family m 9 2 h9 (by decide)
    simpa only [p92, p12] using he
  let V := (family m).mul 10 10
  let A := (family m).mul 9 3
  let B := (family m).mul V 1
  let Q := (family m).mul 10 11
  have Veq : V = (family m).mul 9 2 := by
    have he := (family m).mul_distrib 9 1 1
    rw [n1, n9] at he
    exact he.symm
  have Aeq : A = (family m).mul V 10 := by
    have he := (family m).mul_distrib 9 2 1
    rw [n2, n9, ← Veq] at he
    exact he
  have QV : Q = (family m).mul V 11 := by
    have he := (family m).mul_distrib 10 10 1
    rw [n10] at he
    exact he
  have Qeq : Q = (family m).mul A B := by
    have he := (family m).mul_distrib V 10 1
    rw [n10, ← Aeq, ← QV] at he
    exact he
  have Vsig : signature m V = 2 := by dsimp [V]; rw [signature_mul, sig10, ten1]
  have V1 : act family m V 1 = 1 := fixes_below_signature family m V 1 (by rw [Vsig]; decide)
  have V2 : act family m V 2 = act family m 7 2 :=
    (application_at family m 10 10 ten1 ten1).trans ten2
  have A1 : act family m A 1 = act family m 7 2 := by
    rw [Aeq]
    exact (application_at family m V 10 V1 ten1).trans V2
  have A2 : act family m A 2 = act family m 9 3 := application_at family m 9 3 p91 p31
  have Bcong : congruent m 2 B 1 := by
    have he := app_critical family m V 1
    rwa [Vsig] at he
  have Qcong : congruent m (act family m 9 3) Q ((family m).mul A 1) := by
    have he := congruent_transport family m Bcong A
    rwa [A2, ← Qeq] at he
  have nuEight : act family m 9 3 < act family m 9 4 :=
    act_strict_below_cap family m 9 3 4 (by decide) (Nat.lt_trans hd.eight_lt_upper hd.upper_below)
  have nuCap : act family m 9 3 < m := Nat.lt_trans nuEight (Nat.lt_trans hd.eight_lt_upper hd.upper_below)
  have AjMu : act family m ((family m).mul A 1) (act family m 7 2) = act family m 9 3 :=
    (application_at family m A 1 A1 p11).trans A2
  have Aj4 : act family m ((family m).mul A 1) 4 < act family m 9 3 := by
    have he := act_strict_below_cap family m ((family m).mul A 1) 4 (act family m 7 2)
      (by have := hd.mu_lower; omega) (by rw [AjMu]; exact nuCap)
    rwa [AjMu] at he
  have Q4nu : act family m Q 4 < act family m 9 3 := by
    have he := congruent_read family m (congruent_symm Qcong) Aj4
    omega
  have Qsquare : congruent m (act family m 9 4) Q ((family m).comp 11 11) := by
    have he := congruent_transport family m hd.square 10
    simpa only [tenMu, (family m).mul_comp, n10] using he
  have comp4 : act family m ((family m).comp 11 11) 4 = theta family m 7 := act_composition family m 11 11 4
  have Q4 : act family m Q 4 = theta family m 7 := by
    have he := congruent_read family m (congruent_symm Qsquare) (by rw [comp4]; exact hd.seven_lt_eight)
    rw [comp4] at he
    exact he.symm
  have sig4 : signature m 4 = 2 := signature_from_nine m 4 2 h9 (by decide) (by decide)
  refine ⟨by rw [← Q4]; exact Q4nu, nuEight, ?_, ?_, ?_⟩
  · change signature m ((family m).mul 9 4) = act family m 7 2
    rw [signature_mul, sig4, p92]
  · exact application_at family m 9 4 p92 p42
  · exact application_at family m 9 4 rfl p43

structure FeedbackCap (family : BinaryFamily) (m : Nat) where
  dynamicWindow : DynamicWindow family m
  S : Nat
  S0 : act family m S 0 = 0
  S1 : act family m S 1 = 1
  Sk : act family m S dynamicWindow.window.bg.k = dynamicWindow.window.bg.k
  gap : dynamicWindow.d < act family m S dynamicWindow.window.bg.a
  cap : act family m S dynamicWindow.window.bg.c < m

def nativeFeedbackCap (family : BinaryFamily) (m : Nat) (hm : PeriodAtLeast32 (family m)) :
    FeedbackCap family m := by
  let w := nativeFeedbackWindow family m hm
  let s := fanSeed family m hm
  let S := promoter family m
  let u := act family m S (theta family m 5)
  let A := (family m).mul S s.f
  let d := act family m A (theta family m 7)
  have hd := higherData family m hm
  have upper := upperWindowData family m hm
  have td := s.termData
  have cap8 : theta family m 8 < m := Nat.lt_trans hd.eight_lt_upper hd.upper_below
  have Sfix {x : Nat} (hx : x < theta family m 4) : act family m S x = x :=
    fixes_below_signature family m S x (by rw [upper.S_signature]; exact hx)
  have S0 : act family m S 0 = 0 := Sfix (by have := hd.mu_lower; change 0 < act family m 7 2; omega)
  have S1 : act family m S 1 = 1 := Sfix (by have := hd.mu_lower; change 1 < act family m 7 2; omega)
  have S2 : act family m S 2 = 2 := Sfix (by have := hd.mu_lower; change 2 < act family m 7 2; omega)
  have S4 : act family m S 4 = 4 := Sfix (by have := hd.mu_lower; change 4 < act family m 7 2; omega)
  have Sc : act family m S (theta family m 7) < theta family m 8 := by
    have he := act_strict_below_cap family m S (theta family m 7) (act family m 9 3)
      upper.c_nu (by rw [upper.S_next]; exact cap8)
    rwa [upper.S_next] at he
  have Sa : act family m S (theta family m 6) < m := Nat.lt_of_le_of_lt
    (act_mono family m S (Nat.le_of_lt hd.six_lt_seven)) (Nat.lt_trans Sc cap8)
  have uSa : u < act family m S (theta family m 6) :=
    act_strict_below_cap family m S _ _ hd.five_lt_six Sa
  have uCap : u < m := Nat.lt_trans uSa Sa
  have nuU : act family m 9 3 < u := by
    have he := act_strict_below_cap family m S (theta family m 4) (theta family m 5)
      hd.mu_lt_five uCap
    rwa [upper.S_first] at he
  have cu : theta family m 7 < u := Nat.lt_trans upper.c_nu nuU
  have A0 : act family m A 0 = 4 := (application_at family m S s.f S0 td.f0).trans S4
  have A1 : act family m A 1 = u := application_at family m S s.f S1 td.f1
  have Au : act family m A u = act family m S (theta family m 6) :=
    application_at family m S s.f rfl td.f5
  have dSa : d < act family m S (theta family m 6) := by
    have he := act_strict_below_cap family m A (theta family m 7) u cu (by rw [Au]; exact Sa)
    rwa [Au] at he
  have dCap : d < m := Nat.lt_trans dSa Sa
  have ud : u < d := by
    have h1c : 1 < theta family m 7 := s.points.strict (by decide : 1 < 7) (by decide)
    have he := act_strict_below_cap family m A 1 (theta family m 7) h1c dCap
    rwa [A1] at he
  let dyn : DynamicWindow family m := {
    window := w, r := 4, u := u, d := d, A := A
    k_r := by change 2 < 4; decide
    r_a := s.points.strict (by decide : 3 < 6) (by decide)
    c_u := cu, u_d := ud, d_cap := dCap
    A0 := A0, A1 := A1, Ac := rfl }
  exact {
    dynamicWindow := dyn, S := S, S0 := S0, S1 := S1, Sk := S2
    gap := dSa, cap := Nat.lt_trans Sc cap8 }

#print axioms upperWindowData
#print axioms nativeFeedbackCap

end LaverLowerBounds.FiniteTable
