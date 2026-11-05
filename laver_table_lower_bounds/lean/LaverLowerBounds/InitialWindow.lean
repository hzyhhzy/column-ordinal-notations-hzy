import LaverLowerBounds.InitialFan

set_option autoImplicit false

namespace LaverLowerBounds.FiniteTable

theorem two_from_three (family : BinaryFamily) (m root a b c e : Nat)
    (hsig : signature m e = root) (hr : act family m e root = a)
    (ha : act family m e a = b) (hb : act family m e b = c)
    (hra : root < a) (hab : a < b) (hbc : b < c) (hc : c < m) :
    Lined family m root 2 a c := by
  let u := (family m).mul e e
  let v := (family m).mul u e
  have usig : signature m u = a := by dsimp [u]; rw [signature_mul, hsig, hr]
  have ur : act family m u root = root := fixes_below_signature family m u root (by omega)
  have ua : act family m u a = b := (application_at family m e e hr hr).trans ha
  have ub : act family m u b = c := (application_at family m e e ha ha).trans hb
  have vsig : signature m v = root := by dsimp [v]; rw [signature_mul, hsig, ur]
  have vr : act family m v root = b := (application_at family m u e ur hr).trans ua
  have vb : act family m v b = c := (application_at family m u e ua ha).trans ub
  exact .cons e hsig hr ha hab (.cons v vsig vr vb hbc (.nil hc))

namespace FanSeed

variable {family : BinaryFamily} {m : Nat}

def entry (s : FanSeed family m) := act family m s.L3 (s.points.point 5)
def E (s : FanSeed family m) := (family m).mul s.L3 s.K
def P (s : FanSeed family m) := (family m).mul s.L3 s.f
def W (s : FanSeed family m) := (family m).mul s.L3 s.b

structure WindowData (s : FanSeed family m) : Prop where
  six_lt_entry : s.points.point 6 < s.entry
  entry_lt_seven : s.entry < s.points.point 7
  E0 : act family m s.E (s.points.point 0) = s.points.point 2
  E1 : act family m s.E (s.points.point 1) = s.points.point 6
  E6 : act family m s.E (s.points.point 6) = s.entry
  P0 : act family m s.P (s.points.point 0) = s.points.point 6
  P1 : act family m s.P (s.points.point 1) = s.entry
  P_entry : act family m s.P s.entry = s.points.point 7
  two_line : Lined family m (s.points.point 2) 2 (s.points.point 6) s.entry

theorem windowData (s : FanSeed family m) : WindowData s := by
  have hd := s.termData
  let t := s.points.point
  have lt {i j : Nat} (hij : i < j) (hj : j ≤ 8) : t i < t j := s.points.strict hij hj
  have h7 : t 7 < m := s.points.below (by decide)
  have eb : s.entry < t 7 := by
    have he := act_strict_below_cap family m s.L3 (t 5) (t 6)
      (lt (by decide) (by decide)) (by rw [hd.L3_next]; exact h7)
    rw [hd.L3_next] at he
    exact he
  have entryCap : s.entry < m := Nat.lt_trans eb h7
  have be : t 6 < s.entry := by
    have he := act_strict_below_cap family m s.L3 (t 3) (t 5)
      (lt (by decide) (by decide)) entryCap
    rw [hd.L3_first] at he
    exact he
  have fix {i : Nat} (hi : i < 3) : act family m s.L3 (t i) = t i :=
    fixes_below_signature family m s.L3 (t i) (by rw [hd.L3_signature]; exact lt hi (by decide))
  have e0 : act family m s.E (t 0) = t 2 :=
    (application_at family m s.L3 s.K (fix (by decide)) (s.K_image 0 (by decide))).trans (fix (by decide))
  have e1 : act family m s.E (t 1) = t 6 :=
    (application_at family m s.L3 s.K (fix (by decide)) (s.K_image 1 (by decide))).trans hd.L3_first
  have e6 : act family m s.E (t 6) = s.entry :=
    application_at family m s.L3 s.K hd.L3_first (s.K_image 3 (by decide))
  have p0 : act family m s.P (t 0) = t 6 :=
    (application_at family m s.L3 s.f (fix (by decide)) hd.f0).trans hd.L3_first
  have p1 : act family m s.P (t 1) = s.entry := application_at family m s.L3 s.f (fix (by decide)) hd.f1
  have pe : act family m s.P s.entry = t 7 :=
    (application_at family m s.L3 s.f (rfl : act family m s.L3 (t 5) = s.entry) hd.f5).trans hd.L3_next
  let middle := act family m s.L3 (t 4)
  have bm : middle < s.entry := act_strict_below_cap family m s.L3 (t 4) (t 5)
    (lt (by decide) (by decide)) entryCap
  have mb : t 6 < middle := by
    have he := act_strict_below_cap family m s.L3 (t 3) (t 4)
      (lt (by decide) (by decide)) (show middle < m by omega)
    rw [hd.L3_first] at he
    exact he
  have wsig : signature m s.W = t 2 := by
    change signature m ((family m).mul s.L3 s.b) = _
    rw [signature_mul, hd.b_signature]
    exact fix (by decide)
  have w2 : act family m s.W (t 2) = t 6 := (application_at family m s.L3 s.b (fix (by decide)) hd.b2).trans hd.L3_first
  have w6 : act family m s.W (t 6) = middle := application_at family m s.L3 s.b hd.L3_first hd.b3
  have wm : act family m s.W middle = s.entry := application_at family m s.L3 s.b rfl hd.b4
  have line := two_from_three family m (t 2) (t 6) middle s.entry s.W wsig w2 w6 wm
    (lt (by decide) (by decide)) mb bm (by omega)
  exact ⟨be, eb, e0, e1, e6, p0, p1, pe, line⟩

theorem initial_sixteen_line (family : BinaryFamily) (m : Nat) (hm : PeriodAtLeast32 (family m)) :
    ∃ endpoint, Lined family m 2 16 (theta family m 6) endpoint ∧ endpoint < (fanSeed family m hm).entry := by
  let s := fanSeed family m hm
  have wd := s.windowData
  have h7 : s.points.point 7 < m := s.points.below (by decide)
  have entryCap : s.entry < m := Nat.lt_trans wd.entry_lt_seven h7
  have h6 : act family m s.E (s.points.point 6) < m := by rw [wd.E6]; exact entryCap
  have h5 : act family m s.E (s.points.point 5) < s.entry := by
    have he := act_strict_below_cap family m s.E (s.points.point 5) (s.points.point 6)
      (s.points.strict (by decide) (by decide)) h6
    exact wd.E6 ▸ he
  have line : Lined family m (s.points.point 0) 16 (s.points.point 1) (s.points.point 5) :=
    short_initial_line family m hm
  have mapped := line.map s.E (Nat.lt_trans h5 entryCap)
  rw [wd.E0, wd.E1] at mapped
  exact ⟨_, mapped, h5⟩

#print axioms windowData
#print axioms initial_sixteen_line

end FanSeed
end LaverLowerBounds.FiniteTable
