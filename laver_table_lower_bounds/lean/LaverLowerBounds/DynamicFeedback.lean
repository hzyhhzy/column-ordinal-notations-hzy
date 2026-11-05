import LaverLowerBounds.FeedbackTemplates

set_option autoImplicit false

namespace LaverLowerBounds

theorem stage_preserves_height (n : Nat) : PreservesHeightFloor (stage ParentBMS.tripleCount n) := by
  induction n with
  | zero => exact base_preserves_height
  | succ n ih => exact upgrade_preserves_height ih

theorem dynamic_preserves_height : PreservesHeightFloor (dynamic ParentBMS.tripleCount) := by
  intro h hh
  exact stage_preserves_height _ h hh

namespace FiniteTable

theorem act_identity (family : BinaryFamily) (m x : Nat) (hx : x ≤ m) : act family m 0 x = x := by
  unfold act
  rw [(family m).zero_mul]
  have he : signature m (2 ^ x % 2 ^ m) = signature m (2 ^ x) :=
    signature_mod_eq (by rw [Nat.mod_mod])
  rw [he, signature_pow m x hx]

theorem NaturalTemplate.evaluate {family : BinaryFamily} {m b d : Nat} {F : Nat → Nat}
    (template : NaturalTemplate family m b d F) (hm : 1 ≤ m) (hb : b ≤ m) (hd : d < m)
    {h : Nat} (hh : 3 ≤ h) (old : OwnedFan family m h) (hold : old.fan.endpoint < b) :
    ∃ next : OwnedFan family m (F h), next.fan.endpoint < d := by
  have h0 := act_identity family m 0 (Nat.zero_le _)
  have h1 := act_identity family m 1 hm
  have hbb := act_identity family m b hb
  have hdd := act_identity family m d (Nat.le_of_lt hd)
  have he := template 0 h0 h1 (by rw [hdd]; exact hd) h hh old (by rw [hbb]; exact hold)
  simpa only [hdd] using he

/-- Iterate upgrades along a high-root line. The starting template may already
have positive depth, and the final template works for every admissible input. -/
theorem grow_stage_along_line {family : BinaryFamily} {m : Nat} (w : FeedbackWindow family m)
    {r n u z : Nat} (line : Lined family m r n u z) (hkr : w.bg.k < r) (hra : r < w.bg.a) :
    ∀ i d, w.bg.c ≤ d → d < u → NaturalTemplate family m w.b d (stage ParentBMS.tripleCount i) →
      ∃ exit, w.bg.c ≤ exit ∧ exit < z ∧
        NaturalTemplate family m w.b exit (stage ParentBMS.tripleCount (i + n)) := by
  induction line with
  | nil _ =>
      intro i d hcd hdu template
      exact ⟨d, hcd, hdu, template⟩
  | @cons n u v z H hsig hstart hnext huv tail ih =>
      intro i d hcd hdu template
      have hvCap : v < m := Nat.lt_of_le_of_lt tail.endpoints.1 tail.endpoints.2
      have hk := w.bg.k_lower
      have H0 : act family m H 0 = 0 := fixes_below_signature family m H 0 (by rw [hsig]; omega)
      have H1 : act family m H 1 = 1 := fixes_below_signature family m H 1 (by rw [hsig]; omega)
      have Hk : act family m H w.bg.k = w.bg.k := fixes_below_signature family m H w.bg.k (by rw [hsig]; exact hkr)
      have hcu : w.bg.c < u := by omega
      have Hc : act family m H w.bg.c < v := by
        have he := act_strict_below_cap family m H w.bg.c u hcu (by rw [hnext]; exact hvCap)
        rwa [hnext] at he
      have HaCap : act family m H w.bg.a < m := Nat.lt_of_le_of_lt
        (act_mono family m H (Nat.le_of_lt w.bg.a_c)) (Nat.lt_trans Hc hvCap)
      have Hra : u < act family m H w.bg.a := by
        have he := act_strict_below_cap family m H r w.bg.a hra HaCap
        rwa [hstart] at he
      have upgraded := upgrade_template w template (stage_preserves_height i) hcd H H0 H1 Hk
        (Nat.lt_trans hdu Hra) (Nat.lt_trans Hc hvCap)
      have newAbove : w.bg.c ≤ act family m H w.bg.c := le_act family m H w.bg.c (Nat.le_of_lt w.bg.c_cap)
      obtain ⟨exit, hc, he, ht⟩ := ih (i + 1) (act family m H w.bg.c) newAbove Hc upgraded
      refine ⟨exit, hc, he, ?_⟩
      have hn : i + (n + 1) = (i + 1) + n := by omega
      rwa [hn]

theorem stage_template_from_line {family : BinaryFamily} {m : Nat} (w : FeedbackWindow family m)
    {r n u z : Nat} (line : Lined family m r n u z)
    (hkr : w.bg.k < r) (hra : r < w.bg.a) (hcu : w.bg.c < u) :
    ∃ exit, w.bg.c ≤ exit ∧ exit < z ∧ NaturalTemplate family m w.b exit (stage ParentBMS.tripleCount n) := by
  simpa only [Nat.zero_add] using
    grow_stage_along_line w line hkr hra 0 w.bg.c (Nat.le_refl _) hcu w.base_template

/-- Only the points at or below d are retained. A higher endpoint used to
discover the actor A is not part of its later transport interface. -/
structure DynamicWindow (family : BinaryFamily) (m : Nat) where
  window : FeedbackWindow family m
  r : Nat
  u : Nat
  d : Nat
  A : Nat
  k_r : window.bg.k < r
  r_a : r < window.bg.a
  c_u : window.bg.c < u
  u_d : u < d
  d_cap : d < m
  A0 : act family m A 0 = r
  A1 : act family m A 1 = u
  Ac : act family m A window.bg.c = d

namespace DynamicWindow

variable {family : BinaryFamily} {m : Nat}

def map (w : DynamicWindow family m) (H : Nat)
    (h0 : act family m H 0 = 0) (h1 : act family m H 1 = 1)
    (hd : act family m H w.d < m) : DynamicWindow family m := by
  have hcd : w.window.bg.c < w.d := Nat.lt_trans w.c_u w.u_d
  have hc : act family m H w.window.bg.c < m := Nat.lt_of_le_of_lt
    (act_mono family m H (Nat.le_of_lt hcd)) hd
  have ha : act family m H w.window.bg.a < m := Nat.lt_of_le_of_lt
    (act_mono family m H (Nat.le_of_lt w.window.bg.a_c)) hc
  have hr : act family m H w.r < m := Nat.lt_of_le_of_lt
    (act_mono family m H (Nat.le_of_lt w.r_a)) ha
  have hu : act family m H w.u < m := Nat.lt_of_le_of_lt
    (act_mono family m H (Nat.le_of_lt w.u_d)) hd
  exact {
    window := w.window.map H h0 h1 hc
    r := act family m H w.r, u := act family m H w.u, d := act family m H w.d
    A := (family m).mul H w.A
    k_r := act_strict_below_cap family m H _ _ w.k_r hr
    r_a := act_strict_below_cap family m H _ _ w.r_a ha
    c_u := act_strict_below_cap family m H _ _ w.c_u hu
    u_d := act_strict_below_cap family m H _ _ w.u_d hd
    d_cap := hd
    A0 := application_at family m H w.A h0 w.A0
    A1 := application_at family m H w.A h1 w.A1
    Ac := application_at family m H w.A rfl w.Ac }

theorem dynamic_fan (w : DynamicWindow family m) {h : Nat} (hh : 3 ≤ h)
    (old : OwnedFan family m h) (hold : old.fan.endpoint < w.window.b) :
    ∃ next : OwnedFan family m (dynamic ParentBMS.tripleCount h), next.fan.endpoint < w.d := by
  obtain ⟨first, hfirst⟩ := w.window.base_fan old hh hold
  let N := ParentBMS.tripleCount (base ParentBMS.tripleCount h)
  let l := Nat.log2 N
  have hN : 0 < N := by have := ParentBMS.tripleCount_ge_three (base ParentBMS.tripleCount h); omega
  have hcount : N < first.fan.endpoint := first.fan.tripleCount_lt (base_preserves_height h hh)
  have hp : 2 ^ l ≤ N := (Nat.le_log2 (by omega : N ≠ 0)).mp (Nat.le_refl _)
  have hpc : 2 ^ l < w.window.bg.c := by omega
  have std := standard_line family m l (Nat.lt_trans hpc w.window.bg.c_cap)
  have hz : act family m w.A (2 ^ l) < w.d := by
    have he := act_strict_below_cap family m w.A (2 ^ l) w.window.bg.c hpc
      (by rw [w.Ac]; exact w.d_cap)
    rwa [w.Ac] at he
  have line := std.map w.A (Nat.lt_trans hz w.d_cap)
  rw [w.A0, w.A1] at line
  obtain ⟨exit, hce, hez, template⟩ := stage_template_from_line w.window line w.k_r w.r_a w.c_u
  have hexit : exit < m := Nat.lt_trans hez (Nat.lt_trans hz w.d_cap)
  have hm : 1 ≤ m := by have := w.window.bg.k_lower; have := w.window.k_a; have := w.window.bg.a_c; have := w.window.bg.c_cap; omega
  have hb : w.window.b ≤ m := Nat.le_of_lt (Nat.lt_trans w.window.b_c w.window.bg.c_cap)
  obtain ⟨next, hn⟩ := template.evaluate hm hb hexit hh old hold
  exact ⟨next, Nat.lt_trans hn (Nat.lt_trans hez hz)⟩

theorem dynamic_template (w : DynamicWindow family m) :
    NaturalTemplate family m w.window.b w.d (dynamic ParentBMS.tripleCount) := by
  intro H H0 H1 Hcap h hh old hold
  exact (w.map H H0 H1 Hcap).dynamic_fan hh old hold

end DynamicWindow

#print axioms grow_stage_along_line
#print axioms DynamicWindow.dynamic_template

end FiniteTable
end LaverLowerBounds
