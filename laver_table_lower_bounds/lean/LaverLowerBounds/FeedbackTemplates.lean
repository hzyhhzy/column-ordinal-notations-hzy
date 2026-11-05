import LaverLowerBounds.FeedbackWindow

set_option autoImplicit false

namespace LaverLowerBounds

theorem iter_succ_start (F : Nat → Nat) (n h : Nat) : iter F (n + 1) h = iter F n (F h) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg F ih

def PreservesHeightFloor (F : Nat → Nat) : Prop := ∀ h, 3 ≤ h → 3 ≤ F h

theorem iter_preserves_height {F : Nat → Nat} (hF : PreservesHeightFloor F)
    (n h : Nat) (hh : 3 ≤ h) : 3 ≤ iter F n h := by
  induction n with
  | zero => exact hh
  | succ n ih => exact hF _ ih

theorem base_preserves_height : PreservesHeightFloor (base ParentBMS.tripleCount) := by
  intro h _
  have := ParentBMS.tripleCount_ge_three h
  unfold base
  omega

theorem upgrade_preserves_height {F : Nat → Nat} (hF : PreservesHeightFloor F) :
    PreservesHeightFloor (upgrade ParentBMS.tripleCount F) := by
  intro h hh
  exact iter_preserves_height hF _ h hh

namespace FiniteTable

namespace NaturalTemplate

variable {family : BinaryFamily} {m b d : Nat} {F : Nat → Nat}

theorem map (template : NaturalTemplate family m b d F) (e : Nat)
    (e0 : act family m e 0 = 0) (e1 : act family m e 1 = 1) :
    NaturalTemplate family m (act family m e b) (act family m e d) F := by
  intro H h0 h1 hc h hh old hold
  have c0 : act family m ((family m).comp H e) 0 = 0 := by rw [act_composition, e0, h0]
  have c1 : act family m ((family m).comp H e) 1 = 1 := by rw [act_composition, e1, h1]
  have result := template ((family m).comp H e) c0 c1 (by rw [act_composition]; exact hc)
    h hh old (by rw [act_composition]; exact hold)
  simpa only [act_composition] using result

theorem widen (template : NaturalTemplate family m b d F) {d' : Nat} (hdd : d ≤ d') :
    NaturalTemplate family m b d' F := by
  intro H h0 h1 hc h hh old hold
  have he := act_mono family m H hdd
  obtain ⟨next, hn⟩ := template H h0 h1 (Nat.lt_of_le_of_lt he hc) h hh old hold
  exact ⟨next, Nat.lt_of_lt_of_le hn he⟩

theorem along_line (template : NaturalTemplate family m b d F)
    (hF : PreservesHeightFloor F) {k : Nat} (hk : 2 ≤ k) (hkb : k < b) (hbd : b ≤ d)
    {n a z : Nat} (line : Lined family m k n a z) :
    d < a → ∀ h, 3 ≤ h → ∀ old : OwnedFan family m h, old.fan.endpoint < a →
      ∃ next : OwnedFan family m (iter F n h), next.fan.endpoint < z := by
  induction line with
  | nil _ =>
      intro _ h _ old hold
      exact ⟨old, hold⟩
  | @cons n a y z Q hsig hroot hnext hay tail ih =>
      intro hda h hh old hold
      have hycap : y < m := Nat.lt_of_le_of_lt tail.endpoints.1 tail.endpoints.2
      have q0 : act family m Q 0 = 0 := fixes_below_signature family m Q 0 (by rw [hsig]; omega)
      have q1 : act family m Q 1 = 1 := fixes_below_signature family m Q 1 (by rw [hsig]; omega)
      have qd : act family m Q d < y := by
        have he := act_strict_below_cap family m Q d a hda (by rw [hnext]; exact hycap)
        rwa [hnext] at he
      have qbcap : act family m Q b < m := Nat.lt_of_le_of_lt (act_mono family m Q hbd) (by omega)
      have ab : a < act family m Q b := by
        have he := act_strict_below_cap family m Q k b hkb qbcap
        rwa [hroot] at he
      obtain ⟨next, hn⟩ := template Q q0 q1 (by omega) h hh old (Nat.lt_trans hold ab)
      obtain ⟨final, hf⟩ := ih (by omega) (F h) (hF h hh) next (Nat.lt_trans hn qd)
      rw [iter_succ_start]
      exact ⟨final, hf⟩

end NaturalTemplate

/-- One full feedback upgrade. The returned template is again uniform under
every outer actor whose image of the NEW exit is below the cap. -/
theorem upgrade_template {family : BinaryFamily} {m : Nat} (w : FeedbackWindow family m)
    {F : Nat → Nat} {d : Nat} (template : NaturalTemplate family m w.b d F)
    (hF : PreservesHeightFloor F) (hcd : w.bg.c ≤ d) (H : Nat)
    (H0 : act family m H 0 = 0) (H1 : act family m H 1 = 1)
    (Hk : act family m H w.bg.k = w.bg.k)
    (hda : d < act family m H w.bg.a) (Hcap : act family m H w.bg.c < m) :
    NaturalTemplate family m w.b (act family m H w.bg.c) (upgrade ParentBMS.tripleCount F) := by
  intro J J0 J1 Jcap h hh old hold
  have hac : act family m H w.bg.a < act family m H w.bg.c :=
    act_strict_below_cap family m H _ _ w.bg.a_c Hcap
  have jab : act family m H w.bg.a < act family m H w.b :=
    act_strict_below_cap family m H _ _ w.a_b
      (Nat.lt_of_le_of_lt (act_mono family m H (Nat.le_of_lt w.b_c)) Hcap)
  have JaCap : act family m J (act family m H w.bg.a) < m :=
    Nat.lt_of_le_of_lt (act_mono family m J (Nat.le_of_lt hac)) Jcap
  have Jda : act family m J d < act family m J (act family m H w.bg.a) :=
    act_strict_below_cap family m J _ _ hda JaCap
  have JdCap : act family m J d < m := Nat.lt_trans Jda JaCap
  let composed := (family m).comp J H
  have c0 : act family m composed 0 = 0 := by dsimp [composed]; rw [act_composition, H0, J0]
  have c1 : act family m composed 1 = 1 := by dsimp [composed]; rw [act_composition, H1, J1]
  have ccap : act family m composed w.bg.c < m := by dsimp [composed]; rw [act_composition]; exact Jcap
  let w' := w.map composed c0 c1 ccap
  have wa : w'.bg.a = act family m J (act family m H w.bg.a) := act_composition family m J H w.bg.a
  have wb : w'.b = act family m J (act family m H w.b) := act_composition family m J H w.b
  have wc : w'.bg.c = act family m J (act family m H w.bg.c) := act_composition family m J H w.bg.c
  have wk : w'.bg.k = act family m J w.bg.k := by
    change act family m composed w.bg.k = _
    dsimp [composed]
    rw [act_composition, Hk]
  obtain ⟨first, hfirst⟩ := template J J0 J1 JdCap h hh old hold
  let N := ParentBMS.tripleCount (F h)
  have hcount : N < first.fan.endpoint := first.fan.tripleCount_lt (hF h hh)
  have hN : 0 < N := by have := ParentBMS.tripleCount_ge_three (F h); omega
  have hNa : N < w'.bg.a := by rw [wa]; omega
  have hNb : N < w'.b := Nat.lt_trans hNa w'.a_b
  obtain ⟨z, line, hz⟩ := w'.number_to_line N hN hNb
  rw [wk] at line
  have mapped := template.map J J0 J1
  have bd : w.b ≤ d := Nat.le_trans (Nat.le_of_lt w.b_c) hcd
  have JbCap : act family m J w.b < m := Nat.lt_of_le_of_lt (act_mono family m J bd) JdCap
  have Jkb : act family m J w.bg.k < act family m J w.b :=
    act_strict_below_cap family m J _ _ (Nat.lt_trans w.k_a w.a_b) JbCap
  have JkLower : 2 ≤ act family m J w.bg.k :=
    Nat.le_trans w.bg.k_lower (le_act family m J _ (by have := w.k_a; have := w.bg.a_c; have := w.bg.c_cap; omega))
  have Jbd := act_mono family m J bd
  obtain ⟨final, hfinal⟩ := mapped.along_line hF JkLower Jkb Jbd line
    (by rw [wa]; exact Jda) (F h) (hF h hh) first (by rw [wa]; omega)
  have height : upgrade ParentBMS.tripleCount F h = iter F N (F h) := iter_succ_start F N h
  rw [height]
  exact ⟨final, Nat.lt_trans hfinal (by rw [← wc]; exact hz)⟩

#print axioms NaturalTemplate.along_line
#print axioms upgrade_template

end FiniteTable
end LaverLowerBounds
