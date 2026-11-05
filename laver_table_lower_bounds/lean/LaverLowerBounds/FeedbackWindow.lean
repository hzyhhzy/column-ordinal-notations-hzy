import LaverLowerBounds.BackgroundIteration
import LaverLowerBounds.StandardLine
import LaverLowerBounds.LineShortening
import LaverLowerBounds.TripleCount
import LaverLowerBounds.Numerical

set_option autoImplicit false

namespace LaverLowerBounds.FiniteTable

structure FeedbackWindow (family : BinaryFamily) (m : Nat) where
  bg : InsertionBackground family m
  b : Nat
  P : Nat
  a_b : bg.a < b
  b_c : b < bg.c
  P0 : act family m P 0 = bg.a
  P1 : act family m P 1 = b
  Pb : act family m P b = bg.c
  line : Lined family m bg.k 2 bg.a b

def nativeFeedbackWindow (family : BinaryFamily) (m : Nat) (hm : PeriodAtLeast32 (family m)) :
    FeedbackWindow family m := by
  let s := fanSeed family m hm
  have wd := s.windowData
  exact {
    bg := nativeInsertionBackground family m hm
    b := s.entry, P := s.P
    a_b := wd.six_lt_entry, b_c := wd.entry_lt_seven
    P0 := wd.P0, P1 := wd.P1, Pb := wd.P_entry, line := wd.two_line }

namespace FeedbackWindow

variable {family : BinaryFamily} {m : Nat}

def map (w : FeedbackWindow family m) (H : Nat)
    (h0 : act family m H 0 = 0) (h1 : act family m H 1 = 1)
    (hc : act family m H w.bg.c < m) : FeedbackWindow family m := by
  have hb : act family m H w.b < m := Nat.lt_of_le_of_lt
    (act_mono family m H (Nat.le_of_lt w.b_c)) hc
  exact {
    bg := w.bg.map H h0 h1 hc
    b := act family m H w.b
    P := (family m).mul H w.P
    a_b := act_strict_below_cap family m H _ _ w.a_b hb
    b_c := act_strict_below_cap family m H _ _ w.b_c hc
    P0 := application_at family m H w.P h0 w.P0
    P1 := application_at family m H w.P h1 w.P1
    Pb := application_at family m H w.P rfl w.Pb
    line := w.line.map H hb }

theorem k_a (w : FeedbackWindow family m) : w.bg.k < w.bg.a := by
  have := w.bg.k_sigma
  have := w.bg.sigma_r
  have := w.bg.r_mu
  have := w.bg.mu_a
  omega

/-- A natural number below the entry becomes that many actual line segments.
The standard chain, multiplication, and endpoint-preserving contraction are
all already proved; this is not an inference from mere endpoint size. -/
theorem number_to_line (w : FeedbackWindow family m) (N : Nat)
    (hN : 0 < N) (hNb : N < w.b) :
    ∃ z, Lined family m w.bg.k N w.bg.a z ∧ z < w.bg.c := by
  let l := Nat.log2 N
  have hp : 2 ^ l ≤ N := (Nat.le_log2 (by omega : N ≠ 0)).mp (Nat.le_refl _)
  have hbcap : w.b < m := Nat.lt_trans w.b_c w.bg.c_cap
  have std := standard_line family m l (by omega)
  have hz : act family m w.P (2 ^ l) < w.bg.c := by
    have he := act_strict_below_cap family m w.P (2 ^ l) w.b (by omega)
      (by rw [w.Pb]; exact w.bg.c_cap)
    rwa [w.Pb] at he
  have higher := std.map w.P (Nat.lt_trans hz w.bg.c_cap)
  rw [w.P0, w.P1] at higher
  have multiplied := w.line.multiply higher w.k_a
  have hlen : N ≤ 2 * 2 ^ l := by
    have he := Nat.lt_log2_self (n := N)
    change N < 2 ^ (l + 1) at he
    rw [Nat.pow_succ] at he
    omega
  exact ⟨_, multiplied.shorten w.k_a hN hlen, hz⟩

theorem base_fan (w : FeedbackWindow family m) {h : Nat}
    (old : OwnedFan family m h) (hh : 3 ≤ h) (hold : old.fan.endpoint < w.b) :
    ∃ next : OwnedFan family m (base ParentBMS.tripleCount h), next.fan.endpoint < w.bg.c := by
  have hcount := old.fan.tripleCount_lt hh
  have hN := ParentBMS.tripleCount_ge_three h
  obtain ⟨z, line, hz⟩ := w.number_to_line (ParentBMS.tripleCount h) (by omega) (by omega)
  obtain ⟨next, hnext⟩ := w.bg.line_to_fan line (Nat.le_refl _)
  exact ⟨next, Nat.lt_trans hnext hz⟩

end FeedbackWindow

/-- Uniformity under every bounded outer actor is an explicit conclusion to
be proved by each template constructor. It is not an additional algebra axiom. -/
def NaturalTemplate (family : BinaryFamily) (m b d : Nat) (F : Nat → Nat) : Prop :=
  ∀ H, act family m H 0 = 0 → act family m H 1 = 1 → act family m H d < m →
    ∀ h, 3 ≤ h → ∀ old : OwnedFan family m h, old.fan.endpoint < act family m H b →
      ∃ next : OwnedFan family m (F h), next.fan.endpoint < act family m H d

theorem FeedbackWindow.base_template {family : BinaryFamily} {m : Nat} (w : FeedbackWindow family m) :
    NaturalTemplate family m w.b w.bg.c (base ParentBMS.tripleCount) := by
  intro H h0 h1 hc h hh old hold
  exact (w.map H h0 h1 hc).base_fan old hh hold

#print axioms FeedbackWindow.number_to_line
#print axioms FeedbackWindow.base_template

end LaverLowerBounds.FiniteTable
