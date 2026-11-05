import LaverLowerBounds.UpperWindow

set_option autoImplicit false

namespace LaverLowerBounds.FiniteTable

theorem FeedbackCap.final_template {family : BinaryFamily} {m : Nat} (w : FeedbackCap family m) :
    NaturalTemplate family m w.dynamicWindow.window.b
      (act family m w.S w.dynamicWindow.window.bg.c) (finalHeight ParentBMS.tripleCount) := by
  have hcd : w.dynamicWindow.window.bg.c ≤ w.dynamicWindow.d :=
    Nat.le_of_lt (Nat.lt_trans w.dynamicWindow.c_u w.dynamicWindow.u_d)
  exact upgrade_template w.dynamicWindow.window w.dynamicWindow.dynamic_template
    dynamic_preserves_height hcd w.S w.S0 w.S1 w.Sk w.gap w.cap

/-- The complete finite-table budget for the dynamic feedback construction.
D is the ACTUAL fixed-[1] stopping count of the parent-array three-column
matrix wherever used. No BMS/FGH comparison is assumed in this theorem. -/
theorem finite_feedback_stops (family : BinaryFamily) (m : Nat) (hm : PeriodAtLeast32 (family m)) :
    ∃ n, PrefixDescent.Stops (fun s => ParentBMS.expand s 1)
        (ParentBMS.triple (finalHeight ParentBMS.tripleCount 18)) n ∧ n < m := by
  let w := nativeFeedbackCap family m hm
  have h9 := threshold_gt_nine family m hm
  have wbcap : w.dynamicWindow.window.b < m :=
    Nat.lt_trans w.dynamicWindow.window.b_c w.dynamicWindow.window.bg.c_cap
  obtain ⟨initial, hi⟩ := initial_height_eighteen family m hm
  have hi' : initial.fan.endpoint < w.dynamicWindow.window.b := hi
  obtain ⟨final, hf⟩ := w.final_template.evaluate (by omega) (Nat.le_of_lt wbcap) w.cap
    (by decide : 3 ≤ 18) initial hi'
  have hheight : 3 ≤ finalHeight ParentBMS.tripleCount 18 :=
    upgrade_preserves_height dynamic_preserves_height 18 (by decide)
  obtain ⟨n, hn, hcount⟩ := final.fan.counting_bound hheight
  exact ⟨n, hn, Nat.lt_trans hcount (Nat.lt_trans hf w.cap)⟩

theorem finite_feedback_budget (family : BinaryFamily) (m : Nat) (hm : PeriodAtLeast32 (family m)) :
    ParentBMS.tripleCount (finalHeight ParentBMS.tripleCount 18) < m := by
  obtain ⟨n, hn, hb⟩ := finite_feedback_stops family m hm
  rw [ParentBMS.tripleCount_eq hn]
  exact hb

/-- Generic numerical interface. FiniteFGHBound.lean supplies the actual
F_Lambda evaluator and proves its CountingEstimate, removing these generic
function hypotheses from the final theorem. -/
theorem threshold_bound_of_countingEstimate (family : BinaryFamily) (m : Nat)
    (hm : PeriodAtLeast32 (family m)) {g : Nat → Nat} (hg : Grows g)
    (hD : CountingEstimate ParentBMS.tripleCount g) : omegaSuccessor g 3 < m :=
  numerical_bound_at_three hg hD (finite_feedback_budget family m hm)

theorem q5_bound_of_countingEstimate (family : BinaryFamily) (m : Nat)
    (hm : Q5At family m) {g : Nat → Nat} (hg : Grows g)
    (hD : CountingEstimate ParentBMS.tripleCount g) : omegaSuccessor g 3 < m :=
  threshold_bound_of_countingEstimate family m hm.1 hg hD

#print axioms finite_feedback_budget
#print axioms q5_bound_of_countingEstimate

end LaverLowerBounds.FiniteTable
