import LaverLowerBounds.FiniteFeedbackBudget
import LaverLowerBounds.UpperHierarchyEvaluation

set_option autoImplicit false

namespace LaverLowerBounds.FiniteTable

/-- Fully realized Lambda+omega+1 lower bound for the parent-array hierarchy.
The result contains a finite FGH evaluation, not an arbitrary totalized value.
No I3 assumption, global BMS well-ordering, or counting-estimate hypothesis is
present. OriginalBMSBound.lean transfers this to the original numeric BM4
evaluator using the exact expansion correspondence. -/
theorem threshold_fgh_bound (family : BinaryFamily) (m : Nat) (hm : PeriodAtLeast32 (family m)) :
    ∃ y, ParentBMS.OmegaSuccessorEval 3 y ∧ y < m := by
  let g := ParentBMS.diagonalFast
  let D := ParentBMS.tripleCount
  let y := omegaSuccessor g 3
  have hg : Grows g := ParentBMS.diagonalFast_grows
  have hD : CountingEstimate D g := ParentBMS.triple_countingEstimate
  have hbuffer : buffer y ≤ finalHeight D 18 :=
    finalHeight_simulates hg hD 3 18 (by decide) (by decide)
  obtain ⟨n, hn, hnm⟩ := finite_feedback_stops family m hm
  have hactual : ∀ a, 2 ≤ a → a ≤ y → ParentBMS.LambdaEval a (g a) := by
    intro a ha hay
    exact (ParentBMS.triple_diagonal_bound (by omega)
      (Nat.le_trans (buffer_mono hay) hbuffer) hn).1
  have heval : ParentBMS.OmegaSuccessorEval 3 y :=
    ParentBMS.omegaSuccessor_realized hg hactual (by decide) (Nat.le_refl _)
  have hbound : y < m := threshold_bound_of_countingEstimate family m hm hg hD
  exact ⟨y, heval, hbound⟩

theorem q5_fgh_bound (family : BinaryFamily) (m : Nat) (hm : Q5At family m) :
    ∃ y, ParentBMS.OmegaSuccessorEval 3 y ∧ y < m :=
  threshold_fgh_bound family m hm.1

theorem q5_above_every_fgh_value (family : BinaryFamily) (m : Nat) (hm : Q5At family m)
    {y : Nat} (hy : ParentBMS.OmegaSuccessorEval 3 y) : y < m := by
  obtain ⟨z, hz, hzm⟩ := q5_fgh_bound family m hm
  have he := ParentBMS.omegaSuccessorEval_unique hy hz
  omega

#print axioms threshold_fgh_bound
#print axioms q5_fgh_bound
#print axioms q5_above_every_fgh_value

end LaverLowerBounds.FiniteTable
