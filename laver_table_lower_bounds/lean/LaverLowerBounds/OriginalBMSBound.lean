import LaverLowerBounds.FiniteFGHBound
import LaverLowerBounds.NumericFGH

set_option autoImplicit false

namespace LaverLowerBounds.FiniteTable

/-- Original numerical BM4 conclusion, including a terminating FGH evaluation.
Lambda[n] is the (n+1)-row seed, F_0(x)=x+1, successor iteration is x+1,
and (Lambda+omega)[x]=Lambda+(x+1). No I3, global BMS well-ordering, or
unproved comparison/counting hypothesis is assumed. -/
theorem threshold_original_bms_bound (family : BinaryFamily) (m : Nat)
    (hm : PeriodAtLeast32 (family m)) :
    ∃ y, NumericBMS.OmegaSuccessorEval 3 y ∧ y < m := by
  obtain ⟨y, hy, hym⟩ := threshold_fgh_bound family m hm
  exact ⟨y, (NumericBMS.omegaSuccessorEval_iff 3 y).mpr hy, hym⟩

/-- If q(5)=m exists, m exceeds F_(lim(BMS)+omega+1)(3), for the
original numeric BM4 definition. This also proves existence of that finite
FGH value under the stated finite-period hypothesis. -/
theorem q5_original_bms_bound (family : BinaryFamily) (m : Nat)
    (hm : Q5At family m) : ∃ y, NumericBMS.OmegaSuccessorEval 3 y ∧ y < m :=
  threshold_original_bms_bound family m hm.1

theorem q5_above_original_bms_value (family : BinaryFamily) (m : Nat)
    (hm : Q5At family m) {y : Nat} (hy : NumericBMS.OmegaSuccessorEval 3 y) : y < m := by
  obtain ⟨z, hz, hzm⟩ := q5_original_bms_bound family m hm
  have := NumericBMS.omegaSuccessorEval_unique hy hz
  omega

#print axioms threshold_original_bms_bound
#print axioms q5_original_bms_bound
#print axioms q5_above_original_bms_value

end LaverLowerBounds.FiniteTable
