import K11.Successor
import K11.Index

/-!
Public entry point. Everything in this statement is an explicit finite
Laver-table operation or an actual evaluation of the numerical BM4 rules.
No elementary-embedding model, I3, total FGH, or unproved counting interface
is a hypothesis.
-/

set_option autoImplicit false
namespace LaverLowerBounds.FiniteTable

/-- The target entry alone suffices: no condition on row 1 is assumed. -/
theorem k11_nonzero_bms_successor_bound (family : BinaryFamily) (m : Nat)
    (hm : (family m).mul 11 16 ≠ 0) :
    ∃ y, NumericBMS.FiniteLevelEval 1 120 y ∧
      y < signature m ((family m).mul 11 16) ∧
      signature m ((family m).mul 11 16) < m := by
  have hc := (K11.act_unsaturated_iff family m 11 4).mpr hm
  obtain ⟨y, hy, hb⟩ := K11.bms_successor_120_of_unsaturated family m hc
  exact ⟨y, hy, hb, hc⟩

/-- If the stable k11 index exists, it exceeds the actual BMS+1 FGH value. -/
theorem k11_index_bms_successor_bound (family : BinaryFamily) (r : Nat)
    (hr : K11Index family r) :
    ∃ y, NumericBMS.FiniteLevelEval 1 120 y ∧ y < r := by
  obtain ⟨m, he, hc⟩ := hr
  obtain ⟨y, hy, hb⟩ := K11.bms_successor_120_of_unsaturated family m (by omega)
  exact ⟨y, hy, by omega⟩

/-- Unconditional dichotomy, relative only to the ordinary finite-table
defining equations: the stable index is absent, or it exceeds the bound. -/
theorem k11_undefined_or_large (family : BinaryFamily) :
    (¬ ∃ r, K11Index family r) ∨
      ∃ r y, K11Index family r ∧ NumericBMS.FiniteLevelEval 1 120 y ∧ y < r := by
  classical
  by_cases he : ∃ r, K11Index family r
  · obtain ⟨r, hr⟩ := he
    obtain ⟨y, hy, hb⟩ := k11_index_bms_successor_bound family r hr
    exact Or.inr ⟨r, y, hr, hy, hb⟩
  · exact Or.inl he

/-- The undefined branch has a direct table interpretation: column 16 in
row 11 is zero at every finite order. -/
theorem k11_zero_or_large (family : BinaryFamily) :
    (∀ m, (family m).mul 11 16 = 0) ∨
      ∃ r y, K11Index family r ∧ NumericBMS.FiniteLevelEval 1 120 y ∧ y < r := by
  rcases k11_undefined_or_large family with hn | hl
  · exact Or.inl ((k11Index_absent_iff family).mp hn)
  · exact Or.inr hl

/-- If row 1 has not vanished at column 16, the capped 2-adic valuation
of row 11, column 16 is strictly above the BMS+1 FGH value at input 120.
The valuation is also strictly below the cap, so it is not a saturated
value. Column 16 is 2^4; the index 4 corresponds to κ₃ = γ₄. -/
theorem k11_original_bms_successor_bound (family : BinaryFamily) (m : Nat)
    (hm : (family m).mul 1 16 ≠ 0) :
    ∃ y, NumericBMS.FiniteLevelEval 1 120 y ∧
      y < signature m ((family m).mul 11 16) ∧
      signature m ((family m).mul 11 16) < m := by
  have hp := (periodAtLeast32_iff family m).mpr hm
  obtain ⟨y, hy, hb⟩ := K11.bms_successor_120 family m hp
  have hc := k_four_unsaturated family m hp
  exact ⟨y, hy, hb, hc⟩

/-- In particular this holds at the first period-32 threshold, if it exists. -/
theorem q5_k11_bms_successor_bound (family : BinaryFamily) (m : Nat)
    (hm : Q5At family m) :
    ∃ y, NumericBMS.FiniteLevelEval 1 120 y ∧
      y < signature m ((family m).mul 11 16) ∧
      signature m ((family m).mul 11 16) < m :=
  k11_original_bms_successor_bound family m ((periodAtLeast32_iff family m).mp hm.1)

/-- The same lower bound belongs to a stable index: every larger finite
table has exactly that index in row 11, column 16. -/
theorem k11_stable_bms_successor_bound (family : BinaryFamily) (m : Nat)
    (hm : (family m).mul 1 16 ≠ 0) :
    ∃ r y, NumericBMS.FiniteLevelEval 1 120 y ∧ y < r ∧ r < m ∧
      ∀ n, m ≤ n → signature n ((family n).mul 11 16) = r := by
  obtain ⟨y, hy, hb, hc⟩ := k11_original_bms_successor_bound family m hm
  refine ⟨signature m ((family m).mul 11 16), y, hy, hb, hc, ?_⟩
  intro n hmn
  exact K11.act_stable_of_unsaturated family (a := 11) (x := 4) hmn hc

#print k11_original_bms_successor_bound
#print k11_undefined_or_large
#print axioms k11_nonzero_bms_successor_bound
#print axioms k11_index_bms_successor_bound
#print axioms k11_undefined_or_large
#print axioms k11_zero_or_large
#print axioms k11_original_bms_successor_bound
#print axioms q5_k11_bms_successor_bound
#print axioms k11_stable_bms_successor_bound
end LaverLowerBounds.FiniteTable
