import K11.Feedback
import K11.Counting
import K11.Stability

set_option autoImplicit false
namespace LaverLowerBounds

theorem ParentBMS.RelIter.prepend {R : Nat → Nat → Prop} {n x z y : Nat}
    (first : R x z) (tail : ParentBMS.RelIter R n z y) :
    ParentBMS.RelIter R (n + 1) x y := by
  induction tail with
  | zero z => exact .step (.zero x) first
  | step _ last ih => exact .step (ih first) last

namespace FiniteTable.K11.Entrance
open ParentBMS
variable {family : BinaryFamily} {m : Nat}

/-- Each consumed actual segment realizes one base-level FGH computation
and regenerates a fan large enough for the next one. -/
theorem iterate_feedback (e : Entrance family m) {n a b : Nat}
    (line : Lined family m e.bg.k n a b) :
    ∀ {h x}, (old : OwnedFan family m h) → 4 ≤ x → rowBudget x ≤ h →
      e.zeta ≤ a → old.fan.endpoint < a →
      ∃ y h', ∃ next : OwnedFan family m h',
        RelIter LambdaEval n x y ∧ 4 ≤ y ∧ rowBudget y ≤ h' ∧ next.fan.endpoint < b := by
  induction line with
  | nil _ =>
    intro h x old hx hrow hz hc
    exact ⟨x, h, old, .zero x, hx, hrow, hc⟩
  | @cons n a b c Q hQ hQa hQb hab tail ih =>
    intro h x old hx hrow hz hc
    obtain ⟨z, hzEval, hzRow⟩ := buffered_fgh_of_fan old.fan hx hrow
    have growth := FastEval.growth hzEval
    have oldHeight : 3 ≤ h := by have := rowBudget_ge x; omega
    have newHeight : 2 ≤ Nat.log2 (tripleCount h) := by
      have := rowBudget_ge z
      omega
    have bcap : b < m := Nat.lt_of_le_of_lt tail.endpoints.1 tail.endpoints.2
    obtain ⟨next, hnext⟩ := e.feedback hQ hQa hQb hz bcap old oldHeight hc newHeight
    obtain ⟨y, h', final, run, hy, hbudget, hfinal⟩ :=
      ih next (by omega) hzRow (by omega) hnext
    exact ⟨y, h', final, run.prepend hzEval, hy, hbudget, hfinal⟩

end FiniteTable.K11.Entrance

namespace FiniteTable.K11
open ParentBMS

/-- Numerical conclusion for an actual entrance constructed below k11. -/
theorem bms_successor_120_from_entrance {family : BinaryFamily} {m : Nat}
    (e : Entrance family m) :
    ∃ y, NumericBMS.FiniteLevelEval 1 120 y ∧ y < act family m 11 4 := by
  obtain ⟨a, initial, suffix⟩ := e.line.split (p := 131) (by decide)
  obtain ⟨fan, hfan⟩ := e.bg.line_to_fan initial (by decide)
    (by have := e.xi_eta; have := e.eta_zeta; omega)
  have start : e.zeta ≤ a := initial.endpoints.1
  obtain ⟨y, h, final, run, _, hrow, hfinal⟩ :=
    e.iterate_feedback suffix fan (x := 120) (by decide) (by decide) start hfan
  have actual : NumericBMS.FiniteLevelEval 1 120 y :=
    (NumericBMS.finiteLevelEval_iff 1 120 y).mpr run
  have last : 2 * (h + 1) + 1 ≤ final.fan.endpoint := final.fan.chain.index_le (Nat.le_refl _)
  have bound := rowBudget_ge y
  have target := e.target
  exact ⟨y, actual, by omega⟩

/-- Existence of the k11 index itself is sufficient. Enlarging the finite
cap to at least 9 preserves the index and supplies the fixed low products;
no first-row period threshold is used. -/
theorem bms_successor_120_of_unsaturated (family : BinaryFamily) (m : Nat)
    (ht : act family m 11 4 < m) :
    ∃ y, NumericBMS.FiniteLevelEval 1 120 y ∧ y < act family m 11 4 := by
  let n := max m 9
  have hmn : m ≤ n := Nat.le_max_left _ _
  have h9 : 9 ≤ n := Nat.le_max_right _ _
  have stable := act_stable_of_unsaturated family hmn ht
  have hn : act family n 11 4 < n := by omega
  obtain ⟨y, hy, hb⟩ := bms_successor_120_from_entrance (entrance_of_unsaturated family n h9 hn)
  exact ⟨y, hy, by omega⟩

/-- Compatibility with the earlier, stronger period-32 premise. -/
theorem bms_successor_120 (family : BinaryFamily) (m : Nat)
    (hm : PeriodAtLeast32 (family m)) :
    ∃ y, NumericBMS.FiniteLevelEval 1 120 y ∧ y < act family m 11 4 :=
  bms_successor_120_of_unsaturated family m (k_four_unsaturated family m hm)

/-- The bound applies to the unique value of the explicit numeric BM4 FGH. -/
theorem bms_successor_120_bound (family : BinaryFamily) (m y : Nat)
    (hm : PeriodAtLeast32 (family m)) (hy : NumericBMS.FiniteLevelEval 1 120 y) :
    y < act family m 11 4 := by
  obtain ⟨z, hz, hb⟩ := bms_successor_120 family m hm
  have he := ParentBMS.finiteLevelEval_unique 1 120 y z
    ((NumericBMS.finiteLevelEval_iff 1 120 y).mp hy)
    ((NumericBMS.finiteLevelEval_iff 1 120 z).mp hz)
  omega

#print axioms bms_successor_120
#print axioms bms_successor_120_of_unsaturated
#print axioms bms_successor_120_bound
end FiniteTable.K11
end LaverLowerBounds
