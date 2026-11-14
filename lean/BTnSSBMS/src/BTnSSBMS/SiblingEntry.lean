import BTnSSBMS.SourceSiblingGeometry
import BTnSSBMS.CopyRoot

/-! Move an earlier sibling to a later entry without altering its syntax.
The actual row-zero parent is the hypothesis; all higher parents and the
post-root numerical view are derived. Forests may have arbitrary depth. -/
namespace BTnSSBMS.Parents

theorem label_parents_of_shared_zero {d : Nat} {small large : ParentContext}
    (initial : small <+: large) (a : List Nat)
    (same : (label d large a).parents[0]?.join = (label d small a).parents[0]?.join)
    (row : Nat) (room : row < d) :
    (label d large a).parents[row]?.join = (label d small a).parents[row]?.join := by
  induction row with
  | zero => exact same
  | succ row ih =>
    rw [label_next d large a row room, label_next d small a row room, ih (by omega)]
    apply (search_prefix initial _ _ _ ?_).symm
    cases selected : (label d small a).parents[row]?.join with
    | none => simp
    | some p =>
      have bound := label_parent_bound d small a row p selected
      simp only [Option.map_some, Option.getD_some]
      omega

theorem sibling_head_unitSteps {d : Nat} {small large : ParentContext}
    (initial : small <+: large) (valid : ContextValid large)
    (unit : UnitSteps d large) (a : List Nat)
    (oldUnit : UnitSteps d (small ++ [label d small a]))
    (same : (label d large a).parents[0]?.join = (label d small a).parents[0]?.join) :
    UnitSteps d (large ++ [label d large a]) := by
  apply unit.extend_one (context_valid_append_label d large valid a)
    (List.prefix_append _ _) (by simp)
  intro row room
  rw [reading_append_label, append_label_parent, label_parents_of_shared_zero initial a same row room]
  have equation := label_unit_value a oldUnit room
  cases selected : (label d small a).parents[row]?.join with
  | none => simpa only [selected, Option.map_none, Option.getD_none] using equation
  | some p =>
    have inside := label_parent_bound d small a row p selected
    simp only [selected, Option.map_some, Option.getD_some] at equation ⊢
    rw [← reading_prefix (initial.trans (List.prefix_append _ _)) row p inside]
    exact equation

theorem sibling_numericalView {d : Nat} {small large : ParentContext}
    (initial : small <+: large) (valid : ContextValid small) (a : List Nat)
    (same : (label d large a).parents[0]?.join = (label d small a).parents[0]?.join) :
    NumericalView d (small ++ [label d small a]) (large ++ [label d large a])
      (List.range small.length ++ [large.length]) := by
  apply (numericalView_identity d small).append_stretched (label d small a)
    (context_valid_append_label d small valid a) (initial.trans (List.prefix_append _ _))
    large.length (by simp) (by simp) initial.length_le
  intro row room p selected
  rw [point_range _ p (label_parent_bound d small a row p selected)]
  apply Ancestor.up ?_ (.refl _)
  rw [append_label_parent, label_parents_of_shared_zero initial a same row room, selected]

end BTnSSBMS.Parents

namespace BTnSSBMS.Source

theorem copied_zero (d root cap : Nat) (delta : List Nat) (context : ParentContext)
    (history : List Nat) (e : NumericalExpr) :
    copied d root cap delta 0 context history e = e := by
  rw [copied_eq_ascend d root cap delta 0 context history e .nil,
    ascendReplace_nohole_zero, mark_erase, Parents.annotate_erase]

theorem sibling_shiftView {d : Nat} {small large : ParentContext}
    (initial : small <+: large) (coherent : Parents.Coherent d large)
    (valid : Parents.ContextValid large) (unit : Parents.UnitSteps d large)
    (a : List Nat) (oldUnit : Parents.UnitSteps d (small ++ [Parents.label d small a]))
    (same : (Parents.label d large a).parents[0]?.join = (Parents.label d small a).parents[0]?.join) :
    ShiftView d (small ++ [Parents.label d small a]) (large ++ [Parents.label d large a])
      (List.range small.length ++ [large.length]) (List.replicate small.length 0 ++ [0])
      small.length 0 [] 0 := by
  refine ⟨Parents.coherent_append_label (coherent.restrict initial) a,
    Parents.context_valid_append_label d small (valid.restrict initial) a,
    Parents.coherent_append_label coherent a,
    Parents.context_valid_append_label d large valid a,
    Parents.sibling_head_unitSteps initial valid unit a oldUnit same,
    Parents.sibling_numericalView initial (valid.restrict initial) a same,
    by simp, BMS.HistoryCorrect.at_root
      (Parents.context_valid_append_label d small (valid.restrict initial) a) small.length 0,
    by simp, by omega, ?_⟩
  intro p inside row room
  simp only [Nat.mul_zero, ite_self, Nat.add_zero]
  by_cases old : p < small.length
  · rw [Parents.point_append_old _ p large.length (by simpa using old), Parents.point_range _ p old,
      ← Parents.reading_prefix (List.prefix_append small _) row p old,
      ← Parents.reading_prefix (initial.trans (List.prefix_append _ _)) row p old]
  · have atRoot : p = small.length := by
      simp only [List.length_append, List.length_cons, List.length_nil] at inside
      omega
    subst p
    have atEnd : Parents.point (List.range small.length ++ [large.length]) small.length = large.length := by
      simpa only [List.length_range] using Parents.point_append_last (List.range small.length) large.length
    rw [atEnd, Parents.reading_append_label, Parents.reading_append_label]

/-- Moving an entire earlier expression after a gap is legal when its
first column still has the same computed P0 parent. This is forward
insertion, not an unverified removal of the intervening context. -/
theorem FiniteLegal.at_shared_zero {d : Nat} {small large : ParentContext}
    (initial : small <+: large) (coherent : Parents.Coherent d large)
    (valid : Parents.ContextValid large) (unit : Parents.UnitSteps d large)
    (positive : 0 < d) {a : List Nat} {hs : Forests (List Nat)} {rest : NumericalExpr}
    (legal : FiniteLegal d small (.cons a hs rest))
    (same : (Parents.label d large a).parents[0]?.join = (Parents.label d small a).parents[0]?.join) :
    FiniteLegal d large (.cons a hs rest) := by
  have scope := sibling_shiftView initial coherent valid unit a legal.2.1 same
  have usable : ShiftView d (small ++ [Parents.label d small a])
      (large ++ [Parents.label d large (shift a 0 [] 0)])
      (List.range small.length ++ [large.length]) (List.replicate small.length 0 ++ [0])
      small.length 0 [] 0 := by simpa only [shift_zero] using scope
  simpa only [copied_zero] using copied_root_finiteLegal usable positive hs rest legal

/-- Actual sibling roots supply the shared-parent condition for the
earlier head, even when their higher coordinates differ. -/
theorem FiniteLegal.at_sibling {d : Nat} {small large : ParentContext}
    (initial : small <+: large) (coherent : Parents.Coherent d large)
    (valid : Parents.ContextValid large) (positive : 0 < d)
    {a b : List Nat} {hs : Forests (List Nat)} {rest : NumericalExpr}
    (legal : FiniteLegal d small (.cons a hs rest))
    (otherUnit : Parents.UnitSteps d (large ++ [Parents.label d large b]))
    (same : (Parents.label d large b).parents[0]?.join = (Parents.label d small a).parents[0]?.join) :
    FiniteLegal d large (.cons a hs rest) := by
  have coordinate := same_zero_parent_value positive initial a b legal.2.1 otherUnit same
  apply legal.at_shared_zero initial coherent valid
    (otherUnit.restrict (Parents.context_valid_append_label d large valid b) (List.prefix_append _ _)) positive
  apply Eq.trans (Parents.label_parents_congr_through d large a b 0 positive ?_) same
  intro k bound
  have eq : k = 0 := by omega
  simpa only [eq] using coordinate.symm

end BTnSSBMS.Source
