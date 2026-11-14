import BTnSSBMS.SiblingRelocation
import BTnSSBMS.RelocationBlocks

/-! Complete sibling-block comparison at different entries. Equality
of actual target zero-parents is reflected back to the source; the
shared-source-entry theorem then supplies a full, not head-only, order
comparison. -/
namespace BTnSSBMS.Source

theorem relocated_zero_parent_reflect {d : Nat}
    {small large targetSmall targetLarge : ParentContext} {visible nextVisible : List Nat}
    (initial : small <+: large) (visibleInitial : visible <+: nextVisible)
    (sourceCoherent : Parents.Coherent d large) (sourceValid : Parents.ContextValid large)
    (targetSmallCoherent : Parents.Coherent d targetSmall) (targetSmallValid : Parents.ContextValid targetSmall)
    (targetCoherent : Parents.Coherent d targetLarge) (targetValid : Parents.ContextValid targetLarge)
    (view : Parents.NumericalView d small targetSmall visible)
    (nextView : Parents.NumericalView d large targetLarge nextVisible)
    (positive : 0 < d) (a b : List Nat)
    (same : (Parents.label d targetLarge (relocationHead d large targetLarge nextVisible b)).parents[0]?.join =
      (Parents.label d targetSmall (relocationHead d small targetSmall visible a)).parents[0]?.join) :
    (Parents.label d large b).parents[0]?.join = (Parents.label d small a).parents[0]?.join := by
  rw [relocationHead_parents sourceCoherent sourceValid targetCoherent targetValid nextView b 0 positive,
    relocationHead_parents (sourceCoherent.restrict initial) (sourceValid.restrict initial)
      targetSmallCoherent targetSmallValid view a 0 positive] at same
  cases right : (Parents.label d small a).parents[0]?.join with
  | none =>
    cases left : (Parents.label d large b).parents[0]?.join with
    | none => rfl
    | some p => simp [right, left] at same
  | some q =>
    cases left : (Parents.label d large b).parents[0]?.join with
    | none => simp [right, left] at same
    | some p =>
      have pBound := Parents.label_parent_bound d large b 0 p left
      have qBound := Parents.label_parent_bound d small a 0 q right
      simp only [left, right, Option.map_some, Option.some.injEq] at same
      rw [Parents.point_prefix visibleInitial q (by rw [view.length]; exact qBound)] at same
      have qLarge : q < large.length := Nat.lt_of_lt_of_le qBound initial.length_le
      have pq := (nextView.point_le_iff pBound qLarge).mp (Nat.le_of_eq same)
      have qp := (nextView.point_le_iff qLarge pBound).mp (Nat.le_of_eq same.symm)
      have eq : p = q := by omega
      simp only [eq]

theorem relocate_sibling_blocks_compare {d : Nat}
    {small large targetSmall targetLarge : ParentContext} {visible nextVisible : List Nat}
    (initial : small <+: large) (targetInitial : targetSmall <+: targetLarge)
    (visibleInitial : visible <+: nextVisible)
    (sourceCoherent : Parents.Coherent d large) (sourceValid : Parents.ContextValid large)
    (targetCoherent : Parents.Coherent d targetLarge) (targetValid : Parents.ContextValid targetLarge)
    (targetUnit : Parents.UnitSteps d targetLarge)
    (view : Parents.NumericalView d small targetSmall visible)
    (nextView : Parents.NumericalView d large targetLarge nextVisible)
    (positive : 0 < d) (a b : List Nat) (hs ks : Forests (List Nat)) (rest tail : NumericalExpr)
    (oldLegal : FiniteLegal d small (.cons a hs rest))
    (newLegal : FiniteLegal d large (.cons b ks tail))
    (same : (Parents.label d large b).parents[0]?.join = (Parents.label d small a).parents[0]?.join) :
    (rootBlock (relocate d large targetLarge nextVisible (.cons b ks tail))).compare (listCompare Ord.compare)
        (rootBlock (relocate d small targetSmall visible (.cons a hs rest))) =
      (rootBlock (.cons b ks tail)).compare (listCompare Ord.compare) (rootBlock (.cons a hs rest)) := by
  have oldBlockLegal := rootBlock_finiteLegal oldLegal
  have newBlockLegal := rootBlock_finiteLegal newLegal
  have commonLegal := oldBlockLegal.at_sibling initial sourceCoherent sourceValid positive newLegal.2.1 same
  have sourceUnit := newLegal.2.1.restrict
    (Parents.context_valid_append_label d large sourceValid b) (List.prefix_append _ _)
  have coordinate := same_zero_parent_value positive initial a b oldLegal.2.1 newLegal.2.1 same
  have shared : (Parents.label d large a).parents[0]?.join = (Parents.label d small a).parents[0]?.join := by
    apply Eq.trans (Parents.label_parents_congr_through d large a b 0 positive ?_) same
    intro k bound
    have eq : k = 0 := by omega
    simpa only [eq] using coordinate.symm
  have aligned := relocate_at_shared_zero initial targetInitial visibleInitial sourceCoherent sourceValid sourceUnit
    targetCoherent targetValid targetUnit view nextView positive a hs (takeAbove (a[0]?.getD 0) rest) oldBlockLegal shared
  change relocate d small targetSmall visible (rootBlock (.cons a hs rest)) =
    relocate d large targetLarge nextVisible (rootBlock (.cons a hs rest)) at aligned
  rw [← relocate_rootBlock d (.cons b ks tail) large targetLarge nextVisible sourceCoherent sourceValid
      targetCoherent targetValid nextView positive newLegal,
    ← relocate_rootBlock d (.cons a hs rest) small targetSmall visible
      (sourceCoherent.restrict initial) (sourceValid.restrict initial)
      (targetCoherent.restrict targetInitial) (targetValid.restrict targetInitial) view positive oldLegal,
    aligned]
  exact relocate_compare d (rootBlock (.cons b ks tail)) (rootBlock (.cons a hs rest))
    large targetLarge nextVisible sourceCoherent sourceValid targetCoherent targetValid nextView newBlockLegal commonLegal

theorem copied_sibling_blocks_compare {d : Nat}
    {small large targetSmall targetLarge : ParentContext} {visible nextVisible history nextHistory : List Nat}
    {root cap : Nat} {delta : List Nat} {phase : Nat}
    (oldScope : ShiftView d small targetSmall visible history root cap delta phase)
    (newScope : ShiftView d large targetLarge nextVisible nextHistory root cap delta phase)
    (initial : small <+: large) (targetInitial : targetSmall <+: targetLarge)
    (visibleInitial : visible <+: nextVisible) (positive : 0 < d)
    (a b : List Nat) (hs ks : Forests (List Nat)) (rest tail : NumericalExpr)
    (oldLegal : FiniteLegal d small (.cons a hs rest))
    (newLegal : FiniteLegal d large (.cons b ks tail))
    (same : (Parents.label d large b).parents[0]?.join = (Parents.label d small a).parents[0]?.join) :
    (rootBlock (copied d root cap delta phase large nextHistory (.cons b ks tail))).compare (listCompare Ord.compare)
        (rootBlock (copied d root cap delta phase small history (.cons a hs rest))) =
      (rootBlock (.cons b ks tail)).compare (listCompare Ord.compare) (rootBlock (.cons a hs rest)) := by
  rw [← relocate_eq_copied newScope _ newLegal, ← relocate_eq_copied oldScope _ oldLegal]
  exact relocate_sibling_blocks_compare initial targetInitial visibleInitial newScope.sourceCoherent newScope.sourceValid
    newScope.targetCoherent newScope.targetValid newScope.targetUnit oldScope.view newScope.view positive a b hs ks rest tail
    oldLegal newLegal same

end BTnSSBMS.Source
