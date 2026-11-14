import BTnSSBMS.SiblingEntry
import BTnSSBMS.CopyKeyComparison
import BTnSSBMS.RelocationLegality

/-! A genuine common-entry theorem for sibling expressions. Earlier and
later contexts need not be equal. Moving the earlier root forward gives
an identity transport, and the two complete transports commute. -/
namespace BTnSSBMS.Parents

theorem sibling_maps {d : Nat} {source target : ParentContext} {visible : List Nat}
    (view : NumericalView d source target visible) (nextVisible : List Nat)
    (initial : visible <+: nextVisible) {later next : Nat}
    (length : nextVisible.length = later) :
    (visible ++ [target.length]).map (point (List.range target.length ++ [next])) =
      (List.range source.length ++ [later]).map (point (nextVisible ++ [next])) := by
  rw [point_composition_append view (List.range target.length) List.length_range next]
  have old : visible.map (point (List.range target.length)) = visible := by
    have eq : visible.map (point (List.range target.length)) = visible.map id := by
      apply List.map_congr_left
      intro p member
      obtain ⟨i, inside, lookup⟩ := List.getElem_of_mem member
      have bound := view.bounded i (by rw [← view.length]; exact inside)
      have actual : point visible i = p := by
        simp only [point, List.getElem?_eq_getElem inside, Option.getD_some, lookup]
      rw [actual] at bound
      exact point_range target.length p bound
    simpa only [List.map_id] using eq
  rw [old, List.map_append, List.map_cons, List.map_nil]
  have atEnd : point (nextVisible ++ [next]) later = next := by
    rw [← length, point_append_last]
  rw [atEnd]
  congr 1
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, view.length]
  · intro i left right
    have inside : i < source.length := by rw [← view.length]; exact left
    have oldInside : i < visible.length := by rw [view.length]; exact inside
    have nextInside : i < nextVisible.length := Nat.lt_of_lt_of_le oldInside initial.length_le
    simp only [List.getElem_map, List.getElem_range]
    rw [point_append_old nextVisible i next nextInside, ← point_prefix initial i oldInside]
    simp only [point, List.getElem?_eq_getElem oldInside, Option.getD_some]

end BTnSSBMS.Parents

namespace BTnSSBMS.Source

theorem relocationHead_at_shared_zero {d : Nat}
    {small large targetSmall targetLarge : ParentContext} {visible nextVisible : List Nat}
    (initial : small <+: large) (targetInitial : targetSmall <+: targetLarge)
    (visibleInitial : visible <+: nextVisible)
    (view : Parents.NumericalView d small targetSmall visible) (a : List Nat)
    (same : (Parents.label d large a).parents[0]?.join = (Parents.label d small a).parents[0]?.join) :
    relocationHead d large targetLarge nextVisible a = relocationHead d small targetSmall visible a := by
  apply List.ext_getElem
  · simp only [relocationHead_width]
  · intro row left right
    have room : row < d := by simpa only [relocationHead_width] using left
    have values : (relocationHead d large targetLarge nextVisible a)[row]?.getD 0 =
        (relocationHead d small targetSmall visible a)[row]?.getD 0 := by
      rw [relocationHead_value d large targetLarge nextVisible a room,
        relocationHead_value d small targetSmall visible a room]
      unfold Parents.representedValue
      rw [Parents.label_parents_of_shared_zero initial a same row room]
      cases selected : (Parents.label d small a).parents[row]?.join with
      | none => rfl
      | some p =>
        have bound := Parents.label_parent_bound d small a row p selected
        simp only [Option.map_some, Option.getD_some]
        rw [← Parents.point_prefix visibleInitial p (by rw [view.length]; exact bound),
          ← Parents.reading_prefix targetInitial row (Parents.point visible p) (view.bounded p bound)]
    simpa only [List.getElem?_eq_getElem left, List.getElem?_eq_getElem right, Option.getD_some] using values

/-- Identity transports on both vertical sides of a commuting square
reduce a cross-entry comparison to a single entry. This lemma is used
below with the concrete sibling views, not as a coverage assumption. -/
theorem relocate_zero_square {d : Nat}
    {source sourceNext target targetNext : ParentContext} {visible nextVisible sourceMap targetMap : List Nat}
    {sourceHistory targetHistory : List Nat} {sourceRoot targetRoot sourceCap targetCap : Nat}
    {sourceDelta targetDelta : List Nat}
    (sourceMove : ShiftView d source sourceNext sourceMap sourceHistory sourceRoot sourceCap sourceDelta 0)
    (targetMove : ShiftView d target targetNext targetMap targetHistory targetRoot targetCap targetDelta 0)
    (view : Parents.NumericalView d source target visible)
    (nextLength : nextVisible.length = sourceNext.length)
    (square : visible.map (Parents.point targetMap) = sourceMap.map (Parents.point nextVisible))
    (e : NumericalExpr) (legal : FiniteLegal d source e)
    (outputLegal : FiniteLegal d target (relocate d source target visible e)) :
    relocate d source target visible e = relocate d sourceNext targetNext nextVisible e := by
  have left := relocate_compose d e source target targetNext visible targetMap
    sourceMove.sourceCoherent sourceMove.sourceValid targetMove.sourceCoherent targetMove.sourceValid
    view targetMove.view.length
  have right := relocate_compose d e source sourceNext targetNext sourceMap nextVisible
    sourceMove.sourceCoherent sourceMove.sourceValid sourceMove.targetCoherent sourceMove.targetValid
    sourceMove.view nextLength
  rw [relocate_eq_copied targetMove _ outputLegal, copied_zero] at left
  rw [relocate_eq_copied sourceMove e legal, copied_zero] at right
  rw [left, square, ← right]

theorem relocateForests_zero_square {d : Nat}
    {source sourceNext target targetNext : ParentContext} {visible nextVisible sourceMap targetMap : List Nat}
    {sourceHistory targetHistory : List Nat} {sourceRoot targetRoot sourceCap targetCap : Nat}
    {sourceDelta targetDelta : List Nat}
    (sourceMove : ShiftView d source sourceNext sourceMap sourceHistory sourceRoot sourceCap sourceDelta 0)
    (targetMove : ShiftView d target targetNext targetMap targetHistory targetRoot targetCap targetDelta 0)
    (view : Parents.NumericalView d source target visible)
    (nextLength : nextVisible.length = sourceNext.length)
    (square : visible.map (Parents.point targetMap) = sourceMap.map (Parents.point nextVisible))
    (owner nextOwner : Nat) (hs : Forests (List Nat))
    (legal : FiniteLegalForests d source owner hs)
    (outputLegal : FiniteLegalForests d target nextOwner (relocateForests d source target visible hs)) :
    relocateForests d source target visible hs = relocateForests d sourceNext targetNext nextVisible hs := by
  have left := relocateForests_compose d hs source target targetNext visible targetMap
    sourceMove.sourceCoherent sourceMove.sourceValid targetMove.sourceCoherent targetMove.sourceValid
    view targetMove.view.length
  have right := relocateForests_compose d hs source sourceNext targetNext sourceMap nextVisible
    sourceMove.sourceCoherent sourceMove.sourceValid sourceMove.targetCoherent sourceMove.targetValid
    sourceMove.view nextLength
  rw [relocateForests_eq_copied targetMove nextOwner _ outputLegal, copiedForests_zero] at left
  rw [relocateForests_eq_copied sourceMove owner hs legal, copiedForests_zero] at right
  rw [left, square, ← right]

/-- Transporting an earlier sibling at the later entry changes no
output syntax. Higher parent rows, both identity side transports, and
the whole commuting square are derived from actual parent searches. -/
theorem relocate_at_shared_zero {d : Nat}
    {small large targetSmall targetLarge : ParentContext} {visible nextVisible : List Nat}
    (initial : small <+: large) (targetInitial : targetSmall <+: targetLarge)
    (visibleInitial : visible <+: nextVisible)
    (sourceCoherent : Parents.Coherent d large) (sourceValid : Parents.ContextValid large)
    (sourceUnit : Parents.UnitSteps d large)
    (targetCoherent : Parents.Coherent d targetLarge) (targetValid : Parents.ContextValid targetLarge)
    (targetUnit : Parents.UnitSteps d targetLarge)
    (view : Parents.NumericalView d small targetSmall visible)
    (nextView : Parents.NumericalView d large targetLarge nextVisible)
    (positive : 0 < d) (a : List Nat) (hs : Forests (List Nat)) (rest : NumericalExpr)
    (legal : FiniteLegal d small (.cons a hs rest))
    (same : (Parents.label d large a).parents[0]?.join = (Parents.label d small a).parents[0]?.join) :
    relocate d small targetSmall visible (.cons a hs rest) =
      relocate d large targetLarge nextVisible (.cons a hs rest) := by
  have smallCoherent := sourceCoherent.restrict initial
  have smallValid := sourceValid.restrict initial
  have smallTargetCoherent := targetCoherent.restrict targetInitial
  have smallTargetValid := targetValid.restrict targetInitial
  have smallTargetUnit := targetUnit.restrict targetValid targetInitial
  let head := relocationHead d small targetSmall visible a
  have headEq := relocationHead_at_shared_zero initial targetInitial visibleInitial view a same
  have newSame : (Parents.label d targetLarge head).parents[0]?.join =
      (Parents.label d targetSmall head).parents[0]?.join := by
    change (Parents.label d targetLarge (relocationHead d small targetSmall visible a)).parents[0]?.join = _
    rw [← headEq, relocationHead_parents sourceCoherent sourceValid targetCoherent targetValid nextView a 0 positive]
    change _ = (Parents.label d targetSmall (relocationHead d small targetSmall visible a)).parents[0]?.join
    rw [relocationHead_parents smallCoherent smallValid smallTargetCoherent smallTargetValid view a 0 positive, same]
    cases selected : (Parents.label d small a).parents[0]?.join with
    | none => rfl
    | some p =>
      simp only [Option.map_some]
      rw [← Parents.point_prefix visibleInitial p
        (by rw [view.length]; exact Parents.label_parent_bound d small a 0 p selected)]
  have sourceMove := sibling_shiftView initial sourceCoherent sourceValid sourceUnit a legal.2.1 same
  have targetMove := sibling_shiftView targetInitial targetCoherent targetValid targetUnit head
    (relocationHead_unitSteps smallCoherent smallValid smallTargetCoherent smallTargetValid smallTargetUnit view a) newSame
  have appended := relocation_view_append smallCoherent smallValid smallTargetCoherent smallTargetValid view a
  have outputLegal := relocate_finiteLegal d (.cons a hs rest) small targetSmall visible smallCoherent smallValid
    smallTargetCoherent smallTargetValid smallTargetUnit view positive legal
  have square := Parents.sibling_maps view nextVisible visibleInitial (next := targetLarge.length) nextView.length
  have nextLength : (nextVisible ++ [targetLarge.length]).length =
      (large ++ [Parents.label d large a]).length := by simp only [List.length_append, List.length_cons, List.length_nil, nextView.length]
  have inside := relocateForests_zero_square sourceMove targetMove appended nextLength square
    (a[0]?.getD 0) (head[0]?.getD 0) hs legal.2.2.2.1 outputLegal.2.2.2.1
  have after := relocate_zero_square sourceMove targetMove appended nextLength square rest legal.2.2.2.2 outputLegal.2.2.2.2
  simp only [relocate, headEq]
  rw [inside, after]

end BTnSSBMS.Source
