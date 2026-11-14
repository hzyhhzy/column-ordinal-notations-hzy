import BTnSSBMS.CopyHoleDensity
import BTnSSBMS.RootCopyReset

/-! Exact composition of the actual maps at a copied terminal hole.
The root-to-hole interval is dense, so agreement at the entering root
forces agreement at every later visible position. No correspondence of
the terminal maps is postulated. -/
namespace BTnSSBMS.Parents

theorem NumericalView.composition_from_spans {d : Nat}
    {source middle target : ParentContext} {first second direct : List Nat}
    (left : NumericalView d source middle first)
    (right : NumericalView d middle target second)
    (diagonal : NumericalView d source target direct)
    {root : Nat} (inside : root < source.length)
    (leftSpan : middle.length + root = source.length + point first root)
    (directSpan : target.length + root = source.length + point direct root)
    (initial : ∀ position, position ≤ root →
      point second (point first position) = point direct position) :
    first.map (point second) = direct := by
  have rootInside := left.bounded root inside
  have rootSame := initial root (Nat.le_refl root)
  have rightSpan : target.length + point first root =
      middle.length + point second (point first root) := by omega
  apply List.ext_getElem
  · simp only [List.length_map, left.length, diagonal.length]
  · intro position lhs rhs
    have sourceInside : position < source.length := by
      simpa only [List.length_map, left.length] using lhs
    have value : point (first.map (point second)) position = point direct position := by
      rw [point_map first second position (by rw [left.length]; exact sourceInside)]
      by_cases before : position ≤ root
      · exact initial position before
      · have after : root ≤ position := by omega
        have firstValue := left.dense_from_span inside leftSpan after sourceInside
        have secondValue := right.dense_from_span rootInside rightSpan
          (position := point first position) (by omega) (left.bounded position sourceInside)
        have directValue := diagonal.dense_from_span inside directSpan after sourceInside
        omega
    simpa only [point, List.getElem?_eq_getElem lhs,
      List.getElem?_eq_getElem rhs, Option.getD_some] using value

end BTnSSBMS.Parents

namespace BTnSSBMS.Source

theorem copied_hole_map_square {d : Nat} {context target later : ParentContext} {a : List Nat}
    {visible nextVisible : List Nat} {cap : Nat} {delta : List Nat} {phase nextPhase : Nat}
    (scope : ShiftView d (context ++ [Parents.label d context a])
      (target ++ [Parents.label d target (shift a cap delta phase)]) visible
      (List.replicate context.length 0 ++ [cap]) context.length cap delta phase)
    (next : ShiftView d (context ++ [Parents.label d context a])
      (later ++ [Parents.label d later (shift a cap delta nextPhase)]) nextVisible
      (List.replicate context.length 0 ++ [cap]) context.length cap delta nextPhase)
    (entering : List Nat) (enteringLength : entering.length = target.length + 1)
    (enteringSquare : visible.map (Parents.point entering) = nextVisible)
    (hs : Forests (List Nat)) (rest : NumericalExpr) (depth : Nat)
    {site oldHole newHole : HoleSite}
    (found : holeSite d context none depth (.cons a hs rest) = some site)
    (oldFound : holeSite d target none depth
      (copied d context.length cap delta phase context (List.replicate context.length 0)
        (.cons a hs rest)) = some oldHole)
    (newFound : holeSite d later none depth
      (copied d context.length cap delta nextPhase context (List.replicate context.length 0)
        (.cons a hs rest)) = some newHole)
    (afterHead : context.length < site.context.length)
    {oldMap newMap moved : List Nat}
    (oldView : Parents.NumericalView d site.context oldHole.context oldMap)
    (newView : Parents.NumericalView d site.context newHole.context newMap)
    (between : Parents.NumericalView d oldHole.context newHole.context moved)
    (oldExtended : visible <+: oldMap) (newExtended : nextVisible <+: newMap)
    (movedExtended : entering <+: moved) :
    oldMap.map (Parents.point moved) = newMap := by
  have oldRoot : Parents.point oldMap context.length = target.length := by
    rw [← Parents.point_prefix oldExtended context.length (by rw [scope.view.length]; simp)]
    exact root_view_point scope
  have newRoot : Parents.point newMap context.length = later.length := by
    rw [← Parents.point_prefix newExtended context.length (by rw [next.view.length]; simp)]
    exact root_view_point next
  have oldSpan := copied_root_holeSite_span d cap delta phase context target a hs rest depth found oldFound
  have newSpan := copied_root_holeSite_span d cap delta nextPhase context later a hs rest depth found newFound
  apply oldView.composition_from_spans between newView afterHead
    (by rw [oldRoot]; exact oldSpan) (by rw [newRoot]; exact newSpan)
  intro position before
  have sourceInside : position < visible.length := by rw [scope.view.length]; simp; omega
  have targetInside : position < nextVisible.length := by rw [next.view.length]; simp; omega
  rw [← Parents.point_prefix oldExtended position sourceInside,
    ← Parents.point_prefix newExtended position targetInside,
    ← Parents.point_prefix movedExtended (Parents.point visible position)
      (by rw [enteringLength]; simpa only [List.length_append, List.length_cons, List.length_nil]
        using scope.view.bounded position (by simpa only [scope.view.length] using sourceInside))]
  have reset := congrArg (fun values => Parents.point values position)
    enteringSquare
  rw [Parents.point_map visible _ position sourceInside] at reset
  exact reset

theorem root_copy_hole_reset_map {d : Nat} {context target later : ParentContext} {a : List Nat}
    {visible nextVisible : List Nat} {cap : Nat} {delta : List Nat} {phase nextPhase : Nat}
    (scope : ShiftView d (context ++ [Parents.label d context a])
      (target ++ [Parents.label d target (shift a cap delta phase)]) visible
      (List.replicate context.length 0 ++ [cap]) context.length cap delta phase)
    (next : ShiftView d (context ++ [Parents.label d context a])
      (later ++ [Parents.label d later (shift a cap delta nextPhase)]) nextVisible
      (List.replicate context.length 0 ++ [cap]) context.length cap delta nextPhase)
    (fixed : nextVisible.take context.length = visible.take context.length)
    (hs : Forests (List Nat)) (rest : NumericalExpr) (depth : Nat)
    {site oldHole newHole : HoleSite}
    (found : holeSite d context none depth (.cons a hs rest) = some site)
    (oldFound : holeSite d target none depth
      (copied d context.length cap delta phase context (List.replicate context.length 0)
        (.cons a hs rest)) = some oldHole)
    (newFound : holeSite d later none depth
      (copied d context.length cap delta nextPhase context (List.replicate context.length 0)
        (.cons a hs rest)) = some newHole)
    (afterHead : context.length < site.context.length)
    {oldMap newMap moved : List Nat}
    (oldView : Parents.NumericalView d site.context oldHole.context oldMap)
    (newView : Parents.NumericalView d site.context newHole.context newMap)
    (between : Parents.NumericalView d oldHole.context newHole.context moved)
    (oldExtended : visible <+: oldMap) (newExtended : nextVisible <+: newMap)
    (movedExtended : List.range target.length ++ [later.length] <+: moved) :
    oldMap.map (Parents.point moved) = newMap :=
  copied_hole_map_square scope next (List.range target.length ++ [later.length])
    (by simp) (root_views_reset_map scope next fixed) hs rest depth found oldFound newFound
    afterHead oldView newView between oldExtended newExtended movedExtended

end BTnSSBMS.Source
