import BTnSSBMS.CopyHoleSpan
import BTnSSBMS.NumericalViewDensity
import BTnSSBMS.ExactCopyHole

/-! Actual hole spans force every compatible scoped numerical view to
cover the complete root-to-hole interval. No target positions are skipped. -/
namespace BTnSSBMS.Source

theorem copied_root_hole_density {d : Nat} {context target : ParentContext} {a : List Nat}
    {visible : List Nat} {cap : Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d (context ++ [Parents.label d context a])
      (target ++ [Parents.label d target (shift a cap delta phase)]) visible
      (List.replicate context.length 0 ++ [cap]) context.length cap delta phase)
    (hs : Forests (List Nat)) (rest : NumericalExpr) (depth : Nat) {site targetSite : HoleSite}
    (found : holeSite d context none depth (.cons a hs rest) = some site)
    (targetFound : holeSite d target none depth
      (copied d context.length cap delta phase context (List.replicate context.length 0)
        (.cons a hs rest)) = some targetSite)
    (later : context.length < site.context.length) {holeVisible : List Nat}
    (view : Parents.NumericalView d site.context targetSite.context holeVisible)
    (extended : visible <+: holeVisible) :
    Parents.point holeVisible context.length = target.length ∧
    (∀ position, context.length ≤ position → position < site.context.length →
      Parents.point holeVisible position = target.length + (position - context.length)) ∧
    (∀ position, target.length ≤ position → position < targetSite.context.length →
      ∃ sourcePosition, context.length ≤ sourcePosition ∧ sourcePosition < site.context.length ∧
        Parents.point holeVisible sourcePosition = position) := by
  have rootPoint : Parents.point holeVisible context.length = target.length := by
    rw [← Parents.point_prefix extended context.length (by rw [scope.view.length]; simp)]
    exact root_view_point scope
  have sizes := copied_root_holeSite_span d cap delta phase context target a hs rest depth found targetFound
  have span : targetSite.context.length + context.length =
      site.context.length + Parents.point holeVisible context.length := by
    rw [rootPoint]
    exact sizes
  refine ⟨rootPoint, ?_, ?_⟩
  · intro position after inside
    simpa only [rootPoint] using view.dense_from_span later span after inside
  · intro position after inside
    apply view.surjective_from_span later span (position := position) ?_ inside
    simpa only [rootPoint] using after

end BTnSSBMS.Source
