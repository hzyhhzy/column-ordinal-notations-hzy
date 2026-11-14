import BTnSSBMS.ExactCopyBarrierPath
import BTnSSBMS.CopyHoleRun

/-! Gap-path reflection after arbitrarily many restarts. The fixed
pre-root prefix is retained, but the new root may occur much later
than the first restart. -/
namespace BTnSSBMS.Parents

theorem NumericalView.later_gap_path {d : Nat}
    {oldSource oldTarget source target : ParentContext} {oldVisible visible : List Nat}
    (oldView : NumericalView d oldSource oldTarget oldVisible)
    (nextView : NumericalView d source target visible)
    (sourceValid : ContextValid source) (targetValid : ContextValid target)
    {root earlier row : Nat} (afterRoot : root < earlier) (earlierInside : earlier < oldSource.length)
    (room : row < d)
    (exactAt : ∀ position, root < position → position < source.length →
      ExactPosition d source target visible position)
    (fixed : visible.take root = oldVisible.take root)
    (laterRoot : oldTarget.length ≤ point visible root)
    {endpoint : Nat} (after : root ≤ endpoint) (inside : endpoint < source.length)
    (path : Ancestor target row (point oldVisible earlier) (point visible endpoint)) :
    Ancestor target row (point visible root) (point visible endpoint) := by
  have gap : ∀ position, position < root → point visible position < point oldVisible earlier := by
    intro position before
    rw [← point_take visible root position before, fixed, point_take oldVisible root position before]
    exact oldView.increasing position earlier (by omega) earlierInside
  have before : point oldVisible earlier < point visible root :=
    Nat.lt_of_lt_of_le (oldView.bounded earlier earlierInside) laterRoot
  exact nextView.gap_ancestor_through_root sourceValid targetValid room exactAt gap before after inside path

end BTnSSBMS.Parents
