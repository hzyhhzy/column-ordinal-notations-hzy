import BTnSSBMS.ExactAncestryReflection

/-!
A path from the gap before a restarted root into an exact copied suffix
must pass through that root. Ordinary parents cannot jump into the gap:
they are mapped source parents, and the old source prefix is below it.
-/
namespace BTnSSBMS.Parents

theorem NumericalView.gap_ancestor_through_root {d : Nat}
    {source target : ParentContext} {visible : List Nat}
    (view : NumericalView d source target visible)
    (sourceValid : ContextValid source) (targetValid : ContextValid target)
    {root earlier row : Nat} (room : row < d)
    (exactAt : ∀ position, root < position → position < source.length →
      ExactPosition d source target visible position)
    (gap : ∀ position, position < root → point visible position < earlier)
    (before : earlier < point visible root)
    {endpoint : Nat} (after : root ≤ endpoint) (inside : endpoint < source.length)
    (path : Ancestor target row earlier (point visible endpoint)) :
    Ancestor target row (point visible root) (point visible endpoint) := by
  induction endpoint using Nat.strongRecOn with
  | ind endpoint ih =>
    by_cases same : endpoint = root
    · subst endpoint
      exact .refl _
    · have strict : root < endpoint := by omega
      have forward := view.increasing root endpoint strict inside
      have different : earlier ≠ point visible endpoint := by omega
      obtain ⟨p, edge, previous⟩ := (Ancestor.iff_parent different).mp path
      have transported := exactAt endpoint strict inside row room
      rw [transported] at edge
      cases selected : parent source row endpoint with
      | none => simp only [selected, Option.map_none] at edge; cases edge
      | some q =>
        have pointEq : point visible q = p := by
          simpa only [selected, Option.map_some, Option.some.injEq] using edge
        rw [← pointEq] at previous
        have qEarlier := parent_earlier sourceValid selected
        have qAfter : root ≤ q := by
          by_cases afterRoot : root ≤ q
          · exact afterRoot
          · have fixedPrefix := gap q (by omega)
            have pathOrder := previous.le targetValid
            omega
        have rootPath := ih q qEarlier qAfter (by omega) previous
        exact Ancestor.up (by rw [transported, selected, Option.map_some]) rootPath

/-- The reset view produced by the real restart supplies the gap
inequalities. Old and new source scopes may have different lengths. -/
theorem NumericalView.restarted_gap_path {d : Nat}
    {oldSource oldTarget source target : ParentContext} {oldVisible visible : List Nat}
    (oldView : NumericalView d oldSource oldTarget oldVisible)
    (nextView : NumericalView d source target visible)
    (sourceValid : ContextValid source) (targetValid : ContextValid target)
    {root earlier row : Nat} (afterRoot : root < earlier) (earlierInside : earlier < oldSource.length)
    (room : row < d)
    (exactAt : ∀ position, root < position → position < source.length →
      ExactPosition d source target visible position)
    (initial : oldVisible.take root ++ [oldTarget.length] <+: visible)
    {endpoint : Nat} (after : root ≤ endpoint) (inside : endpoint < source.length)
    (path : Ancestor target row (point oldVisible earlier) (point visible endpoint)) :
    Ancestor target row oldTarget.length (point visible endpoint) := by
  have prefixLength : (oldVisible.take root).length = root := by
    simp only [List.length_take, oldView.length]
    omega
  have rootPoint : point visible root = oldTarget.length := by
    rw [← point_prefix initial root (by simp only [List.length_append, prefixLength,
      List.length_cons, List.length_nil]; omega)]
    simpa only [prefixLength] using point_append_last (oldVisible.take root) oldTarget.length
  have gap : ∀ position, position < root → point visible position < point oldVisible earlier := by
    intro position before
    have initialBound : position < (oldVisible.take root ++ [oldTarget.length]).length := by
      simp only [List.length_append, prefixLength, List.length_cons, List.length_nil]
      omega
    have fixedBound : position < (oldVisible.take root).length := by rw [prefixLength]; exact before
    rw [← point_prefix initial position initialBound,
      point_append_old _ position oldTarget.length fixedBound,
      point_take oldVisible root position before]
    exact oldView.increasing position earlier (by omega) earlierInside
  have barrierPath := nextView.gap_ancestor_through_root sourceValid targetValid room exactAt gap
    (by rw [rootPoint]; exact oldView.bounded earlier earlierInside) after inside path
  simpa only [rootPoint] using barrierPath

end BTnSSBMS.Parents
