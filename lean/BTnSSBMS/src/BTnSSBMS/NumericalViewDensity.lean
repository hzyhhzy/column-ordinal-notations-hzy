import BTnSSBMS.ExactNumericalPosition

/-! A strictly increasing visible map with matching remaining interval
lengths has no holes. This converts represented-position statements to
statements about every target position in that interval. -/
namespace BTnSSBMS.Parents

theorem NumericalView.distance_le {d : Nat} {source target : ParentContext} {visible : List Nat}
    (view : NumericalView d source target visible) {first last : Nat}
    (ordered : first ≤ last) (inside : last < source.length) :
    point visible first + (last - first) ≤ point visible last := by
  induction last with
  | zero =>
    have same : first = 0 := by omega
    subst first
    simp
  | succ last ih =>
    by_cases same : first = last + 1
    · subst first
      simp
    · have earlier : first ≤ last := by omega
      have prior := ih earlier (by omega)
      have next := view.increasing last (last + 1) (by omega) inside
      omega

theorem NumericalView.dense_from_span {d : Nat} {source target : ParentContext} {visible : List Nat}
    (view : NumericalView d source target visible) {root : Nat} (rootInside : root < source.length)
    (span : target.length + root = source.length + point visible root)
    {position : Nat} (after : root ≤ position) (inside : position < source.length) :
    point visible position = point visible root + (position - root) := by
  have lower := view.distance_le after inside
  have upper := view.distance_le (first := position) (last := source.length - 1) (by omega) (by omega)
  have nonempty : source ≠ [] := by intro empty; simp [empty] at rootInside
  have last := view.frontier nonempty
  omega

theorem NumericalView.surjective_from_span {d : Nat} {source target : ParentContext} {visible : List Nat}
    (view : NumericalView d source target visible) {root : Nat} (rootInside : root < source.length)
    (span : target.length + root = source.length + point visible root)
    {position : Nat} (after : point visible root ≤ position) (inside : position < target.length) :
    ∃ sourcePosition, root ≤ sourcePosition ∧ sourcePosition < source.length ∧
      point visible sourcePosition = position := by
  let sourcePosition := root + (position - point visible root)
  have sourceAfter : root ≤ sourcePosition := by omega
  have sourceInside : sourcePosition < source.length := by omega
  refine ⟨sourcePosition, sourceAfter, sourceInside, ?_⟩
  rw [view.dense_from_span rootInside span sourceAfter sourceInside]
  omega

end BTnSSBMS.Parents
