import BTnSSBMS.CopyMaterialNaturality

/-! The two finite coherence facts used when passing a paired copy
transport through its next seam: protected parent equations survive
prefix growth, and the two actual reset maps still commute. -/
namespace BTnSSBMS.Parents

theorem parent_transport_extends {d root row : Nat}
    {source sourceNext target targetNext : ParentContext} {visible nextVisible : List Nat}
    (view : NumericalView d source target visible) (valid : ContextValid source)
    (inside : root < source.length)
    (exactAt : parent target row (point visible root) =
      (parent source row root).map (point visible))
    (sourcePrefix : source <+: sourceNext) (targetPrefix : target <+: targetNext)
    (visiblePrefix : visible <+: nextVisible) :
    parent targetNext row (point nextVisible root) =
      (parent sourceNext row root).map (point nextVisible) := by
  rw [← point_prefix visiblePrefix root (by rw [view.length]; exact inside),
    ← parent_prefix_eq targetPrefix row (point visible root) (view.bounded root inside),
    ← parent_prefix_eq sourcePrefix row root inside, exactAt]
  cases selected : parent source row root with
  | none => rfl
  | some p =>
    simp only [Option.map_some]
    rw [← point_prefix visiblePrefix p (by
      rw [view.length]
      have earlier := parent_earlier valid selected
      omega)]

theorem reset_composition_square {d : Nat} {source middle : ParentContext}
    {first second direct : List Nat}
    (view : NumericalView d source middle first) (length : second.length = middle.length)
    (square : first.map (point second) = direct) (root next : Nat) :
    (first.take root ++ [middle.length]).map (point (second ++ [next])) =
      direct.take root ++ [next] := by
  rw [List.map_append, List.map_take]
  have old : first.map (point (second ++ [next])) = direct := by
    rw [← square]
    apply List.map_congr_left
    intro p member
    obtain ⟨position, inside, lookup⟩ := List.getElem_of_mem member
    have bound := view.bounded position (by rw [← view.length]; exact inside)
    have value : point first position = p := by
      simp only [point, List.getElem?_eq_getElem inside, Option.getD_some, lookup]
    rw [value] at bound
    exact point_append_old second p next (by omega)
  rw [old]
  simp only [List.map_cons, List.map_nil, ← length, point_append_last]

end BTnSSBMS.Parents
