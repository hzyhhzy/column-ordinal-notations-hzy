import BTnSSBMS.CopyRunGeometry
import BTnSSBMS.PartialRebaseMaterial

/-! Reset-map composition and the exact mixed head for two forced
copy roots. These finite identities prepare complete rooted-material
transport; they do not supply a source block inequality. -/
namespace BTnSSBMS.Source

theorem root_views_reset_map {d : Nat} {context target later : ParentContext} {a : List Nat}
    {visible nextVisible : List Nat} {cap : Nat} {delta : List Nat} {phase nextPhase : Nat}
    (scope : ShiftView d (context ++ [Parents.label d context a])
      (target ++ [Parents.label d target (shift a cap delta phase)]) visible
      (List.replicate context.length 0 ++ [cap]) context.length cap delta phase)
    (next : ShiftView d (context ++ [Parents.label d context a])
      (later ++ [Parents.label d later (shift a cap delta nextPhase)]) nextVisible
      (List.replicate context.length 0 ++ [cap]) context.length cap delta nextPhase)
    (fixed : nextVisible.take context.length = visible.take context.length) :
    visible.map (Parents.point (List.range target.length ++ [later.length])) = nextVisible := by
  apply List.ext_getElem
  · simp only [List.length_map, scope.view.length, next.view.length]
  · intro position left right
    have oldInside : position < visible.length := by simpa only [List.length_map] using left
    have sourceInside : position < context.length + 1 := by
      simpa only [scope.view.length, List.length_append, List.length_cons, List.length_nil] using oldInside
    have value : Parents.point (visible.map (Parents.point (List.range target.length ++ [later.length]))) position =
        Parents.point nextVisible position := by
      rw [Parents.point_map visible _ position oldInside]
      by_cases before : position < context.length
      · have oldBound : Parents.point visible position < target.length := by
          rw [← root_view_point scope]
          exact scope.view.increasing position context.length before (by simp)
        rw [Parents.point_append_old _ (Parents.point visible position) later.length (by simpa using oldBound),
          Parents.point_range target.length (Parents.point visible position) oldBound,
          ← Parents.point_take nextVisible context.length position before, fixed,
          Parents.point_take visible context.length position before]
      · have last : position = context.length := by omega
        subst position
        rw [root_view_point scope, root_view_point next]
        simpa only [List.length_range] using Parents.point_append_last (List.range target.length) later.length
    simpa only [Parents.point, List.getElem?_eq_getElem left, List.getElem?_eq_getElem right, Option.getD_some] using value

theorem root_prefix_coordinates {d : Nat} {target later : ParentContext} {head : List Nat}
    (initial : target ++ [Parents.label d target head] <+: later) :
    (later[target.length]?.getD default).coordinates = head := by
  have same := (List.prefix_iff_getElem?.mp initial) target.length (by simp)
  rw [same]
  simp only [Option.getD_some, List.getElem_append_right (Nat.le_refl target.length),
    Nat.sub_self, List.getElem_cons_zero, Parents.label]

theorem root_copy_partial_head {d : Nat} {target later : ParentContext} {a : List Nat}
    {cap : Nat} {delta : List Nat} {phase nextPhase : Nat}
    (coherent : Parents.Coherent d later) (width : a.length = d)
    (positive : 0 < cap) (room : cap < d)
    (initial : target ++ [Parents.label d target (shift a cap delta phase)] <+: later)
    (path : Parents.Ancestor (later ++ [Parents.label d later (shift a cap delta nextPhase)])
      (cap - 1) target.length later.length) :
    partialHead later target.length cap (shift a cap delta nextPhase) = shift a cap delta nextPhase := by
  have inside : target.length < later.length := by
    have bound := initial.length_le
    simp only [List.length_append, List.length_cons, List.length_nil] at bound
    omega
  have coordinates := root_prefix_coordinates initial
  have oldWidth : (later[target.length]?.getD default).coordinates.length = d := by
    rw [coordinates, shift_width, width]
  have values := partialHead_values coherent (shift a cap delta nextPhase) positive room inside path oldWidth
  apply List.ext_getElem
  · rw [partialHead_width, oldWidth, shift_width, width]
  · intro row left right
    have rowRoom : row < d := by simpa only [shift_width, width] using right
    have value : (partialHead later target.length cap (shift a cap delta nextPhase))[row]?.getD 0 =
        (shift a cap delta nextPhase)[row]?.getD 0 := by
      by_cases low : row < cap
      · exact values.1 row low
      · rw [values.2 row (by omega) rowRoom]
        change (later[target.length]?.getD default).coordinates[row]?.getD 0 = _
        rw [coordinates, shift_unshifted_row _ _ _ _ _ (by omega) (by rw [width]; exact rowRoom),
          shift_unshifted_row _ _ _ _ _ (by omega) (by rw [width]; exact rowRoom)]
    simpa only [List.getElem?_eq_getElem left, List.getElem?_eq_getElem right, Option.getD_some] using value

end BTnSSBMS.Source
