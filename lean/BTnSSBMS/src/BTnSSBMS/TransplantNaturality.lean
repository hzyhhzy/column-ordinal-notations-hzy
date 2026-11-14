import BTnSSBMS.RelocationLegality
import BTnSSBMS.CopySeam

/-!
A commuting square for complete attached forests. Moving an earlier
highest-row ancestor's attachment to the final visible column commutes
with numerical transport. The two composed position maps are proved
equal, and composition identifies the entire finite syntax.
-/
namespace BTnSSBMS.Parents

theorem NumericalView.prefix_at {d : Nat} {source target : ParentContext} {visible : List Nat}
    (view : NumericalView d source target visible) (targetValid : ContextValid target)
    (root : Nat) (insideRoot : root < source.length) :
    NumericalView d (source.take (root + 1)) (target.take (point visible root + 1))
      (visible.take (root + 1)) := by
  have sourceLength : (source.take (root + 1)).length = root + 1 := by simp only [List.length_take]; omega
  have targetLength : (target.take (point visible root + 1)).length = point visible root + 1 := by
    have bound := view.bounded root insideRoot
    simp only [List.length_take]; omega
  refine ⟨by simp only [List.length_take, view.length], ?_, ?_, ?_, ?_⟩
  · intro p inside
    rw [point_take visible (root + 1) p (by omega), targetLength]
    have earlier := (view.point_le_iff (by omega) insideRoot).mpr (by omega : p ≤ root)
    omega
  · intro j room p q pBound qBound path
    rw [point_take visible (root + 1) p (by omega), point_take visible (root + 1) q (by omega)]
    have lifted := view.lift j room p q (by omega) (by omega) (path.prefix (List.take_prefix ..))
    apply lifted.restrict (List.take_prefix ..) targetValid
    rw [targetLength]
    have earlier := (view.point_le_iff (by omega) insideRoot).mpr (by omega : q ≤ root)
    omega
  · intro _
    rw [sourceLength, Nat.add_sub_cancel, point_take visible (root + 1) root (by omega), targetLength]
  · intro p q earlier inside
    rw [point_take visible (root + 1) p (by omega), point_take visible (root + 1) q (by omega)]
    exact view.increasing p q earlier (by omega)

theorem ancestor_to_last_view {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context) (positive : 0 < d)
    {root : Nat} (before : root < context.length - 1)
    (path : Ancestor context (d - 1) root (context.length - 1)) :
    NumericalView d (context.take (root + 1)) context (List.range root ++ [context.length - 1]) := by
  have bound : root < context.length := by omega
  have length : (context.take root).length = root := by simp only [List.length_take]; omega
  have divided := List.take_succ_eq_append_getElem bound
  have view := numericalView_identity d (context.take root)
  rw [length] at view
  rw [divided]
  apply view.append_stretched context[root]
    (by rw [← divided]; exact valid.restrict (List.take_prefix ..))
    (List.take_prefix root context) (context.length - 1) (by omega) (by omega) (by omega)
  intro j room p edge
  have actual : parent context j root = some p := by
    simpa only [parent, List.getElem?_eq_getElem bound, Option.bind_some] using edge
  have earlier := parent_earlier valid actual
  rw [point_range root p earlier]
  exact (Ancestor.up actual (.refl _)).trans (path.lower_row coherent (by omega : d - 1 < d) (by omega))

private theorem range_map_point (visible : List Nat) (count : Nat) (bound : count ≤ visible.length) :
    (List.range count).map (point visible) = visible.take count := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_take, Nat.min_eq_left bound]
  · intro j left right
    have room : j < count := by simpa only [List.length_map, List.length_range] using left
    simp only [List.getElem_map, List.getElem_range, point, List.getElem?_eq_getElem (by omega : j < visible.length),
      Option.getD_some, List.getElem_take]

theorem NumericalView.transplant_maps {d : Nat} {source target : ParentContext} {visible : List Nat}
    (view : NumericalView d source target visible) {root : Nat} (before : root < source.length - 1) :
    (List.range root ++ [source.length - 1]).map (point visible) =
      (visible.take (root + 1)).map (point (List.range (point visible root) ++ [target.length - 1])) := by
  have inside : root < source.length := by omega
  have nonempty : source ≠ [] := by intro empty; simp only [empty, List.length_nil] at inside; omega
  have final := view.frontier nonempty
  have last : point visible (source.length - 1) = target.length - 1 := by omega
  have visibleRoot : root < visible.length := by rw [view.length]; exact inside
  rw [List.map_append, List.map_cons, List.map_nil, last,
    range_map_point visible root (by rw [view.length]; omega), List.take_succ_eq_append_getElem visibleRoot,
    List.map_append, List.map_cons, List.map_nil]
  have atRoot : visible[root] = point visible root := by
    simp only [point, List.getElem?_eq_getElem visibleRoot, Option.getD_some]
  rw [atRoot]
  have replacement : point (List.range (point visible root) ++ [target.length - 1]) (point visible root) =
      target.length - 1 := by
    simpa only [List.length_range] using point_append_last (List.range (point visible root)) (target.length - 1)
  rw [replacement]
  have unchanged : (visible.take root).map (point (List.range (point visible root) ++ [target.length - 1])) =
      visible.take root := by
    have identity : (visible.take root).map (point (List.range (point visible root) ++ [target.length - 1])) =
        (visible.take root).map id := by
      apply List.map_congr_left
      intro p member
      obtain ⟨i, iBound, lookup⟩ := List.getElem_of_mem member
      have earlier : i < root := by simp only [List.length_take] at iBound; omega
      have value : point visible i = p := by
        rw [← point_take visible root i earlier]
        simp only [point, List.getElem?_eq_getElem iBound, Option.getD_some, lookup]
      have smaller := view.increasing i root earlier inside
      rw [value] at smaller
      rw [point_append_old _ p _ (by simpa only [List.length_range] using smaller), point_range _ p smaller]
      rfl
    simpa only [List.map_id] using identity
  rw [unchanged]

end BTnSSBMS.Parents

namespace BTnSSBMS.Source

/-- The whole closed-list commuting square, including arbitrary nested
forests. Both root maps and the restricted intermediate view are derived. -/
theorem relocateForests_transplant_naturality {d : Nat} {source target : ParentContext} {visible : List Nat}
    (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
    (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
    (view : Parents.NumericalView d source target visible) (positive : 0 < d)
    {root : Nat} (before : root < source.length - 1)
    (path : Parents.Ancestor source (d - 1) root (source.length - 1)) (hs : Forests (List Nat)) :
    relocateForests d source target visible
      (relocateForests d (source.take (root + 1)) source (List.range root ++ [source.length - 1]) hs) =
    relocateForests d (target.take (Parents.point visible root + 1)) target
      (List.range (Parents.point visible root) ++ [target.length - 1])
      (relocateForests d (source.take (root + 1)) (target.take (Parents.point visible root + 1))
        (visible.take (root + 1)) hs) := by
  have inside : root < source.length := by omega
  have moved := Parents.ancestor_to_last_view sourceCoherent sourceValid positive before path
  have restricted := view.prefix_at targetValid root inside
  have old := relocateForests_compose d hs (source.take (root + 1)) source target
    (List.range root ++ [source.length - 1]) visible
    (sourceCoherent.restrict (List.take_prefix ..)) (sourceValid.restrict (List.take_prefix ..))
    sourceCoherent sourceValid moved view.length
  have next := relocateForests_compose d hs (source.take (root + 1))
    (target.take (Parents.point visible root + 1)) target (visible.take (root + 1))
    (List.range (Parents.point visible root) ++ [target.length - 1])
    (sourceCoherent.restrict (List.take_prefix ..)) (sourceValid.restrict (List.take_prefix ..))
    (targetCoherent.restrict (List.take_prefix ..)) (targetValid.restrict (List.take_prefix ..)) restricted
    (by have bound := view.bounded root inside
        simp only [List.length_append, List.length_range, List.length_cons, List.length_nil, List.length_take]
        omega)
  rw [old, next, view.transplant_maps before]

end BTnSSBMS.Source
