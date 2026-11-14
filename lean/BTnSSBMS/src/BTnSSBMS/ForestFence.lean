import BTnSSBMS.AuxiliaryParents
import BTnSSBMS.SourceFS

/-!
Finite forest fences: attaching columns whose zeroth values exceed their
owner keeps that owner on the actual row-zero ancestor chain of the final
frontier. Combined with a numerical view, this controls forest exit in the
target even though the source scope is later restored.
-/
namespace BTnSSBMS.Parents

theorem reading_coordinates (context : ParentContext) (row position : Nat) :
    reading context row position = ((context.map ParentLabel.coordinates)[position]?.getD [])[row]?.getD 0 := by
  cases lookup : context[position]? with
  | none => simp only [reading, lookup, List.getElem?_map, Option.map_none, Option.getD_none]; rfl
  | some a => simp only [reading, lookup, List.getElem?_map, Option.map_some, Option.getD_some]

theorem reading_prefix {small large : ParentContext} (initial : small <+: large)
    (row position : Nat) (inside : position < small.length) :
    reading small row position = reading large row position := by
  obtain ⟨tail, rfl⟩ := initial
  simp only [reading, List.getElem?_append_left inside]

theorem point_prefix {small large : List Nat} (initial : small <+: large)
    (position : Nat) (inside : position < small.length) :
    point small position = point large position := by
  obtain ⟨tail, rfl⟩ := initial
  simp only [point, List.getElem?_append_left inside]

theorem reading_append_label (d : Nat) (context : ParentContext) (coordinates : List Nat) (row : Nat) :
    reading (context ++ [label d context coordinates]) row context.length = coordinates[row]?.getD 0 := by
  simp only [reading, List.getElem?_concat_length, Option.getD_some, label]

end BTnSSBMS.Parents

namespace BTnSSBMS.BMS

/-- Adding a whole finite row-zero forest preserves its owner's ancestry
through to the final frontier. All comparisons are on literal input values. -/
theorem appended_forest_frontier {d : Nat} {context : ParentContext}
    (positive : 0 < d) (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    (nonempty : 0 < context.length) (m : Matrix)
    (above : ∀ col ∈ m, Parents.reading context 0 (context.length - 1) < col[0]?.getD 0) :
    Parents.Ancestor (parentTableAux d context m) 0 (context.length - 1)
      ((parentTableAux d context m).length - 1) := by
  let next := parentTableAux d context m
  have nextLength : next.length = context.length + m.length := parentTableAux_length d context m
  have extended : context <+: next := by
    obtain ⟨tail, shape⟩ := parentTableAux_extends d context m
    exact ⟨tail, shape.symm⟩
  have lastInside : next.length - 1 < next.length := by omega
  apply Parents.ancestor_zero_of_interval (parentTableAux_coherent d context m coherent)
    (parentTableAux_valid d context valid m) positive lastInside (by omega)
  intro position after before
  have oldEnd : context.length ≤ position := by omega
  have inside : position - context.length < m.length := by omega
  have targetLookup : ((next.map ParentLabel.coordinates)[position]?) = some m[position - context.length] := by
    rw [parentTableAux_coordinates]
    rw [List.getElem?_append_right (by simp only [List.length_map]; omega)]
    simp only [List.length_map, List.getElem?_eq_getElem inside]
  have high := above m[position - context.length] (List.getElem_mem inside)
  rw [← Parents.reading_prefix extended 0 (context.length - 1) (by omega),
    Parents.reading_coordinates next 0 position, targetLookup, Option.getD_some]
  exact high

end BTnSSBMS.BMS

namespace BTnSSBMS.Encoder

/-- Recover an actual target fence from the output view of a forest.
The incoming visible list is a prefix of the returned list, so its owner
position is unchanged even though the last source position has advanced. -/
theorem forest_output_fence {d : Nat} {context : ParentContext} {visible finalVisible : List Nat}
    (state : State d) (m : Matrix) (positive : 0 < d)
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    (nonempty : 0 < context.length) (visibleLength : visible.length = context.length)
    (extended : visible <+: finalVisible)
    (above : ∀ col ∈ m, Parents.reading context 0 (context.length - 1) < col[0]?.getD 0)
    (view : Parents.NumericalView d (BMS.parentTableAux d context m)
      (BMS.parentTable (d + 2) (matrix state)) finalVisible) :
    Parents.Ancestor (BMS.parentTable (d + 2) (matrix state)) 0
      (Parents.point visible (context.length - 1)) (state.length - 1) := by
  have path := BMS.appended_forest_frontier positive coherent valid nonempty m above
  have finalLength := BMS.parentTableAux_length d context m
  have ownerBound : context.length - 1 < (BMS.parentTableAux d context m).length := by omega
  have endBound : (BMS.parentTableAux d context m).length - 1 < (BMS.parentTableAux d context m).length := by omega
  have targetPath := view.lift 0 positive _ _ ownerBound endBound path
  have frontier := view.frontier (by intro empty; simp [empty] at finalLength; omega)
  have exactEnd : Parents.point finalVisible ((BMS.parentTableAux d context m).length - 1) = state.length - 1 := by
    rw [table_length] at frontier
    omega
  rw [exactEnd, ← Parents.point_prefix extended (context.length - 1) (by rw [visibleLength]; omega)] at targetPath
  exact targetPath

end BTnSSBMS.Encoder
