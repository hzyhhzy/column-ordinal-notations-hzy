import BTnSSBMS.SourceBlockEncoding

/-!
Complete blocks at row-zero descendants stay inside their ancestor's
block. A bounded block can therefore be recovered in an actual execution
prefix, not merely in an arbitrary chosen output interval.
-/
namespace BTnSSBMS.BMS

theorem parentTable_prefix {rows : Nat} {small large : Matrix} (initial : small <+: large) :
    parentTable rows small <+: parentTable rows large := by
  obtain ⟨tail, rfl⟩ := initial
  rw [parentTable_append]
  obtain ⟨added, shape⟩ := parentTableAux_extends rows (parentTable rows small) tail
  exact ⟨added, shape.symm⟩

theorem block_end_le_of_ancestor {rows : Nat} {m : Matrix} {root child : Nat}
    (positive : 0 < rows) (inside : child < m.length)
    (path : Parents.Ancestor (parentTable rows m) 0 root child) :
    child + (block m child).length ≤ root + (block m root).length := by
  have before := path.le (parentTable_valid rows m)
  obtain ⟨tail, shape⟩ := block_head m child inside
  have nonempty : 0 < (block m child).length := by rw [shape, List.length_cons]; omega
  have bound := (block_prefix m child).length_le
  simp only [List.length_drop] at bound
  let last := child + (block m child).length - 1
  have endInside : last < m.length := by dsimp only [last]; omega
  have childEnd : child + ((block m child).length - 1) = last := by dsimp only [last]; omega
  have childPath := (block_length_iff_ancestor rows m positive child
    ((block m child).length - 1) (by omega)).mp (by omega)
  rw [childEnd] at childPath
  have rootEnd : root + (last - root) = last := by dsimp only [last]; omega
  have inRoot := (block_length_iff_ancestor rows m positive root (last - root) (by omega)).mpr
    (by simpa only [rootEnd] using path.trans childPath)
  dsimp only [last] at inRoot
  omega

/-- If the whole large block ends before an actual prefix ends, computing
it in that prefix gives exactly the same block. -/
theorem block_restrict_of_bound {rows : Nat} {small large : Matrix} {root : Nat}
    (positive : 0 < rows) (initial : small <+: large) (inside : root < small.length)
    (contained : root + (block large root).length ≤ small.length) :
    block small root = block large root := by
  have longer := initial.length_le
  have tableInitial : parentTable rows small <+: parentTable rows large := parentTable_prefix initial
  obtain ⟨smallTail, smallShape⟩ := block_head small root inside
  obtain ⟨largeTail, largeShape⟩ := block_head large root (by omega)
  have smallPositive : 0 < (block small root).length := by rw [smallShape, List.length_cons]; omega
  have largePositive : 0 < (block large root).length := by rw [largeShape, List.length_cons]; omega
  have smallBound := (block_prefix small root).length_le
  simp only [List.length_drop] at smallBound
  have smallLast := (block_length_iff_ancestor rows small positive root
    ((block small root).length - 1) (by omega)).mp (by omega)
  have largeLast := (block_length_iff_ancestor rows large positive root
    ((block large root).length - 1) (by omega)).mp (by omega)
  have forward := (block_length_iff_ancestor rows large positive root
    ((block small root).length - 1) (by omega)).mpr (smallLast.prefix tableInitial)
  have backward := (block_length_iff_ancestor rows small positive root
    ((block large root).length - 1) (by omega)).mpr
    (largeLast.restrict tableInitial (parentTable_valid rows large)
      (by simp only [parentTable_length]; omega))
  have sameSize : (block small root).length = (block large root).length := by omega
  calc
    block small root = (small.drop root).take (block large root).length := by rw [block_eq_take, sameSize]
    _ = (large.drop root).take (block large root).length := by
      obtain ⟨rest, shape⟩ := initial
      have dropShape : large.drop root = small.drop root ++ rest := by
        rw [← shape, List.drop_append_of_le_length (by omega : root ≤ small.length)]
      rw [dropShape, List.take_append_of_le_length (by simp only [List.length_drop]; omega)]
    _ = block large root := (block_eq_take large root).symm

theorem block_restrict_descendant {rows : Nat} {small large : Matrix} {root child : Nat}
    (positive : 0 < rows) (initial : small <+: large) (inside : child < small.length)
    (path : Parents.Ancestor (parentTable rows large) 0 root child)
    (contained : root + (block large root).length ≤ small.length) :
    block large child = block small child := by
  have longer := initial.length_le
  have bound := block_end_le_of_ancestor positive (by omega : child < large.length) path
  exact (block_restrict_of_bound positive initial inside (by omega)).symm

end BTnSSBMS.BMS
