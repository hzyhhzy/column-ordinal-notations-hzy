import BTnSSBMS.RowRebaseValues
import BTnSSBMS.BMSBlocks

/-!
An actual ancestry-sensitive translation of row zero preserves the exact
end of its root block. Positions after that end are not silently included
in a rebased block. No block-order condition is assumed.
-/
namespace BTnSSBMS.Encoder

theorem rowBump_le (state : State d) (j root amount position : Nat) :
    rowBump state j root amount position ≤ amount := by
  classical
  simp only [rowBump]
  split <;> omega

theorem RowRebaseTrace.zero_root {state next result newResult : State d} {amount : Nat}
    (trace : RowRebaseTrace 0 state.length amount state next result newResult)
    (nonempty : state.length < result.length) :
    Parents.reading (BMS.parentTable (d + 2) (matrix newResult)) 0 next.length =
      Parents.reading (BMS.parentTable (d + 2) (matrix result)) 0 state.length + amount := by
  simpa only [Nat.add_zero, rowBump_self] using trace.values 0 (by omega)

theorem RowRebaseTrace.zero_ancestry_iff {state next result newResult : State d} {amount : Nat}
    (trace : RowRebaseTrace 0 state.length amount state next result newResult)
    (offset : Nat) (inside : offset < result.length - state.length) :
    Parents.Ancestor (BMS.parentTable (d + 2) (matrix newResult)) 0 next.length (next.length + offset) ↔
      Parents.Ancestor (BMS.parentTable (d + 2) (matrix result)) 0 state.length (state.length + offset) := by
  classical
  have length := trace.length
  have oldNonempty : state.length < result.length := by omega
  have newBound : next.length + offset < newResult.length := by omega
  have oldBound : state.length + offset < result.length := by omega
  have rootValue := trace.zero_root oldNonempty
  constructor
  · intro path
    have interval := path.zero_interval (BMS.parentTable_coherent _ _) (BMS.parentTable_valid _ _) (by omega)
    apply Parents.ancestor_zero_of_interval (BMS.parentTable_coherent _ _) (BMS.parentTable_valid _ _)
      (by omega : 0 < d + 2) (by simpa only [table_length] using oldBound) (by omega)
    intro position after before
    have offsetBound : position - state.length < result.length - state.length := by omega
    have same : state.length + (position - state.length) = position := by omega
    have value := trace.values (position - state.length) offsetBound
    rw [same] at value
    have high := interval.2 (next.length + (position - state.length)) (by omega) (by omega)
    have bump := rowBump_le result 0 state.length amount position
    omega
  · intro path
    have interval := path.zero_interval (BMS.parentTable_coherent _ _) (BMS.parentTable_valid _ _) (by omega)
    apply Parents.ancestor_zero_of_interval (BMS.parentTable_coherent _ _) (BMS.parentTable_valid _ _)
      (by omega : 0 < d + 2) (by simpa only [table_length] using newBound) (by omega)
    intro position after before
    have offsetBound : position - next.length < result.length - state.length := by omega
    have same : next.length + (position - next.length) = position := by omega
    have value := trace.values (position - next.length) offsetBound
    rw [same] at value
    have oldPosition : state.length + (position - next.length) < result.length := by omega
    have oldPath : Parents.Ancestor (BMS.parentTable (d + 2) (matrix result)) 0 state.length
        (state.length + (position - next.length)) :=
      Parents.ancestor_zero_of_interval (BMS.parentTable_coherent _ _) (BMS.parentTable_valid _ _)
        (by omega : 0 < d + 2) (by simpa only [table_length] using oldPosition) (by omega)
        (fun p h1 h2 => interval.2 p h1 (by omega))
    have high := interval.2 (state.length + (position - next.length)) (by omega) (by omega)
    simp only [rowBump, oldPath, if_true] at value
    omega

theorem RowRebaseTrace.block_length {state next result newResult : State d} {amount : Nat}
    (trace : RowRebaseTrace 0 state.length amount state next result newResult) :
    (BMS.block (matrix newResult) next.length).length =
      (BMS.block (matrix result) state.length).length := by
  have length := trace.length
  have oldLength := trace.oldPrefix.length_le
  have newLength := trace.newPrefix.length_le
  have oldBlock := (BMS.block_prefix (matrix result) state.length).length_le
  have newBlock := (BMS.block_prefix (matrix newResult) next.length).length_le
  have matrixOld : (matrix result).length = result.length := by simp only [matrix, List.length_map]
  have matrixNew : (matrix newResult).length = newResult.length := by simp only [matrix, List.length_map]
  simp only [List.length_drop, matrixOld, matrixNew] at oldBlock newBlock
  have same : ∀ k, k < result.length - state.length →
      (k < (BMS.block (matrix newResult) next.length).length ↔
        k < (BMS.block (matrix result) state.length).length) := by
    intro k inside
    rw [BMS.block_length_iff_ancestor (d + 2) (matrix newResult) (by omega) next.length k
        (by rw [matrixNew]; omega),
      BMS.block_length_iff_ancestor (d + 2) (matrix result) (by omega) state.length k
        (by rw [matrixOld]; omega)]
    exact trace.zero_ancestry_iff k inside
  apply Nat.le_antisymm
  · apply Nat.le_of_not_gt
    intro strict
    have equivalence := same (BMS.block (matrix result) state.length).length (by omega)
    exact Nat.lt_irrefl _ (equivalence.mp strict)
  · apply Nat.le_of_not_gt
    intro strict
    have equivalence := same (BMS.block (matrix newResult) next.length).length (by omega)
    exact Nat.lt_irrefl _ (equivalence.mpr strict)

end BTnSSBMS.Encoder
