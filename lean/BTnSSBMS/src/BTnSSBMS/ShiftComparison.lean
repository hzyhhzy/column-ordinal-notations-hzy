import BTnSSBMS.ShiftedOutput
import BTnSSBMS.EncoderBoundary

/-!
Composition of actual output comparisons. After a strict column has
appeared, later lengths and later branches are unrestricted. Only the
equal case supplies row traces for entering the next recursive call.
-/
namespace BTnSSBMS.Encoder

structure ShiftComparison (root : Nat) (delta : Nat → Nat)
    (state next result newResult : State d) : Prop where
  oldPrefix : state <+: result
  newPrefix : next <+: newResult
  comparison : MatrixFirstLt ((matrix newResult).drop next.length)
      (shiftedOutput result root delta state.length result.length) ∨
    (matrix newResult).drop next.length = shiftedOutput result root delta state.length result.length

theorem ShiftComparison.refl (root : Nat) (delta : Nat → Nat) (state next : State d) :
    ShiftComparison root delta state next state next := by
  refine ⟨List.prefix_refl _, List.prefix_refl _, Or.inr ?_⟩
  simp [matrix, shiftedOutput]

theorem shifted_strict_extends {d root : Nat} {delta : Nat → Nat}
    {state next middle newMiddle result newResult : State d}
    (oldFirst : state <+: middle) (newFirst : next <+: newMiddle)
    (oldLater : middle <+: result) (newLater : newMiddle <+: newResult)
    (strict : MatrixFirstLt ((matrix newMiddle).drop next.length)
      (shiftedOutput middle root delta state.length middle.length)) :
    MatrixFirstLt ((matrix newResult).drop next.length)
      (shiftedOutput result root delta state.length result.length) := by
  rw [matrix_drop_split newFirst newLater,
    shiftedOutput_split result root delta state.length middle.length result.length oldFirst.length_le oldLater.length_le,
    shiftedOutput_prefix oldLater root delta state.length middle.length (Nat.le_refl _)]
  exact strict.append _ _

theorem ShiftComparison.trans {d root : Nat} {delta : Nat → Nat}
    {state next middle newMiddle result newResult : State d}
    (first : ShiftComparison root delta state next middle newMiddle)
    (second : ShiftComparison root delta middle newMiddle result newResult) :
    ShiftComparison root delta state next result newResult := by
  refine ⟨first.oldPrefix.trans second.oldPrefix, first.newPrefix.trans second.newPrefix, ?_⟩
  rcases first.comparison with strict | same
  · exact Or.inl (shifted_strict_extends first.oldPrefix first.newPrefix second.oldPrefix second.newPrefix strict)
  · rw [matrix_drop_split first.newPrefix second.newPrefix,
      shiftedOutput_split result root delta state.length middle.length result.length first.oldPrefix.length_le second.oldPrefix.length_le,
      shiftedOutput_prefix second.oldPrefix root delta state.length middle.length (Nat.le_refl _), same]
    rcases second.comparison with strict | equal
    · exact Or.inl (strict.prepend _)
    · exact Or.inr (congrArg (_ ++ ·) equal)

theorem ShiftComparison.emit_equal (state next : State d) (u v : Nat → Nat)
    (height tag newHeight newTag : Nat) (frame newFrame : List Binding) (root : Nat) (delta : Nat → Nat)
    (same : row d v newHeight newTag =
      shiftedColumn (emit state u height tag frame) root delta state.length) :
    ShiftComparison root delta state next (emit state u height tag frame) (emit next v newHeight newTag newFrame) := by
  refine ⟨emit_extends .., emit_extends .., Or.inr ?_⟩
  rw [emit_length, shiftedOutput_single, matrix_emit]
  have length : (matrix next).length = next.length := List.length_map _
  rw [← length, List.drop_left, same]

theorem ShiftComparison.emit_strict (state next : State d) (u v : Nat → Nat)
    (height tag newHeight newTag : Nat) (frame newFrame : List Binding) (root : Nat) (delta : Nat → Nat)
    (strict : listCompare Ord.compare (row d v newHeight newTag)
      (shiftedColumn (emit state u height tag frame) root delta state.length) = .lt) :
    ShiftComparison root delta state next (emit state u height tag frame) (emit next v newHeight newTag newFrame) := by
  refine ⟨emit_extends .., emit_extends .., Or.inl ?_⟩
  rw [emit_length, shiftedOutput_single, matrix_emit]
  have length : (matrix next).length = next.length := List.length_map _
  rw [← length, List.drop_left]
  exact ⟨[], _, _, [], [], rfl, rfl, strict⟩

theorem equal_shiftedOutput_row_trace {d root : Nat} {delta : Nat → Nat}
    {state next result newResult : State d}
    (oldPrefix : state <+: result) (newPrefix : next <+: newResult)
    (same : (matrix newResult).drop next.length = shiftedOutput result root delta state.length result.length)
    (j : Nat) (room : j < d + 1) :
    RowRebaseTrace j root (delta j) state next result newResult := by
  have lengths := congrArg List.length same
  simp only [List.length_drop, matrix, List.length_map, shiftedOutput_length] at lengths
  have oldLe := oldPrefix.length_le
  have newLe := newPrefix.length_le
  refine ⟨oldPrefix, newPrefix, by omega, ?_⟩
  intro k inside
  have atPosition := congrArg (fun m : Matrix => (m[k]?.getD [])[j]?.getD 0) same
  simp only [List.getElem?_drop, shiftedOutput, List.getElem?_map, List.getElem?_range inside,
    Option.map_some, Option.getD_some] at atPosition
  rw [shiftedColumn_reading _ _ _ _ _ (by omega), if_pos room] at atPosition
  simpa only [BMS.parentTable_reading] using atPosition

end BTnSSBMS.Encoder
