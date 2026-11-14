import BTnSSBMS.NumericalUnits
import BTnSSBMS.FrameReferences
import BTnSSBMS.FrameHeight

/-! Actual higher-row searches and the two non-numerical readouts. -/
namespace BTnSSBMS.Parents

theorem Ancestor.of_reading_le {rows : Nat} {context : ParentContext}
    (coherent : Coherent rows context) {row a b endpoint : Nat}
    (left : Ancestor context row a endpoint) (right : Ancestor context row b endpoint)
    (ordered : reading context row a ≤ reading context row b) : Ancestor context row a b := by
  rcases left.comparable right with forward | backward
  · exact forward
  · by_cases same : a = b
    · subst a; exact .refl _
    · have contrary := backward.reading_lt coherent (Ne.symm same)
      omega

theorem parent_none_of_zero {rows : Nat} {context : ParentContext}
    (coherent : Coherent rows context) (row position : Nat)
    (zero : reading context row position = 0) : parent context row position = none := by
  cases selected : parent context row position with
  | none => rfl
  | some p => have lower := parent_reading_lt coherent selected; omega

theorem next_parent_of_ancestor_value {rows : Nat} {context : ParentContext}
    (coherent : Coherent rows context) (valid : ContextValid context)
    {row root start position : Nat} (room : row + 1 < rows)
    (lower : parent context row position = some start)
    (path : Ancestor context (row + 1) root start)
    (value : reading context (row + 1) position = reading context (row + 1) root + 1) :
    parent context (row + 1) position = some root := by
  obtain ⟨a, atPosition, _⟩ := Option.bind_eq_some_iff.mp lower
  have inside := (List.getElem?_eq_some_iff.mp atPosition).choose
  have earlier := parent_earlier valid lower
  rw [parent_next_search coherent valid room inside, lower, value]
  simp only [Option.map_some, Option.getD_some]
  exact search_ancestor_successor coherent valid room (by omega) path

end BTnSSBMS.Parents

namespace BTnSSBMS.Encoder

theorem row_key_reading (d : Nat) (u : Nat → Nat) (height tag : Nat) :
    (row d u height tag)[d]?.getD 0 = height := by simp [row]

theorem row_tag_reading (d : Nat) (u : Nat → Nat) (height tag : Nat) :
    (row d u height tag)[d + 1]?.getD 0 = tag := by simp [row]

theorem Readout.key_reading {state : State d} {position height tag : Nat}
    (output : Readout state position height tag) :
    Parents.reading (BMS.parentTable (d + 2) (matrix state)) d position = height := by
  obtain ⟨col, lookup, key, _⟩ := output
  rw [BMS.parentTable_reading, matrix_lookup, lookup]
  simp only [Option.map_some, Option.getD_some, key]

theorem Readout.tag_reading {state : State d} {position height tag : Nat}
    (output : Readout state position height tag) :
    Parents.reading (BMS.parentTable (d + 2) (matrix state)) (d + 1) position = tag := by
  obtain ⟨col, lookup, _, label⟩ := output
  rw [BMS.parentTable_reading, matrix_lookup, lookup]
  simp only [Option.map_some, Option.getD_some, label]

theorem emitted_key_zero (state : State d) (u : Nat → Nat) (tag : Nat) (frame : List Binding) :
    Parents.parent (BMS.parentTable (d + 2) (matrix (emit state u 0 tag frame))) d state.length = none :=
  Parents.parent_none_of_zero (BMS.parentTable_coherent _ _) _ _ (readout_emit state u 0 tag frame).key_reading

theorem emitted_tag_zero (state : State d) (u : Nat → Nat) (height : Nat) (frame : List Binding) :
    Parents.parent (BMS.parentTable (d + 2) (matrix (emit state u height 0 frame))) (d + 1) state.length = none :=
  Parents.parent_none_of_zero (BMS.parentTable_coherent _ _) _ _ (readout_emit state u height 0 frame).tag_reading

theorem emitted_key_parent (state : State d) (u : Nat → Nat) (height tag : Nat) (frame : List Binding)
    (positive : 0 < d) (start root : Nat)
    (lower : Parents.parent (BMS.parentTable (d + 2) (matrix (emit state u height tag frame)))
      (d - 1) state.length = some start)
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (matrix state)) d root start)
    (value : height = Parents.reading (BMS.parentTable (d + 2) (matrix state)) d root + 1) :
    Parents.parent (BMS.parentTable (d + 2) (matrix (emit state u height tag frame))) d state.length = some root := by
  have rootBound : root < (BMS.parentTable (d + 2) (matrix state)).length := by
    have before := Parents.parent_earlier (BMS.parentTable_valid _ _) lower
    have left := path.le (BMS.parentTable_valid _ _)
    rw [table_length]; omega
  have rowSame : d - 1 + 1 = d := by omega
  have highPath := path.prefix (table_emit_prefix state u height tag frame)
  have targetValue : Parents.reading (BMS.parentTable (d + 2) (matrix (emit state u height tag frame)))
      d state.length =
      Parents.reading (BMS.parentTable (d + 2) (matrix (emit state u height tag frame))) d root + 1 := by
    rw [(readout_emit state u height tag frame).key_reading,
      ← Parents.reading_prefix (table_emit_prefix ..) d root rootBound]
    exact value
  have result := Parents.next_parent_of_ancestor_value (BMS.parentTable_coherent _ _)
    (BMS.parentTable_valid _ _) (row := d - 1) (by omega) lower
    (by simpa only [rowSame] using highPath) (by simpa only [rowSame] using targetValue)
  simpa only [rowSame] using result

theorem guard_key_parent (state : State d) (u : Nat → Nat) (c : Nat) (positive : 0 < d) :
    Parents.parent (BMS.parentTable (d + 2) (matrix
      (emit (emit state u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 []))) d (state.length + 1) =
      some state.length := by
  have lower := guard_numerical_parents state u c (d - 1) (by omega)
  have result := emitted_key_parent (emit state u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 []
    positive state.length state.length (by simpa only [emit_length] using lower) (.refl _)
    (by rw [(readout_emit state u (c + 1) 1 []).key_reading])
  simpa only [emit_length] using result

theorem emitted_tag_parent (state : State d) (u : Nat → Nat) (height tag : Nat) (frame : List Binding)
    (root : Nat)
    (key : Parents.parent (BMS.parentTable (d + 2) (matrix (emit state u height tag frame))) d state.length = some root)
    (value : tag = Parents.reading (BMS.parentTable (d + 2) (matrix state)) (d + 1) root + 1) :
    Parents.parent (BMS.parentTable (d + 2) (matrix (emit state u height tag frame))) (d + 1) state.length = some root := by
  apply Parents.parent_next_of_gt (BMS.parentTable_coherent _ _) (BMS.parentTable_valid _ _) (by omega) key
  have rootBound : root < (BMS.parentTable (d + 2) (matrix state)).length := by
    have before := Parents.parent_earlier (BMS.parentTable_valid _ _) key
    rw [table_length]; exact before
  rw [← Parents.reading_prefix (table_emit_prefix ..) (d + 1) root rootBound,
    (readout_emit state u height tag frame).tag_reading, value]
  omega

theorem guard_tag_parent (state : State d) (u : Nat → Nat) (c : Nat) (positive : 0 < d) :
    Parents.parent (BMS.parentTable (d + 2) (matrix
      (emit (emit state u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 []))) (d + 1) (state.length + 1) =
      some state.length := by
  have result := emitted_tag_parent (emit state u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 []
    state.length (by simpa only [emit_length] using guard_key_parent state u c positive)
    (by rw [(readout_emit state u (c + 1) 1 []).tag_reading])
  simpa only [emit_length] using result

end BTnSSBMS.Encoder
