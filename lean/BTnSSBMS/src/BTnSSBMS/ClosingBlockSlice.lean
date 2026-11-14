import BTnSSBMS.ClosingInsertionComparison
import BTnSSBMS.CompleteBlockTransport
import BTnSSBMS.SourceBlockTransport

/-! Exact finite slices used to compare a complete closing-root block. -/
namespace BTnSSBMS.Encoder

def Entry.blockTail (entry : Entry d) : NumericalExpr :=
  Source.takeAbove (entry.coordinates[0]?.getD 0) entry.tail

def Entry.blockState (entry : Entry d) : State d :=
  encode d (Parents.annotate d (entry.source ++ [Parents.label d entry.source entry.coordinates]) entry.blockTail)
    (entry.visible ++ [entry.closing]) entry.headed

theorem Entry.headed_nonempty (entry : Entry d) : 0 < entry.headed.length := headState_nonempty ..

theorem Entry.closing_inside_headed (entry : Entry d) : entry.closing < entry.headed.length := by
  have := entry.headed_nonempty
  unfold Entry.closing
  omega

theorem Entry.headed_prefix_blockState (entry : Entry d) : entry.headed <+: entry.blockState := encode_extends ..

theorem Entry.blockState_prefix_result (entry : Entry d) : entry.blockState <+: entry.result := by
  simp only [Entry.result, Entry.remaining, Parents.annotate, encode_split_head]
  exact encode_takeAbove_prefix d entry.tail _ _ _ _

theorem standard_closing_block_slice {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {entry : Entry d}
    (member : entry ∈ entries d e [] [] [] [] []) :
    BMS.block (fromSource d e) entry.closing = (matrix entry.blockState).drop entry.closing := by
  simpa only [Entry.blockState, Entry.blockTail, Entry.remaining, Source.rootBlock,
    Parents.annotate, encode_split_head, Entry.closing, Entry.headed] using
      standard_entry_closing_source_block positive standard member

theorem headState_closing_tag (d : Nat) (a : ParentLabel) (hs : Forests ParentLabel)
    (visible : List Nat) (state : State d) :
    Parents.reading (BMS.parentTable (d + 2) (matrix (headState d a hs visible state)))
      (d + 1) ((headState d a hs visible state).length - 1) = 0 := by
  simp only [headState, encode]
  split <;> simp only [emit_length, Nat.add_sub_cancel] <;> exact (readout_emit ..).tag_reading

theorem standard_closing_tag {d : Nat} {e : NumericalExpr} {entry : Entry d}
    (member : entry ∈ entries d e [] [] [] [] []) :
    Parents.reading (BMS.parentTable (d + 2) (fromSource d e)) (d + 1) entry.closing = 0 := by
  have initial := entry.headed_prefix_result.trans (entries_execution d e [] [] [] [] [] entry member).resultPrefix
  unfold fromSource
  rw [← Parents.reading_prefix (table_prefix initial) (d + 1) entry.closing
    (by rw [table_length]; exact entry.closing_inside_headed)]
  exact headState_closing_tag ..

theorem row_difference_vector (state : State d) (root destination : Nat)
    (rootBound : root < state.length) (destinationBound : destination < state.length) :
    (List.range (d + 2)).map (fun j =>
      Parents.reading (BMS.parentTable (d + 2) (matrix state)) j destination -
        Parents.reading (BMS.parentTable (d + 2) (matrix state)) j root) =
      ((matrix state)[destination]?.getD []).zipWith (· - ·) ((matrix state)[root]?.getD []) := by
  have rootInside : root < (matrix state).length := by simpa only [matrix, List.length_map] using rootBound
  have newInside : destination < (matrix state).length := by simpa only [matrix, List.length_map] using destinationBound
  have rootWidth := matrix_width state _ (List.getElem_mem rootInside)
  have newWidth := matrix_width state _ (List.getElem_mem newInside)
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_zipWith, List.getElem?_eq_getElem rootInside,
      List.getElem?_eq_getElem newInside, Option.getD_some, rootWidth, newWidth, Nat.min_self]
  · intro j left right
    have room : j < d + 2 := by simpa only [List.length_map, List.length_range] using left
    have atRoot : j < ((matrix state)[root]).length := by omega
    have atNew : j < ((matrix state)[destination]).length := by omega
    have same : (((List.range (d + 2)).map (fun k =>
        Parents.reading (BMS.parentTable (d + 2) (matrix state)) k destination -
          Parents.reading (BMS.parentTable (d + 2) (matrix state)) k root))[j]?) =
        ((((matrix state)[destination]?.getD []).zipWith (· - ·) ((matrix state)[root]?.getD []))[j]?) := by
      simp only [List.getElem?_map, List.getElem?_range room, Option.map_some, BMS.parentTable_reading,
        List.getElem?_eq_getElem rootInside, List.getElem?_eq_getElem newInside, Option.getD_some,
        List.getElem?_zipWith, List.getElem?_eq_getElem atRoot, List.getElem?_eq_getElem atNew]
    simpa only [List.getElem?_eq_getElem left, List.getElem?_eq_getElem right, Option.some.injEq] using same

theorem rebase_eq_shifted_slice {state global : State d} {root destination : Nat}
    (initial : state <+: global) (rootBound : root < state.length) (destinationBound : destination < global.length)
    (closed : BMS.block (matrix global) root = (matrix state).drop root) :
    BMS.rebase (d + 2) (matrix global) (d + 1) root destination =
      shiftedOutput state root (fun j =>
        Parents.reading (BMS.parentTable (d + 2) (matrix global)) j destination -
          Parents.reading (BMS.parentTable (d + 2) (matrix global)) j root) root state.length := by
  have rootGlobal : root < global.length := Nat.lt_of_lt_of_le rootBound initial.length_le
  have blockLength : (BMS.block (matrix global) root).length = state.length - root := by
    rw [closed]
    simp only [List.length_drop, matrix, List.length_map]
  have actual := BMS.rebase_eq_take_copy (d + 2) (matrix global) (d + 1) root destination state.length
    (matrix_width global) (by simpa only [matrix, List.length_map] using rootGlobal)
    (by simpa only [matrix, List.length_map] using destinationBound) (by rw [blockLength]; omega)
  rw [← row_difference_vector global root destination rootGlobal destinationBound,
    ← shiftedOutput_eq_copy global root _ root state.length initial.length_le,
    shiftedOutput_prefix initial root _ root state.length (Nat.le_refl _), blockLength] at actual
  rw [List.take_of_length_le (by rw [shiftedOutput_length]; exact Nat.le_refl _)] at actual
  exact actual

theorem shifted_root_eq_destination (state : State d) (root destination : Nat)
    (destinationBound : destination < state.length)
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (matrix state)) d root destination)
    (sameTag : Parents.reading (BMS.parentTable (d + 2) (matrix state)) (d + 1) root =
      Parents.reading (BMS.parentTable (d + 2) (matrix state)) (d + 1) destination) :
    shiftedColumn state root (fun j =>
      Parents.reading (BMS.parentTable (d + 2) (matrix state)) j destination -
        Parents.reading (BMS.parentTable (d + 2) (matrix state)) j root) root =
      (matrix state)[destination]?.getD [] := by
  have inside : destination < (matrix state).length := by simpa only [matrix, List.length_map] using destinationBound
  have width := matrix_width state _ (List.getElem_mem inside)
  apply List.ext_getElem
  · simp only [shiftedColumn_width, List.getElem?_eq_getElem inside, Option.getD_some, width]
  · intro j left right
    have room : j < d + 2 := by simpa only [shiftedColumn_width] using left
    have atRow : j < ((matrix state)[destination]).length := by omega
    have same : (shiftedColumn state root (fun k =>
        Parents.reading (BMS.parentTable (d + 2) (matrix state)) k destination -
          Parents.reading (BMS.parentTable (d + 2) (matrix state)) k root) root)[j]?.getD 0 =
        Parents.reading (BMS.parentTable (d + 2) (matrix state)) j destination := by
      rw [shiftedColumn_reading _ _ _ _ _ room]
      by_cases low : j < d + 1
      · rw [if_pos low, rowBump_self]
        have lower := (path.lower_row (BMS.parentTable_coherent _ _) (by omega) (by omega : j ≤ d)).reading_le
          (BMS.parentTable_coherent _ _)
        omega
      · have tag : j = d + 1 := by omega
        subst j
        simpa only [Nat.lt_irrefl, if_false, Nat.add_zero] using sameTag
    rw [List.getElem?_eq_getElem left, Option.getD_some] at same
    simpa only [BMS.parentTable_reading, List.getElem?_eq_getElem inside, Option.getD_some,
      List.getElem?_eq_getElem atRow] using same

end BTnSSBMS.Encoder
