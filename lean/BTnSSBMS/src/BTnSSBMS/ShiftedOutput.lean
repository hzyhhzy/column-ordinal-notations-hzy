import BTnSSBMS.KeyRowRebase
import BTnSSBMS.CopyRebase

/-!
Proof-side columns with the exact activation used by BMS at cap d+1.
The tag is unshifted. The comparison root and the copied interval's start
are deliberately separate: a closing-root tail starts after its root.
-/
namespace BTnSSBMS.Encoder

noncomputable def shiftedColumn (state : State d) (root : Nat) (delta : Nat → Nat) (p : Nat) : List Nat :=
  row d (fun j => Parents.reading (BMS.parentTable (d + 2) (matrix state)) j p +
    rowBump state j root (delta j) p)
    (Parents.reading (BMS.parentTable (d + 2) (matrix state)) d p + rowBump state d root (delta d) p)
    (Parents.reading (BMS.parentTable (d + 2) (matrix state)) (d + 1) p)

noncomputable def shiftedOutput (state : State d) (root : Nat) (delta : Nat → Nat)
    (start finish : Nat) : Matrix :=
  (List.range (finish - start)).map fun k => shiftedColumn state root delta (start + k)

theorem shiftedColumn_width (state : State d) (root : Nat) (delta : Nat → Nat) (p : Nat) :
    (shiftedColumn state root delta p).length = d + 2 := row_width ..

theorem shiftedColumn_reading (state : State d) (root : Nat) (delta : Nat → Nat) (p j : Nat)
    (room : j < d + 2) :
    (shiftedColumn state root delta p)[j]?.getD 0 =
      Parents.reading (BMS.parentTable (d + 2) (matrix state)) j p +
        if j < d + 1 then rowBump state j root (delta j) p else 0 := by
  by_cases low : j < d
  · simp only [shiftedColumn, row_numerical_reading d _ _ _ j low, if_pos (show j < d + 1 by omega)]
  · by_cases key : j = d
    · subst j
      simp only [shiftedColumn, row_key_reading, Nat.lt_succ_self, if_true]
    · have tag : j = d + 1 := by omega
      subst j
      simp only [shiftedColumn, row_tag_reading, Nat.lt_irrefl, if_false, Nat.add_zero]

theorem shiftedColumn_prefix {state next : State d} (extended : state <+: next)
    (root : Nat) (delta : Nat → Nat) (p : Nat) (inside : p < state.length) :
    shiftedColumn next root delta p = shiftedColumn state root delta p := by
  apply List.ext_getElem
  · rw [shiftedColumn_width, shiftedColumn_width]
  · intro j left right
    have room : j < d + 2 := by simpa only [shiftedColumn_width] using left
    have same : (shiftedColumn next root delta p)[j]?.getD 0 =
        (shiftedColumn state root delta p)[j]?.getD 0 := by
      rw [shiftedColumn_reading _ _ _ _ _ room, shiftedColumn_reading _ _ _ _ _ room,
        ← Parents.reading_prefix (table_prefix extended) j p (by rw [table_length]; exact inside),
        rowBump_prefix extended j root (delta j) p inside]
    simpa only [List.getElem?_eq_getElem left, List.getElem?_eq_getElem right, Option.getD_some] using same

theorem shiftedColumn_emit (state : State d) (u : Nat → Nat) (height tag : Nat) (frame : List Binding)
    (root : Nat) (delta : Nat → Nat) :
    shiftedColumn (emit state u height tag frame) root delta state.length =
      row d (fun j => u j + rowBump (emit state u height tag frame) j root (delta j) state.length)
        (height + rowBump (emit state u height tag frame) d root (delta d) state.length) tag := by
  unfold shiftedColumn row
  congr 1
  · apply List.map_congr_left
    intro j member
    rw [emitted_numerical_value state u height tag frame j (List.mem_range.mp member)]
  · rw [(readout_emit state u height tag frame).key_reading,
      (readout_emit state u height tag frame).tag_reading]

theorem shiftedColumn_eq_copy_column (state : State d) (root : Nat) (delta : Nat → Nat) (p : Nat)
    (inside : p < state.length) :
    shiftedColumn state root delta p =
      ((matrix state)[p]?.getD []).mapIdx (fun j v =>
        if j < (BMS.thresholds (BMS.parentTable (d + 2) (matrix state)) root (d + 1))[p]?.getD 0
        then v + (((List.range (d + 2)).map delta)[j]?.getD 0) * 1 else v) := by
  classical
  have bound : p < (matrix state).length := by simpa only [matrix, List.length_map] using inside
  have width := matrix_width state _ (List.getElem_mem bound)
  apply List.ext_getElem
  · simp only [shiftedColumn_width, List.length_mapIdx, List.getElem?_eq_getElem bound, Option.getD_some, width]
  · intro j left right
    have room : j < d + 2 := by simpa only [shiftedColumn_width] using left
    have atRow : j < ((matrix state)[p]).length := by omega
    have activation := BMS.thresholds_ancestry (d + 2) (matrix state) root (d + 1) (by omega) p bound j
    have value := shiftedColumn_reading state root delta p j room
    simp only [BMS.parentTable_reading, List.getElem?_eq_getElem bound, Option.getD_some,
      List.getElem?_eq_getElem atRow, List.getElem?_eq_getElem left, rowBump] at value
    simp only [List.getElem?_eq_getElem bound, Option.getD_some, List.getElem_mapIdx,
      List.getElem?_map, List.getElem?_range room, Option.map_some, Nat.mul_one, activation]
    by_cases low : j < d + 1 <;>
      by_cases path : Parents.Ancestor (BMS.parentTable (d + 2) (matrix state)) j root p <;>
      simpa only [low, path, if_true, if_false, and_self, false_and, and_false, Nat.add_zero,
        Option.getD_some] using value

theorem shiftedOutput_length (state : State d) (root : Nat) (delta : Nat → Nat) (start finish : Nat) :
    (shiftedOutput state root delta start finish).length = finish - start := by
  simp only [shiftedOutput, List.length_map, List.length_range]

theorem shiftedOutput_prefix {state next : State d} (extended : state <+: next)
    (root : Nat) (delta : Nat → Nat) (start finish : Nat) (bounded : finish ≤ state.length) :
    shiftedOutput next root delta start finish = shiftedOutput state root delta start finish := by
  apply List.map_congr_left
  intro k member
  exact shiftedColumn_prefix extended root delta (start + k) (by have := List.mem_range.mp member; omega)

theorem shiftedOutput_split (state : State d) (root : Nat) (delta : Nat → Nat) (start middle finish : Nat)
    (first : start ≤ middle) (second : middle ≤ finish) :
    shiftedOutput state root delta start finish = shiftedOutput state root delta start middle ++
      shiftedOutput state root delta middle finish := by
  have counts : finish - start = (middle - start) + (finish - middle) := by omega
  simp only [shiftedOutput, counts, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  change shiftedColumn state root delta (start + (middle - start + k)) =
    shiftedColumn state root delta (middle + k)
  exact congrArg (shiftedColumn state root delta) (by omega)

theorem shiftedOutput_single (state : State d) (root : Nat) (delta : Nat → Nat) (p : Nat) :
    shiftedOutput state root delta p (p + 1) = [shiftedColumn state root delta p] := by
  simp only [shiftedOutput, Nat.add_sub_cancel_left, List.range_succ, List.range_zero, List.nil_append,
    List.map_cons, List.map_nil, Nat.add_zero]

theorem matrix_drop_split {state middle result : State d}
    (first : state <+: middle) (second : middle <+: result) :
    (matrix result).drop state.length =
      (matrix middle).drop state.length ++ (matrix result).drop middle.length := by
  obtain ⟨a, rfl⟩ := first
  obtain ⟨b, rfl⟩ := second
  simp [matrix, List.map_append, List.drop_append]

theorem shiftedOutput_eq_copy (state : State d) (root : Nat) (delta : Nat → Nat) (start finish : Nat)
    (bounded : finish ≤ state.length) :
    shiftedOutput state root delta start finish =
      BMS.copy (matrix state) (BMS.thresholds (BMS.parentTable (d + 2) (matrix state)) root (d + 1))
        ((List.range (d + 2)).map delta) start finish 1 := by
  apply List.ext_getElem
  · rw [shiftedOutput_length, BMS.copy_length]
  · intro k left right
    have room : k < finish - start := by simpa only [shiftedOutput_length] using left
    have old := BMS.copy_column (matrix state)
      (BMS.thresholds (BMS.parentTable (d + 2) (matrix state)) root (d + 1))
      ((List.range (d + 2)).map delta) start finish 1 k room
    have new : (shiftedOutput state root delta start finish)[k]? =
        some (shiftedColumn state root delta (start + k)) := by
      simp only [shiftedOutput, List.getElem?_map, List.getElem?_range room, Option.map_some]
    rw [shiftedColumn_eq_copy_column state root delta (start + k) (by omega)] at new
    have same := new.trans old.symm
    simpa only [List.getElem?_eq_getElem left, List.getElem?_eq_getElem right, Option.some.injEq] using same

end BTnSSBMS.Encoder
