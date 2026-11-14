import BTnSSBMS.ClosingBlockSlice

/-!
Complete insertion domination at actual closing ancestors. The left side
is the old block's transported source material, run at the new closing
entry. Relating it to the new entry's own block remains a source-block
ordering obligation; this theorem does not assume or assert that result.
-/
namespace BTnSSBMS.Encoder

theorem matrix_column_prefix {state next : State d} (extended : state <+: next)
    (position : Nat) (inside : position < state.length) :
    (matrix next)[position]?.getD [] = (matrix state)[position]?.getD [] := by
  obtain ⟨extra, rfl⟩ := extended
  have bound : position < (state.map Column.values).length := by simpa only [List.length_map] using inside
  simp only [matrix, List.map_append, List.getElem?_append_left bound]

def Entry.transplantedBlock (earlier later : Entry d) : State d :=
  let source := earlier.source ++ [Parents.label d earlier.source earlier.coordinates]
  let target := later.source ++ [Parents.label d later.source later.coordinates]
  let moved := List.range earlier.source.length ++ [later.source.length]
  encode d (Parents.annotate d target (Source.relocate d source target moved earlier.blockTail))
    (later.visible ++ [later.closing]) later.headed

/-- The entire activation-sensitive block is covered, including every
nested forest and every outer tail column. Only standard-domain facts and
the actual strict closing-ancestor pair are premises. -/
theorem standard_closing_block_insertion {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {later : Entry d}
    (member : later ∈ entries d e [] [] [] [] []) {position : Nat}
    (self : SelfLatest (encode d (Parents.annotate d [] e) [] []) position)
    (before : position < later.closing)
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (fromSource d e)) d position later.closing) :
    ∃ earlier, earlier ∈ entries d e [] [] [] [] [] ∧ earlier.closing = position ∧
      matrixCompare ((matrix (earlier.transplantedBlock later)).drop later.closing)
        (BMS.rebase (d + 2) (fromSource d e) (d + 1) position later.closing) ≠ .gt := by
  obtain ⟨earlier, oldMember, closes, materialComparison⟩ :=
    standard_closing_material_comparison positive standard member self before path
  subst position
  let global := encode d (Parents.annotate d [] e) [] []
  let delta := fun j => Parents.reading (BMS.parentTable (d + 2) (matrix global)) j later.closing -
    Parents.reading (BMS.parentTable (d + 2) (matrix global)) j earlier.closing
  have oldSound := standard_entries_sound positive standard earlier oldMember
  have legal := Source.takeAbove_finiteLegal (floor := earlier.coordinates[0]?.getD 0) oldSound.legal.2.2.2.2
  have tailCompared : ShiftComparison earlier.closing delta earlier.headed later.headed
      earlier.blockState (earlier.transplantedBlock later) := materialComparison earlier.blockTail legal
  have oldGlobal := earlier.blockState_prefix_result.trans (entries_execution d e [] [] [] [] [] earlier oldMember).resultPrefix
  have newGlobal := later.headed_prefix_result.trans (entries_execution d e [] [] [] [] [] later member).resultPrefix
  have oldBound : earlier.closing < earlier.blockState.length :=
    Nat.lt_of_lt_of_le earlier.closing_inside_headed earlier.headed_prefix_blockState.length_le
  have newBound : later.closing < global.length := Nat.lt_of_lt_of_le later.closing_inside_headed newGlobal.length_le
  have newResultBound : later.closing < (matrix (earlier.transplantedBlock later)).length := by
    simpa only [matrix, List.length_map] using
      Nat.lt_of_lt_of_le later.closing_inside_headed tailCompared.newPrefix.length_le
  have rootSame : shiftedColumn earlier.blockState earlier.closing delta earlier.closing =
      (matrix (earlier.transplantedBlock later))[later.closing]?.getD [] := by
    rw [← shiftedColumn_prefix oldGlobal earlier.closing delta earlier.closing oldBound,
      shifted_root_eq_destination global earlier.closing later.closing newBound path
        ((standard_closing_tag oldMember).trans (standard_closing_tag member).symm),
      matrix_column_prefix newGlobal later.closing later.closing_inside_headed,
      matrix_column_prefix tailCompared.newPrefix later.closing later.closing_inside_headed]
  have oldHeadLength : earlier.headed.length = earlier.closing + 1 := by
    have := earlier.headed_nonempty
    unfold Entry.closing
    omega
  have newHeadLength : later.headed.length = later.closing + 1 := by
    have := later.headed_nonempty
    unfold Entry.closing
    omega
  have firstSlice : shiftedOutput earlier.blockState earlier.closing delta earlier.closing earlier.headed.length =
      [shiftedColumn earlier.blockState earlier.closing delta earlier.closing] := by
    rw [oldHeadLength, shiftedOutput_single]
  have rebased := rebase_eq_shifted_slice oldGlobal oldBound newBound
    (standard_closing_block_slice positive standard oldMember)
  change BMS.rebase (d + 2) (fromSource d e) (d + 1) earlier.closing later.closing =
    shiftedOutput earlier.blockState earlier.closing delta earlier.closing earlier.blockState.length at rebased
  refine ⟨earlier, oldMember, rfl, ?_⟩
  rw [rebased, shiftedOutput_split earlier.blockState earlier.closing delta earlier.closing
    earlier.headed.length earlier.blockState.length (Nat.le_of_lt earlier.closing_inside_headed)
    earlier.headed_prefix_blockState.length_le, firstSlice, rootSame,
    List.getElem?_eq_getElem newResultBound, Option.getD_some,
    List.drop_eq_getElem_cons newResultBound, ← newHeadLength]
  rcases tailCompared.comparison with strict | same
  · have extended := strict.prepend [(matrix (earlier.transplantedBlock later))[later.closing]]
    have compared := extended.compare
    simp only [List.cons_append, List.nil_append] at compared ⊢
    rw [compared]
    decide
  · rw [same]
    simp only [List.cons_append, List.nil_append, matrixCompare,
      listCompare_self (listCompare Ord.compare) columnCompare_self]
    decide

end BTnSSBMS.Encoder
