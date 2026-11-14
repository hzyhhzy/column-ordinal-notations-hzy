import BTnSSBMS.PartialRebaseRows
import BTnSSBMS.CopyRebase

/-! Reassemble the actual numerical and control rows into the frozen
BMS copy. This does not identify a lexical suffix with a complete block. -/
namespace BTnSSBMS.Encoder

theorem controlTrace_reading (state : State d) (p j : Nat) :
    ((controlTrace state)[p]?.getD [])[j]?.getD 0 =
      Parents.reading (BMS.parentTable (d + 2) (matrix state)) (d + j) p := by
  rw [BMS.parentTable_reading, matrix_lookup]
  simp only [controlTrace, List.getElem?_map]
  cases found : state[p]? with
  | none => simp
  | some col => simp only [Option.map_some, Option.getD_some, List.getElem?_drop]

theorem SharedTrace.high_reading {state next result newResult : State d}
    (trace : SharedTrace state next result newResult) (k j : Nat) (high : d ≤ j) :
    Parents.reading (BMS.parentTable (d + 2) (matrix newResult)) j (next.length + k) =
      Parents.reading (BMS.parentTable (d + 2) (matrix result)) j (state.length + k) := by
  have equal := congrArg (fun xs : List (List Nat) => (xs[k]?.getD [])[j - d]?.getD 0) trace.suffix
  simp only [List.getElem?_drop, controlTrace_reading] at equal
  have row : d + (j - d) = j := by omega
  simpa only [row] using equal.symm

theorem full_rows_eq_copy {state next result newResult global : State d} {cut destination : Nat}
    (initial : result <+: global) (destinationBound : destination < global.length)
    (cutBound : cut ≤ d)
    (control : SharedTrace state next result newResult)
    (numerical : ∀ j, j < d →
      RowRebaseTrace j state.length
        (if j < cut then Parents.reading (BMS.parentTable (d + 2) (matrix global)) j destination -
          Parents.reading (BMS.parentTable (d + 2) (matrix global)) j state.length else 0)
        state next result newResult) (nonempty : state.length < result.length) :
    (matrix newResult).drop next.length =
      BMS.copy (matrix global) (BMS.thresholds (BMS.parentTable (d + 2) (matrix global)) state.length cut)
        (((matrix global)[destination]?.getD []).zipWith (· - ·) ((matrix global)[state.length]?.getD []))
        state.length result.length 1 := by
  have sameLength := control.length
  have finalLength := initial.length_le
  have rootBound : state.length < global.length := by omega
  apply List.ext_getElem
  · simp only [List.length_drop, matrix, List.length_map, BMS.copy_length]
    omega
  · intro k left right
    have kBound : k < result.length - state.length := by simpa only [BMS.copy_length] using right
    have oldBound : state.length + k < result.length := by omega
    have globalBound : state.length + k < global.length := by omega
    have newBound : next.length + k < newResult.length := by
      simp only [List.length_drop, matrix, List.length_map] at left
      omega
    have newMatrixBound : next.length + k < (matrix newResult).length := by simpa only [matrix, List.length_map] using newBound
    have globalMatrixBound : state.length + k < (matrix global).length := by simpa only [matrix, List.length_map] using globalBound
    have rootMatrixBound : state.length < (matrix global).length := by simpa only [matrix, List.length_map] using rootBound
    have destMatrixBound : destination < (matrix global).length := by simpa only [matrix, List.length_map] using destinationBound
    have copyColumn := BMS.copy_column (matrix global)
      (BMS.thresholds (BMS.parentTable (d + 2) (matrix global)) state.length cut)
      (((matrix global)[destination]?.getD []).zipWith (· - ·) ((matrix global)[state.length]?.getD []))
      state.length result.length 1 k kBound
    have leftColumn : ((matrix newResult).drop next.length)[k]? =
        some (matrix newResult)[next.length + k] := by
      rw [List.getElem?_drop, List.getElem?_eq_getElem newMatrixBound]
    have targetWidth := matrix_width newResult _ (List.getElem_mem newMatrixBound)
    have sourceWidth := matrix_width global _ (List.getElem_mem globalMatrixBound)
    have rWidth := matrix_width global _ (List.getElem_mem rootMatrixBound)
    have tWidth := matrix_width global _ (List.getElem_mem destMatrixBound)
    have columnEquality : (matrix newResult)[next.length + k] =
        (((matrix global)[state.length + k]?.getD []).mapIdx fun j value =>
          if j < (BMS.thresholds (BMS.parentTable (d + 2) (matrix global)) state.length cut)[state.length + k]?.getD 0
          then value + ((((matrix global)[destination]?.getD []).zipWith (· - ·)
            ((matrix global)[state.length]?.getD []))[j]?.getD 0) * 1 else value) := by
      apply List.ext_getElem
      · simp only [List.length_mapIdx, List.getElem?_eq_getElem globalMatrixBound,
          Option.getD_some, targetWidth, sourceWidth]
      · intro j rowLeft rowRight
        have rowBound : j < d + 2 := by omega
        have active := BMS.thresholds_ancestry (d + 2) (matrix global) state.length cut (by omega)
          (state.length + k) (by simpa only [matrix, List.length_map] using globalBound) j
        have desired : Parents.reading (BMS.parentTable (d + 2) (matrix newResult)) j (next.length + k) =
            if j < (BMS.thresholds (BMS.parentTable (d + 2) (matrix global)) state.length cut)[state.length + k]?.getD 0
            then Parents.reading (BMS.parentTable (d + 2) (matrix global)) j (state.length + k) +
              (Parents.reading (BMS.parentTable (d + 2) (matrix global)) j destination -
                Parents.reading (BMS.parentTable (d + 2) (matrix global)) j state.length)
            else Parents.reading (BMS.parentTable (d + 2) (matrix global)) j (state.length + k) := by
          classical
          by_cases low : j < d
          · have rowValue := (numerical j low).values k kBound
            rw [← rowBump_prefix initial j state.length _ (state.length + k) oldBound,
              Parents.reading_prefix (table_prefix initial) j (state.length + k) (by rw [table_length]; exact oldBound)] at rowValue
            simp only [rowBump] at rowValue
            simp only [active]
            by_cases below : j < cut <;>
              by_cases path : Parents.Ancestor (BMS.parentTable (d + 2) (matrix global)) j state.length (state.length + k) <;>
              simpa only [below, path, if_true, if_false, and_self, false_and, and_false, Nat.add_zero] using rowValue
          · have rowValue := control.high_reading k j (by omega)
            rw [Parents.reading_prefix (table_prefix initial) j (state.length + k) (by rw [table_length]; exact oldBound)] at rowValue
            have notActive : ¬ j < (BMS.thresholds (BMS.parentTable (d + 2) (matrix global)) state.length cut)[state.length + k]?.getD 0 :=
              fun h => by have := (active.mp h).1; omega
            simpa only [notActive, if_false] using rowValue
        simp only [BMS.parentTable_reading,
          List.getElem?_eq_getElem newMatrixBound,
          List.getElem?_eq_getElem globalMatrixBound,
          List.getElem?_eq_getElem rootMatrixBound,
          List.getElem?_eq_getElem destMatrixBound,
          Option.getD_some] at desired ⊢
        simpa only [List.getElem_mapIdx, List.getElem?_zipWith,
          List.getElem?_eq_getElem rowLeft, List.getElem?_eq_getElem (show j < ((matrix global)[state.length + k]).length by omega),
          List.getElem?_eq_getElem (show j < ((matrix global)[state.length]).length by omega),
          List.getElem?_eq_getElem (show j < ((matrix global)[destination]).length by omega),
          Option.getD_some, Nat.mul_one] using desired
    have optionEquality := leftColumn.trans ((congrArg some columnEquality).trans copyColumn.symm)
    simpa only [List.getElem?_eq_getElem left, List.getElem?_eq_getElem right, Option.some.injEq] using optionEquality

theorem standard_intermediate_pair_copy {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {a b cut : Nat}
    (rowPositive : 0 < cut) (room : cut < d) (before : a < b) (inside : b < (fromSource d e).length)
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (fromSource d e)) (cut - 1) a b)
    (same : Parents.parent (BMS.parentTable (d + 2) (fromSource d e)) cut a =
      Parents.parent (BMS.parentTable (d + 2) (fromSource d e)) cut b) :
    ∃ earlier later root, earlier ∈ entries d e [] [] [] [] [] ∧
      later ∈ entries d e [] [] [] [] [] ∧ root < later.source.length ∧
      earlier.OriginAt later.source later.visible later.owners later.materials later.state root ∧
      earlier.state.length = a ∧ later.state.length = b ∧
      (let delta := (List.range cut).map
        (fun k => later.coordinates[k]?.getD 0 - earlier.coordinates[k]?.getD 0)
      let shifted := encode d (Parents.annotate d later.source
        (Source.copied d root cut delta 1 earlier.source (List.replicate root 0) earlier.remaining))
        later.visible later.state
      (matrix shifted).drop b =
        BMS.copy (fromSource d e) (BMS.thresholds (BMS.parentTable (d + 2) (fromSource d e)) a cut)
          (((fromSource d e)[b]?.getD []).zipWith (· - ·) ((fromSource d e)[a]?.getD []))
          a earlier.result.length 1) := by
  obtain ⟨earlier, later, root, oldMember, newMember, bound, origin, oldPosition, newPosition, rows⟩ :=
    standard_intermediate_pair_rows positive standard rowPositive room before inside path same
  refine ⟨earlier, later, root, oldMember, newMember, bound, origin, oldPosition, newPosition, ?_⟩
  have sourcePath := standard_entry_ancestor_reflect positive standard oldMember newMember origin bound
    (by omega : cut - 1 < d) (by simpa only [oldPosition, newPosition] using path)
  have shared := standard_entry_shared_parent_reflect positive standard oldMember newMember origin bound room
    (by simpa only [oldPosition, newPosition] using same)
  have control := origin.partial_rebase_control (standard_entries_sound positive standard earlier oldMember)
    (standard_entries_sound positive standard later newMember) rowPositive room bound sourcePath shared.symm
  have result := full_rows_eq_copy (entries_execution d e [] [] [] [] [] earlier oldMember).resultPrefix
    (destination := b) (cut := cut) (by simpa only [fromSource, matrix, List.length_map] using inside) (by omega) control
    (by simpa only [oldPosition, fromSource] using rows) earlier.first_lt_result
  simpa only [fromSource, oldPosition, newPosition] using result

end BTnSSBMS.Encoder
