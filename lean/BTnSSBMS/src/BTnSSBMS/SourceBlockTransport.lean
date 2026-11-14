import BTnSSBMS.SourceBlockEncoding

/-!
The actual intermediate-row rebase equals the complete encoding of the
rebased complete source block. In particular no tail past the source
block's endpoint is used to apply a source block inequality.
-/
namespace BTnSSBMS.Encoder

theorem encode_takeAbove_prefix (d : Nat) (e : NumericalExpr) (floor : Nat)
    (source : ParentContext) (visible : List Nat) (state : State d) :
    encode d (Parents.annotate d source (Source.takeAbove floor e)) visible state <+:
      encode d (Parents.annotate d source e) visible state := by
  cases e with
  | nil => exact List.prefix_refl _
  | cons a hs tail =>
    simp only [Source.takeAbove]
    split
    · simp only [Parents.annotate, encode_split_head]
      exact encode_takeAbove_prefix d tail floor _ _ _
    · exact encode_extends ..

theorem full_interval_eq_rebase {state next result newResult global : State d} {cut destination : Nat}
    (initial : result <+: global) (destinationBound : destination < global.length) (cutBound : cut ≤ d)
    (control : SharedTrace state next result newResult)
    (numerical : ∀ j, j < d →
      RowRebaseTrace j state.length
        (if j < cut then Parents.reading (BMS.parentTable (d + 2) (matrix global)) j destination -
          Parents.reading (BMS.parentTable (d + 2) (matrix global)) j state.length else 0)
        state next result newResult) (nonempty : state.length < result.length)
    (complete : BMS.block (matrix global) state.length = (matrix result).drop state.length) :
    (matrix newResult).drop next.length = BMS.rebase (d + 2) (matrix global) cut state.length destination := by
  have globalLength := initial.length_le
  have size := congrArg List.length complete
  simp only [List.length_drop, matrix, List.length_map] at size
  change (BMS.block (matrix global) state.length).length = result.length - state.length at size
  rw [full_rows_eq_copy initial destinationBound cutBound control numerical nonempty]
  have rootBound : state.length < (matrix global).length := by simp only [matrix, List.length_map]; omega
  have destinationInside : destination < (matrix global).length := by
    simpa only [matrix, List.length_map] using destinationBound
  simp only [List.getElem?_eq_getElem rootBound, List.getElem?_eq_getElem destinationInside, Option.getD_some]
  rw [BMS.first_copy_eq_rebase_take (d + 2) (matrix global) cut state.length destination result.length
    (matrix_width global) (by simp only [matrix, List.length_map]; omega)
    (by simpa only [matrix, List.length_map] using destinationBound) (by omega)]
  rw [← size, ← BMS.rebase_length (d + 2) (matrix global) cut state.length destination, List.take_length]

/-- The ordinary-row block equation used by the paper, now for every
actual standard target pair with its source endpoints constructed.
The right side encodes only the original complete source block. -/
theorem standard_intermediate_source_block {d : Nat} (positive : 0 < d) {e : NumericalExpr}
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
      BMS.rebase (d + 2) (fromSource d e) cut a b =
        (matrix (encode d (Parents.annotate d later.source
          (Source.copied d root cut delta 1 earlier.source (List.replicate root 0)
            (Source.rootBlock earlier.remaining))) later.visible later.state)).drop b) := by
  obtain ⟨earlier, later, root, oldMember, newMember, bound, origin, _, oldPosition, newPosition,
      sourcePath, shared⟩ :=
    standard_intermediate_pair_source positive standard rowPositive room before inside path same
  refine ⟨earlier, later, root, oldMember, newMember, bound, origin, oldPosition, newPosition, ?_⟩
  let clipped : Entry d := { earlier with tail := Source.takeAbove (earlier.coordinates[0]?.getD 0) earlier.tail }
  have oldSound := standard_entries_sound positive standard earlier oldMember
  have newSound := standard_entries_sound positive standard later newMember
  have clippedSound : clipped.Sound :=
    ⟨oldSound.coherent, oldSound.valid, oldSound.view, oldSound.materials, Source.rootBlock_finiteLegal oldSound.legal⟩
  have clippedOrigin : clipped.OriginAt later.source later.visible later.owners later.materials later.state root :=
    ⟨origin.sourceEq, origin.visibleEq, origin.materialEq, origin.ownersPrefix, origin.labelEq,
      origin.attachmentEq, origin.statePrefix, origin.beforeRepresentative⟩
  have localPrefix : clipped.result <+: earlier.result := by
    simp only [Entry.result, Entry.remaining, clipped, Parents.annotate, encode_split_head]
    exact encode_takeAbove_prefix d earlier.tail (earlier.coordinates[0]?.getD 0) _ _ _
  have globalPrefix := localPrefix.trans (entries_execution d e [] [] [] [] [] earlier oldMember).resultPrefix
  have control := clippedOrigin.partial_rebase_control clippedSound newSound rowPositive room bound sourcePath shared.symm
  let delta := (List.range cut).map (fun k => later.coordinates[k]?.getD 0 - earlier.coordinates[k]?.getD 0)
  let shifted := encode d (Parents.annotate d later.source
    (Source.copied d root cut delta 1 earlier.source (List.replicate root 0)
      (Source.rootBlock earlier.remaining))) later.visible later.state
  have rows : ∀ j, j < d →
      RowRebaseTrace j earlier.state.length
        (if j < cut then Parents.reading (BMS.parentTable (d + 2) (fromSource d e)) j b -
          Parents.reading (BMS.parentTable (d + 2) (fromSource d e)) j a else 0)
        earlier.state later.state clipped.result shifted := by
    intro j row
    have vectorValue := origin.partial_rebase_vector oldSound newSound rowPositive room bound sourcePath shared.symm j row
    have oldRead := earlier.first_reading_in (entries_execution d e [] [] [] [] [] earlier oldMember).resultPrefix row
    have newRead := later.first_reading_in (entries_execution d e [] [] [] [] [] later newMember).resultPrefix row
    change Parents.reading (BMS.parentTable (d + 2) (fromSource d e)) j earlier.state.length = _ at oldRead
    change Parents.reading (BMS.parentTable (d + 2) (fromSource d e)) j later.state.length = _ at newRead
    rw [oldPosition] at oldRead
    rw [newPosition] at newRead
    let amount := if j < cut then Parents.reading (BMS.parentTable (d + 2) (fromSource d e)) j b -
        Parents.reading (BMS.parentTable (d + 2) (fromSource d e)) j a else 0
    have headValue : vector later.state later.visible (Parents.label d later.source
          (Source.shift earlier.coordinates cut delta 1)) j =
        vector earlier.state earlier.visible (Parents.label d earlier.source earlier.coordinates) j + amount := by
      rw [vectorValue]
      by_cases low : j < cut
      · have ancestor := path.lower_row (BMS.parentTable_coherent (d + 2) (fromSource d e))
          (by omega : cut - 1 < d + 2) (by omega : j ≤ cut - 1)
        have ordered := ancestor.reading_le (BMS.parentTable_coherent (d + 2) (fromSource d e))
        simp only [low, if_true, amount]
        rw [← oldRead, ← newRead]
        omega
      · simp only [low, if_false, amount, Nat.add_zero]
    exact clippedOrigin.partial_rebase_row clippedSound newSound rowPositive room bound
      sourcePath shared.symm j amount row headValue
  have complete : BMS.block (fromSource d e) earlier.state.length =
      (matrix clipped.result).drop earlier.state.length := standard_entry_source_block positive standard oldMember
  have result := full_interval_eq_rebase globalPrefix (destination := b) (cut := cut)
    (by simpa only [fromSource, matrix, List.length_map] using inside) (by omega) control
    (by simpa only [fromSource, clipped, Entry.remaining, Source.rootBlock, shifted, delta, oldPosition] using rows)
    clipped.first_lt_result complete
  simpa only [fromSource, clipped, Entry.remaining, Source.rootBlock, oldPosition, newPosition] using result.symm

end BTnSSBMS.Encoder
