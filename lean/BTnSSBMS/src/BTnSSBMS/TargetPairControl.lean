import BTnSSBMS.EntryAncestry

/-!
The actual target intermediate-row pair now supplies every source-entry
and root-geometry condition needed for complete control-row transport.
This closes that applicability issue; numerical block transport and the
block inequalities are distinct remaining obligations.
-/
namespace BTnSSBMS.Encoder

theorem standard_intermediate_pair_control {d : Nat} (positive : 0 < d) {e : NumericalExpr}
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
        (fun j => later.coordinates[j]?.getD 0 - earlier.coordinates[j]?.getD 0)
      SharedTrace earlier.state later.state earlier.result
        (encode d (Parents.annotate d later.source
          (Source.copied d root cut delta 1 earlier.source (List.replicate root 0) earlier.remaining))
          later.visible later.state)) := by
  obtain ⟨earlier, later, root, oldMember, newMember, bound, origin, _, oldPosition, newPosition,
      sourcePath, shared⟩ :=
    standard_intermediate_pair_source positive standard rowPositive room before inside path same
  exact ⟨earlier, later, root, oldMember, newMember, bound, origin, oldPosition, newPosition,
    origin.partial_rebase_control (standard_entries_sound positive standard earlier oldMember)
      (standard_entries_sound positive standard later newMember) rowPositive room bound sourcePath shared.symm⟩

/-- In concrete output form, both control-row suffixes are identical,
and both actual executions append the same number of columns. This is
not an identification of a complete BMS block with the lexical suffix. -/
theorem standard_intermediate_pair_control_suffix {d : Nat} (positive : 0 < d) {e : NumericalExpr}
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
        (fun j => later.coordinates[j]?.getD 0 - earlier.coordinates[j]?.getD 0)
      let shifted := encode d (Parents.annotate d later.source
        (Source.copied d root cut delta 1 earlier.source (List.replicate root 0) earlier.remaining))
        later.visible later.state
      (controlTrace earlier.result).drop a = (controlTrace shifted).drop b ∧
        earlier.result.length - a = shifted.length - b) := by
  obtain ⟨earlier, later, root, oldMember, newMember, bound, origin, oldPosition, newPosition, trace⟩ :=
    standard_intermediate_pair_control positive standard rowPositive room before inside path same
  refine ⟨earlier, later, root, oldMember, newMember, bound, origin, oldPosition, newPosition, ?_⟩
  dsimp only at trace ⊢
  have suffix := trace.suffix
  have length := trace.length
  rw [oldPosition, newPosition] at suffix length
  exact ⟨suffix, by omega⟩

end BTnSSBMS.Encoder
