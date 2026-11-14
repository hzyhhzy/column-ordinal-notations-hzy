import BTnSSBMS.SourceBlockTransport
import BTnSSBMS.EntryOrder

/-!
An exact comparison reduction for every actual ordinary-row target pair.
No source SB inequality is assumed or claimed: the comparison is reduced
to the two complete source blocks, in one actual entering environment.
-/
namespace BTnSSBMS.Encoder

theorem Entry.OriginAt.rebased_rootBlock_legal {d : Nat} {earlier later : Entry d} {root cut : Nat}
    (origin : earlier.OriginAt later.source later.visible later.owners later.materials later.state root)
    (oldSound : earlier.Sound) (newSound : later.Sound)
    (positive : 0 < cut) (room : cut < d) (inside : root < later.source.length)
    (path : Parents.Ancestor (later.source ++ [Parents.label d later.source later.coordinates])
      (cut - 1) root later.source.length)
    (same : (Parents.label d later.source later.coordinates).parents[cut]?.join =
      Parents.parent later.source cut root) :
    let delta := (List.range cut).map
      (fun j => later.coordinates[j]?.getD 0 - earlier.coordinates[j]?.getD 0)
    Source.FiniteLegal d later.source
      (Source.copied d root cut delta 1 earlier.source (List.replicate root 0)
        (Source.rootBlock earlier.remaining)) := by
  have legal := Source.rootBlock_finiteLegal oldSound.legal
  have clippedLegal : Source.FiniteLegal d (later.source.take root)
      (.cons (later.source[root]?.getD default).coordinates earlier.attachments
        (Source.takeAbove (earlier.coordinates[0]?.getD 0) earlier.tail)) := by
    simpa only [Entry.remaining, Source.rootBlock, origin.sourceEq, origin.coordinates] using legal
  have result := Source.partial_rebase_finiteLegal newSound.coherent newSound.valid newSound.unit
    later.coordinates newSound.legal.2.1 positive room inside path same earlier.attachments
    (Source.takeAbove (earlier.coordinates[0]?.getD 0) earlier.tail) clippedLegal
  simpa only [Entry.remaining, Source.rootBlock, origin.sourceEq, origin.coordinates] using result

/-- Exact equality of comparison outcomes for all ordinary numerical
rows. Endpoints, scopes, source geometry, and comparison environments
are constructed from actual target pairs, with no SB premise. -/
theorem standard_intermediate_block_compare {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {a b cut : Nat}
    (rowPositive : 0 < cut) (room : cut < d) (before : a < b) (inside : b < (fromSource d e).length)
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (fromSource d e)) (cut - 1) a b)
    (same : Parents.parent (BMS.parentTable (d + 2) (fromSource d e)) cut a =
      Parents.parent (BMS.parentTable (d + 2) (fromSource d e)) cut b) :
    ∃ earlier later root, earlier ∈ entries d e [] [] [] [] [] ∧
      later ∈ entries d e [] [] [] [] [] ∧ root < later.source.length ∧
      earlier.OriginAt later.source later.visible later.owners later.materials later.state root ∧
      earlier.state.length = a ∧ later.state.length = b ∧
      Parents.Ancestor (later.source ++ [Parents.label d later.source later.coordinates])
        (cut - 1) root later.source.length ∧
      Parents.parent later.source cut root = (Parents.label d later.source later.coordinates).parents[cut]?.join ∧
      (let delta := (List.range cut).map
        (fun j => later.coordinates[j]?.getD 0 - earlier.coordinates[j]?.getD 0)
      matrixCompare (BMS.rebase (d + 2) (fromSource d e) cut a b) (BMS.block (fromSource d e) b) =
        (Source.copied d root cut delta 1 earlier.source (List.replicate root 0)
          (Source.rootBlock earlier.remaining)).compare (listCompare Ord.compare)
            (Source.rootBlock later.remaining)) := by
  obtain ⟨earlier, later, root, oldMember, newMember, bound, origin, oldPosition, newPosition, transported⟩ :=
    standard_intermediate_source_block positive standard rowPositive room before inside path same
  have sourcePath := standard_entry_ancestor_reflect positive standard oldMember newMember origin bound
    (by omega : cut - 1 < d) (by simpa only [oldPosition, newPosition] using path)
  have sourceSame := standard_entry_shared_parent_reflect positive standard oldMember newMember origin bound room
    (by simpa only [oldPosition, newPosition] using same)
  refine ⟨earlier, later, root, oldMember, newMember, bound, origin, oldPosition, newPosition,
    sourcePath, sourceSame, ?_⟩
  dsimp only at transported ⊢
  have oldSound := standard_entries_sound positive standard earlier oldMember
  have newSound := standard_entries_sound positive standard later newMember
  have shiftedLegal := origin.rebased_rootBlock_legal oldSound newSound rowPositive room bound sourcePath sourceSame.symm
  have targetBlock := standard_entry_source_block positive standard newMember
  rw [newPosition] at targetBlock
  rw [transported, targetBlock]
  simpa only [newPosition] using standard_entry_compare positive standard newMember _ _
    shiftedLegal (Source.rootBlock_finiteLegal newSound.legal)

end BTnSSBMS.Encoder
