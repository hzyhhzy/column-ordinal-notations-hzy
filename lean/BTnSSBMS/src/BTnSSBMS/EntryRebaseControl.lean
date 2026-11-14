import BTnSSBMS.EncoderEntryOrigins
import BTnSSBMS.PartialRebaseControl

/-!
Partial-rebase control transport at genuinely occurring source entries.
The immutable state and lexical-prefix hypotheses are now obtained from
the complete trace's visible origins, not required of the caller. Source
root geometry remains explicit; recovering it from every target block
pair is a separate step.
-/
namespace BTnSSBMS.Encoder

theorem Entry.OriginAt.coordinates {d : Nat} {source : ParentContext} {visible owners : List Nat}
    {materials : List (Forests (List Nat))} {state : State d} {i : Nat} {entry : Entry d}
    (origin : entry.OriginAt source visible owners materials state i) :
    entry.coordinates = (source[i]?.getD default).coordinates := by
  simpa only [Parents.label] using congrArg ParentLabel.coordinates origin.labelEq

theorem Entry.OriginAt.partial_rebase_control {d : Nat} {earlier later : Entry d} {root cut : Nat}
    (origin : earlier.OriginAt later.source later.visible later.owners later.materials later.state root)
    (oldSound : earlier.Sound) (newSound : later.Sound)
    (positive : 0 < cut) (room : cut < d) (insideRoot : root < later.source.length)
    (path : Parents.Ancestor (later.source ++ [Parents.label d later.source later.coordinates])
      (cut - 1) root later.source.length)
    (same : (Parents.label d later.source later.coordinates).parents[cut]?.join =
      Parents.parent later.source cut root) :
    let delta := (List.range cut).map
      (fun j => later.coordinates[j]?.getD 0 - earlier.coordinates[j]?.getD 0)
    SharedTrace earlier.state later.state earlier.result
      (encode d (Parents.annotate d later.source
        (Source.copied d root cut delta 1 earlier.source (List.replicate root 0) earlier.remaining))
        later.visible later.state) := by
  have legal : Source.FiniteLegal d (later.source.take root)
      (.cons (later.source[root]?.getD default).coordinates earlier.attachments earlier.tail) := by
    simpa only [Entry.remaining, origin.sourceEq, origin.coordinates] using oldSound.legal
  have known : VisibleMaterials d (later.source.take root) earlier.visible earlier.owners earlier.materials
      earlier.state := by simpa only [origin.sourceEq] using oldSound.materials
  have oldView : Parents.NumericalView d (later.source.take root)
      (BMS.parentTable (d + 2) (matrix earlier.state)) earlier.visible := by
    simpa only [origin.sourceEq] using oldSound.view
  have visiblePrefix : earlier.visible <+: later.visible := by
    rw [origin.visibleEq]
    exact List.take_prefix _ _
  have result := partial_rebase_encode_control newSound.coherent newSound.valid newSound.unit
    later.coordinates newSound.legal.2.1 positive room insideRoot path same earlier.attachments earlier.tail
    legal known oldView newSound.view newSound.width visiblePrefix origin.statePrefix
  simpa only [Entry.result, Entry.remaining, origin.sourceEq, origin.coordinates] using result

/-- Every visible source root has a sound historical snapshot to which
the complete actual control-row transport applies. No old-state prefix,
old visible prefix, query equality, or frame pairing is assumed. -/
theorem standard_visible_partial_rebase_control {d : Nat} {e : NumericalExpr}
    (standard : Source.Standard d e) {later : Entry d}
    (laterMember : later ∈ entries d e [] [] [] [] []) {root cut : Nat}
    (positive : 0 < cut) (room : cut < d) (insideRoot : root < later.source.length)
    (path : Parents.Ancestor (later.source ++ [Parents.label d later.source later.coordinates])
      (cut - 1) root later.source.length)
    (same : (Parents.label d later.source later.coordinates).parents[cut]?.join =
      Parents.parent later.source cut root) :
    ∃ earlier, earlier ∈ entries d e [] [] [] [] [] ∧ earlier.Sound ∧
      earlier.OriginAt later.source later.visible later.owners later.materials later.state root ∧
      (let delta := (List.range cut).map
        (fun j => later.coordinates[j]?.getD 0 - earlier.coordinates[j]?.getD 0)
      SharedTrace earlier.state later.state earlier.result
        (encode d (Parents.annotate d later.source
          (Source.copied d root cut delta 1 earlier.source (List.replicate root 0) earlier.remaining))
          later.visible later.state)) := by
  obtain ⟨earlier, member, sound, origin⟩ := standard_visible_entry_origin (by omega) standard laterMember insideRoot
  exact ⟨earlier, member, sound, origin, origin.partial_rebase_control sound
    (standard_entries_sound (by omega) standard later laterMember) positive room insideRoot path same⟩

end BTnSSBMS.Encoder
