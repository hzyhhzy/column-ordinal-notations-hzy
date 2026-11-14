import BTnSSBMS.QueryAncestry
import BTnSSBMS.FrameInsertion

/-!
Recover old closing representatives from key-row activation at any real
query, not merely when their binding is already supplied. This handles
loss of a binding and later queries through a different external parent:
activation is tested in that parent's actual saved frame.
-/
namespace BTnSSBMS.Encoder

theorem standard_query_smaller_ancestral {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {entry : Entry d}
    (entryMember : entry ∈ entries d e [] [] [] [] []) :
    FrameAncestral (encode d (Parents.annotate d [] e) [] []) entry.state.length
      (smaller entry.queryFrame entry.completeKey) := by
  have sound := standard_entries_sound positive standard entry entryMember
  let a := Parents.label d entry.source entry.coordinates
  let frame := entry.queryFrame
  let key := entry.completeKey
  let head := queryHead d a key entry.visible entry.state
  have initial := source_queryHead_prefix entryMember
  have localPaths : FrameAncestral head entry.state.length (smaller frame key) := by
    cases found : equal frame key with
    | some bound =>
      have result := reused_head_result entry.state sound.coherent sound.valid sound.view
        (source_entry_framesOrdered entryMember) (source_entry_framesRealized entryMember)
        (standard_entry_framesAncestral positive standard entryMember) entry.coordinates key bound positive found
      have kept := result.2.subset (fun b member => List.mem_append_left _ member)
      change FrameAncestral
        (queryHead d (Parents.label d entry.source entry.coordinates) key entry.visible entry.state)
        entry.state.length (smaller frame key)
      simp only [queryHead]
      change equal (frameAt entry.state (representative entry.visible (Parents.label d entry.source entry.coordinates) (d - 1))) key = some bound at found
      rw [found]
      exact kept
    | none =>
      have zero : HasZero frame := queried_frame_has_zero entry.state entry.visible
        (source_entries_good d e entry entryMember) a (d - 1)
      have nonempty := hasZero_nonempty (fresh_smaller_has_zero zero key found)
      obtain ⟨parent, selected⟩ := fresh_has_representative entry.state sound.view entry.coordinates
        entry.attachments (sound.legal.parented positive).1 found
      obtain ⟨_, _, _, _, belowPaths⟩ := fresh_head_result entry.state sound.coherent sound.valid sound.view
        (source_entry_framesOrdered entryMember) (source_entry_framesRealized entryMember)
        (standard_entry_framesAncestral positive standard entryMember) entry.coordinates key positive parent selected
        (by simpa only [frame, Entry.queryFrame, selected] using nonempty)
      change FrameAncestral
        (queryHead d (Parents.label d entry.source entry.coordinates) key entry.visible entry.state)
        entry.state.length (smaller frame key)
      simp only [queryHead]
      change equal (frameAt entry.state (representative entry.visible (Parents.label d entry.source entry.coordinates) (d - 1))) key = none at found
      rw [found]
      simpa only [frame, Entry.queryFrame, selected] using belowPaths
  exact localPaths.extends initial

/-- Every older self-registered key ancestor of a real first output is
present in that query's retained frame, with its actual latest pointer. -/
theorem standard_query_ancestor_retained {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {entry : Entry d}
    (entryMember : entry ∈ entries d e [] [] [] [] []) {root : Nat}
    (self : SelfLatest (encode d (Parents.annotate d [] e) [] []) root)
    (before : root < entry.state.length)
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (fromSource d e)) d root entry.state.length) :
    ∃ b ∈ smaller entry.queryFrame entry.completeKey, b.latest = some root := by
  let state := encode d (Parents.annotate d [] e) [] []
  let frame := entry.queryFrame
  let below := smaller frame entry.completeKey
  obtain ⟨i, rootOutput⟩ := selfLatest_even_readout (source_framesDense d e) (source_framesRealized d e) self
  have strict := path.reading_lt (BMS.parentTable_coherent _ _) (by omega)
  have rootValue : Parents.reading (BMS.parentTable (d + 2) (fromSource d e)) d root = 2 * i := rootOutput.key_reading
  rw [rootValue, source_query_key_reading entryMember] at strict
  change 2 * i < firstHeight frame entry.completeKey at strict
  have ordered : FrameOrdered frame := queried_frame_ordered (source_entry_framesOrdered entryMember) _
  have dense : FrameDense frame := queried_frame_dense (source_entry_framesDense entryMember) _
  have zero : HasZero frame := queried_frame_has_zero entry.state entry.visible
    (source_entries_good d e entry entryMember) _ _
  have rank := firstHeight_rank ordered dense zero entry.completeKey
  have inside : i < below.length := by dsimp only [below]; omega
  let b := below[i]
  have lookup : below[i]? = some b := List.getElem?_eq_getElem inside
  have member := List.mem_of_getElem? lookup
  have height := frameDense_prefix dense (smaller_prefix ordered entry.completeKey) i b lookup
  obtain ⟨p, latest, pPath, _⟩ := standard_query_smaller_ancestral positive standard entryMember b member
  have original := (queried_frame_realized (source_entry_framesRealized entryMember)
    (representative entry.visible (Parents.label d entry.source entry.coordinates) (d - 1)) b
    (List.mem_filter.mp member).1).1
  rw [latest, height] at original
  have extended := entry.state_prefix_result.trans (entries_execution d e [] [] [] [] [] entry entryMember).resultPrefix
  have same : root = p := key_ancestors_same_height path pPath rootOutput (readout_extends extended original)
  exact ⟨b, member, same ▸ latest⟩

theorem standard_query_key_ancestor_iff_retained {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {entry : Entry d}
    (entryMember : entry ∈ entries d e [] [] [] [] []) {root : Nat}
    (self : SelfLatest (encode d (Parents.annotate d [] e) [] []) root)
    (before : root < entry.state.length) :
    Parents.Ancestor (BMS.parentTable (d + 2) (fromSource d e)) d root entry.state.length ↔
      ∃ b ∈ smaller entry.queryFrame entry.completeKey, b.latest = some root := by
  constructor
  · exact standard_query_ancestor_retained positive standard entryMember self before
  · rintro ⟨b, member, latest⟩
    have boundMember := (List.mem_filter.mp member).1
    have less : Keys.compare b.key entry.completeKey = .lt := by
      simpa only [beq_iff_eq] using (List.mem_filter.mp member).2
    exact (standard_query_key_ancestor_iff positive standard entryMember b boundMember root latest).mpr less

theorem standard_query_key_activation_iff_retained {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {entry : Entry d}
    (entryMember : entry ∈ entries d e [] [] [] [] []) {root : Nat}
    (self : SelfLatest (encode d (Parents.annotate d [] e) [] []) root)
    (before : root < entry.state.length) :
    d < (BMS.thresholds (BMS.parentTable (d + 2) (fromSource d e)) root (d + 1))[entry.state.length]?.getD 0 ↔
      ∃ b ∈ smaller entry.queryFrame entry.completeKey, b.latest = some root := by
  have length := (source_queryHead_prefix entryMember).length_le
  rw [queryHead_length] at length
  have inside : entry.state.length < (fromSource d e).length := by
    simp only [fromSource, matrix, List.length_map]
    omega
  rw [BMS.thresholds_ancestry (d + 2) (fromSource d e) root (d + 1) (by omega)
    entry.state.length inside d]
  simp only [Nat.lt_succ_self, true_and]
  exact standard_query_key_ancestor_iff_retained positive standard entryMember self before

/-- A query through an external frame which no longer retains the old
representative cannot receive its key-row shift. This is about actual
parent search, even if that root occurred earlier in global chronology. -/
theorem standard_query_key_inactive_of_absent {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {entry : Entry d}
    (entryMember : entry ∈ entries d e [] [] [] [] []) {root : Nat}
    (self : SelfLatest (encode d (Parents.annotate d [] e) [] []) root)
    (before : root < entry.state.length)
    (absent : ∀ b ∈ entry.queryFrame, b.latest ≠ some root) :
    (BMS.thresholds (BMS.parentTable (d + 2) (fromSource d e)) root (d + 1))[entry.state.length]?.getD 0 ≤ d := by
  apply Nat.le_of_not_gt
  intro active
  obtain ⟨b, member, latest⟩ :=
    (standard_query_key_activation_iff_retained positive standard entryMember self before).mp active
  exact absent b (List.mem_filter.mp member).1 latest

end BTnSSBMS.Encoder
