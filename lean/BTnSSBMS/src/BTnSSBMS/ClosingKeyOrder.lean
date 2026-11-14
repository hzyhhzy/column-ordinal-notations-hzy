import BTnSSBMS.VisibleClosingOrigins

/-! Complete source keys on a strict actual closing-representative chain. -/
namespace BTnSSBMS.Encoder

def Entry.completeKey (entry : Entry d) : Key :=
  Keys.ofColumn d entry.visible.length (Parents.label d entry.source entry.coordinates)
    (Parents.annotateForests d (entry.source ++ [Parents.label d entry.source entry.coordinates]) entry.attachments)

private theorem emitted_current_binding (state : State d) (u : Nat → Nat)
    (height : Nat) (below : List Binding) (b : Binding) (key : Key)
    (keyEq : b.key = key) (latest : b.latest = some state.length) :
    ∃ col binding, (emit state u height 0 (below ++ [b]))[state.length]? = some col ∧
      binding ∈ col.frame ∧ binding.key = key ∧ binding.latest = some state.length :=
  ⟨_, b, List.getElem?_concat_length, List.mem_append_right _ (List.mem_singleton_self _), keyEq, latest⟩

theorem headState_current_binding (d : Nat) (a : ParentLabel) (hs : Forests ParentLabel)
    (visible : List Nat) (state : State d) :
    ∃ col binding, (headState d a hs visible state)[(headState d a hs visible state).length - 1]? = some col ∧
      binding ∈ col.frame ∧ binding.key = Keys.ofColumn d visible.length a hs ∧
      binding.latest = some ((headState d a hs visible state).length - 1) := by
  simp only [headState, encode]
  split
  next bound found =>
    have keyEq : bound.key = Keys.ofColumn d visible.length a hs :=
      Keys.compare_eq_imp _ _ (by simpa only [beq_iff_eq] using List.find?_some found)
    simp only [emit_length, Nat.add_sub_cancel]
    exact emitted_current_binding _ _ _ _ {bound with latest := some state.length} _ keyEq rfl
  next fresh =>
    simp only [emit_length, Nat.add_sub_cancel]
    exact emitted_current_binding _ _ _ _ _ _ rfl rfl

theorem source_closing_current_binding {d : Nat} {e : NumericalExpr} {entry : Entry d}
    (member : entry ∈ entries d e [] [] [] [] []) :
    ∃ col binding, (encode d (Parents.annotate d [] e) [] [])[entry.closing]? = some col ∧
      binding ∈ col.frame ∧ binding.key = entry.completeKey ∧ binding.latest = some entry.closing := by
  obtain ⟨col, binding, lookup, contains, keyEq, latest⟩ := headState_current_binding d
    (Parents.label d entry.source entry.coordinates)
    (Parents.annotateForests d (entry.source ++ [Parents.label d entry.source entry.coordinates]) entry.attachments)
    entry.visible entry.state
  have initial := entry.headed_prefix_result.trans (entries_execution d e [] [] [] [] [] entry member).resultPrefix
  have inside := (List.getElem?_eq_some_iff.mp lookup).choose
  change entry.closing < entry.headed.length at inside
  refine ⟨col, binding, ?_, contains, keyEq, latest⟩
  obtain ⟨extra, shape⟩ := initial
  rw [← shape, List.getElem?_append_left inside]
  exact lookup

/-- Strict key-row ancestry of restored representatives forces strict
increase of their real complete source keys. It is not inferred from
global chronological order or from a comparison of numerical labels. -/
theorem standard_closing_key_lt {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {earlier later : Entry d}
    (oldMember : earlier ∈ entries d e [] [] [] [] [])
    (newMember : later ∈ entries d e [] [] [] [] [])
    (before : earlier.closing < later.closing)
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (fromSource d e)) d earlier.closing later.closing) :
    Keys.compare earlier.completeKey later.completeKey = .lt := by
  obtain ⟨oldCol, oldBinding, oldLookup, oldContains, oldKey, oldLatest⟩ := source_closing_current_binding oldMember
  obtain ⟨newCol, newBinding, newLookup, newContains, newKey, newLatest⟩ := source_closing_current_binding newMember
  have legal := Source.standard_finiteLegal positive standard
  have known := source_framesRealized d e
  have frames := selfLatest_ancestor_frame_prefix (source_framesDense d e) known
    (source_framesAncestral d e positive legal.separated (legal.parented positive)) (source_framesStored d e)
    (earlier.closing_selfLatest.extends (entries_execution d e [] [] [] [] [] earlier oldMember).resultPrefix)
    (later.closing_selfLatest.extends (entries_execution d e [] [] [] [] [] later newMember).resultPrefix)
    path oldLookup newLookup
  have oldOutput := (frameRealized_extends (List.take_prefix ..)
    (known earlier.closing oldCol oldLookup) oldBinding oldContains).1
  rw [oldLatest] at oldOutput
  have newOutput := (frameRealized_extends (List.take_prefix ..)
    (known later.closing newCol newLookup) newBinding newContains).1
  rw [newLatest] at newOutput
  have heightLt := path.reading_lt (BMS.parentTable_coherent _ _) (by omega)
  change Parents.reading (BMS.parentTable (d + 2) (matrix (encode d (Parents.annotate d [] e) [] [])))
      d earlier.closing < Parents.reading (BMS.parentTable (d + 2) (matrix (encode d (Parents.annotate d [] e) [] [])))
      d later.closing at heightLt
  rw [oldOutput.key_reading, newOutput.key_reading] at heightLt
  have keyLt := (binding_height_iff (source_framesOrdered d e newCol (List.mem_of_getElem? newLookup))
    oldBinding newBinding (frames.subset oldContains) newContains).mpr heightLt
  simpa only [oldKey, newKey] using keyLt

end BTnSSBMS.Encoder
