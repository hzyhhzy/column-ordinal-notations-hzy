import BTnSSBMS.QueryAncestorRecovery
import BTnSSBMS.RekeyInsertion

/-!
Join rekeyed insertion bounds to the actual BMS copy activation, rather
than shifting every column. The whole-run frame-splice invariant is an
explicit outstanding premise; this file does not assert block coverage.
-/
namespace BTnSSBMS.Encoder

theorem keys_below_inserted_of_not_above (pivot query : Key) (inserted : List Key)
    (interval : ∀ k ∈ inserted, Keys.compare pivot k = .lt)
    (notAbove : Keys.compare pivot query ≠ .lt) :
    ∀ k ∈ inserted, Keys.compare query k = .lt := by
  intro k member
  cases compared : Keys.compare query pivot with
  | lt => exact Keys.compare_lt_trans _ _ _ compared (interval k member)
  | eq => simpa only [Keys.compare_eq_imp _ _ compared] using interval k member
  | gt =>
    have reverse : Keys.compare pivot query = .lt := by
      rw [Keys.compare_oriented, compared]; rfl
    exact False.elim (notAbove reverse)

/-- The old representative is active only for a query above its key.
Below that gate, every inserted key is cut away and there is no shift. -/
theorem FrameKeyInsertion.rekey_height_le_activated {keyOf : Binding → Key} {old relocated new : List Binding}
    (splice : FrameKeyInsertion relocated new) (related : KeyFrameRel keyOf old relocated)
    (oldOrdered : FrameOrdered old) (oldDense : FrameDense old) (oldZero : HasZero old)
    (newOrdered : FrameOrdered new) (newDense : FrameDense new) (newZero : HasZero new)
    (oldKey newKey : Key)
    (comparisons : ∀ b ∈ old, Keys.compare (keyOf b) newKey = Keys.compare b.key oldKey)
    (bound : Binding) (member : bound ∈ old)
    (interval : ∀ k ∈ splice.inserted, Keys.compare (keyOf bound) k = .lt) :
    firstHeight new newKey ≤ firstHeight old oldKey +
      if Keys.compare bound.key oldKey = .lt then 2 * splice.inserted.length else 0 := by
  by_cases active : Keys.compare bound.key oldKey = .lt
  · rw [if_pos active]
    exact splice.rekey_height_le_shift related oldOrdered oldDense oldZero newOrdered newDense newZero
      oldKey newKey comparisons
  · rw [if_neg active, Nat.add_zero]
    have below := keys_below_inserted_of_not_above (keyOf bound) newKey splice.inserted interval
      (by rwa [comparisons bound member])
    exact Nat.le_of_eq (splice.rekey_height_eq_below related oldOrdered oldDense oldZero newOrdered newDense newZero
      oldKey newKey comparisons below)

/-- The same bound for a real source entry, its genuinely relocated
attachments, and the threshold computed by the frozen BMS algorithm.
Only the frame splice and its inserted-key interval remain assumptions;
query comparison and key-row activation are derived, not assumed. -/
theorem standard_relocated_query_height_bound {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {entry : Entry d}
    (entryMember : entry ∈ entries d e [] [] [] [] [])
    (target : ParentContext) (moved : List Nat)
    (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
    (targetUnit : Parents.UnitSteps d target)
    (view : Parents.NumericalView d entry.source target moved)
    (targetWidth : ∀ i, i < target.length → (target[i]?.getD default).coordinates.length = d) :
    let f := rekeyBinding d entry.source target entry.visible moved entry.materials
    let newCoordinates := Source.relocationHead d entry.source target moved entry.coordinates
    let newAttachments := Source.relocateForests d
      (entry.source ++ [Parents.label d entry.source entry.coordinates])
      (target ++ [Parents.label d target newCoordinates]) (moved ++ [target.length]) entry.attachments
    let newKey := queryKey d target newCoordinates newAttachments
    ∀ new, FrameOrdered new → FrameDense new → HasZero new →
      ∀ splice : FrameKeyInsertion (entry.queryFrame.map f) new,
      ∀ bound ∈ entry.queryFrame, ∀ root, bound.latest = some root →
        (∀ k ∈ splice.inserted, Keys.compare (f bound).key k = .lt) →
        firstHeight new newKey ≤
          Parents.reading (BMS.parentTable (d + 2) (fromSource d e)) d entry.state.length +
          if d < (BMS.thresholds (BMS.parentTable (d + 2) (fromSource d e)) root (d + 1))[entry.state.length]?.getD 0
          then 2 * splice.inserted.length else 0 := by
  dsimp only
  intro new newOrdered newDense newZero splice bound member root latest interval
  have sound := standard_entries_sound positive standard entry entryMember
  let f := rekeyBinding d entry.source target entry.visible moved entry.materials
  have related := KeyFrameRel.map_preserving_height entry.queryFrame f
    (rekeyBinding_height d entry.source target entry.visible moved entry.materials)
  have comparisons := sound.query.relocation_comparisons targetCoherent targetValid targetUnit view targetWidth positive
  have oldOrdered : FrameOrdered entry.queryFrame := queried_frame_ordered (source_entry_framesOrdered entryMember) _
  have oldDense : FrameDense entry.queryFrame := queried_frame_dense (source_entry_framesDense entryMember) _
  have oldZero : HasZero entry.queryFrame := queried_frame_has_zero entry.state entry.visible
    (source_entries_good d e entry entryMember) _ _
  have scalar := splice.rekey_height_le_activated related oldOrdered oldDense oldZero newOrdered newDense newZero
    _ _ comparisons bound member interval
  have oldKey : queryKey d entry.source entry.coordinates entry.attachments = entry.completeKey := by
    simp only [queryKey, Entry.completeKey, sound.view.length]
  rw [oldKey] at scalar
  have criterion := standard_query_key_activation_iff positive standard entryMember bound member root latest
  rw [source_query_key_reading entryMember]
  by_cases active : d < (BMS.thresholds (BMS.parentTable (d + 2) (fromSource d e)) root (d + 1))[entry.state.length]?.getD 0
  · simpa only [if_pos active, if_pos (criterion.mp active)] using scalar
  · have missing : Keys.compare bound.key entry.completeKey ≠ .lt := fun yes => active (criterion.mpr yes)
    simpa only [if_neg active, if_neg missing] using scalar

end BTnSSBMS.Encoder
