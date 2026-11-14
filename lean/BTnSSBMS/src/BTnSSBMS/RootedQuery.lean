import BTnSSBMS.RootedSaving

/-!
Activation-sensitive query bounds with the gate carried by the frame
invariant. Equality at an even shift also forces the same query branch;
equality at the full pool shift forces every insertion to survive.
-/
namespace BTnSSBMS.Encoder

theorem firstHeight_even_shift_freshBit {old new : List Binding}
    (oldOrdered : FrameOrdered old) (oldDense : FrameDense old) (oldZero : HasZero old)
    (newOrdered : FrameOrdered new) (newDense : FrameDense new) (newZero : HasZero new)
    (oldKey newKey : Key) (shift : Nat)
    (same : firstHeight new newKey = firstHeight old oldKey + 2 * shift) :
    freshBit new newKey = freshBit old oldKey := by
  have oldRank := firstHeight_rank oldOrdered oldDense oldZero oldKey
  have newRank := firstHeight_rank newOrdered newDense newZero newKey
  have oldBit := freshBit_le_one old oldKey
  have newBit := freshBit_le_one new newKey
  omega

theorem freshBit_eq_branch {old new : List Binding} {oldKey newKey : Key}
    (same : freshBit new newKey = freshBit old oldKey) :
    equal new newKey = none ↔ equal old oldKey = none := by
  cases oldFound : equal old oldKey <;> cases newFound : equal new newKey <;>
    simp_all [freshBit]

theorem RekeyedInsertion.equal_shift_forces_full {keyOf : Binding → Key}
    {old new : List Binding} {pool : List Key}
    (splice : RekeyedInsertion keyOf old new pool)
    (oldOrdered : FrameOrdered old) (oldDense : FrameDense old) (oldZero : HasZero old)
    (newOrdered : FrameOrdered new) (newDense : FrameDense new) (newZero : HasZero new)
    (oldKey newKey : Key)
    (comparisons : ∀ b ∈ old, Keys.compare (keyOf b) newKey = Keys.compare b.key oldKey)
    (same : firstHeight new newKey = firstHeight old oldKey + 2 * pool.length) :
    splice.inserted = pool ∧ (∀ k ∈ pool, Keys.compare k newKey = .lt) ∧
      freshBit new newKey = freshBit old oldKey := by
  let f := fun b : Binding => {b with key := keyOf b}
  have related := KeyFrameRel.map_preserving_height old f (fun _ => rfl)
  have balance := (splice.toInsertion f (fun _ _ => rfl)).rekey_height_balance related
    oldOrdered oldDense oldZero newOrdered newDense newZero oldKey newKey comparisons
  have sameBit := firstHeight_even_shift_freshBit oldOrdered oldDense oldZero
    newOrdered newDense newZero oldKey newKey pool.length same
  have countLe := List.length_filter_le (fun k => Keys.compare k newKey == .lt) splice.inserted
  have poolLe := splice.bounded.length_le
  change firstHeight new newKey + freshBit new newKey = firstHeight old oldKey + freshBit old oldKey +
    2 * (splice.inserted.filter (fun k => Keys.compare k newKey == .lt)).length at balance
  have count : (splice.inserted.filter (fun k => Keys.compare k newKey == .lt)).length =
      splice.inserted.length := by omega
  have full : splice.inserted = pool := splice.bounded.eq_of_length (by omega)
  refine ⟨full, ?_, sameBit⟩
  intro k member
  rw [← full] at member
  simpa only [beq_iff_eq] using List.length_filter_eq_length_iff.mp count k member

/-- The old frame can have lost the original representative entirely.
No separate interval premise or supplied root binding is required. -/
theorem standard_rooted_query_height {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {entry : Entry d}
    (entryMember : entry ∈ entries d e [] [] [] [] []) {root : Nat}
    (self : SelfLatest (encode d (Parents.annotate d [] e) [] []) root)
    (before : root < entry.state.length)
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
    let active := d < (BMS.thresholds (BMS.parentTable (d + 2) (fromSource d e)) root (d + 1))[entry.state.length]?.getD 0
    ∀ new, FrameOrdered new → FrameDense new → HasZero new → ∀ pool,
      RootedInsertion root (fun b => (f b).key) entry.queryFrame new pool →
      firstHeight new newKey ≤
        Parents.reading (BMS.parentTable (d + 2) (fromSource d e)) d entry.state.length +
        (if active then 2 * pool.length else 0) ∧
      (¬ active → firstHeight new newKey =
        Parents.reading (BMS.parentTable (d + 2) (fromSource d e)) d entry.state.length) := by
  dsimp only
  intro new newOrdered newDense newZero pool splice
  have sound := standard_entries_sound positive standard entry entryMember
  have comparisons := sound.query.relocation_comparisons targetCoherent targetValid targetUnit view targetWidth positive
  have oldOrdered : FrameOrdered entry.queryFrame := queried_frame_ordered (source_entry_framesOrdered entryMember) _
  have oldDense : FrameDense entry.queryFrame := queried_frame_dense (source_entry_framesDense entryMember) _
  have oldZero : HasZero entry.queryFrame := queried_frame_has_zero entry.state entry.visible
    (source_entries_good d e entry entryMember) _ _
  have oldKey : queryKey d entry.source entry.coordinates entry.attachments = entry.completeKey := by
    simp only [queryKey, Entry.completeKey, sound.view.length]
  rw [oldKey] at comparisons
  have criterion := standard_query_key_activation_iff_retained positive standard entryMember self before
  rw [source_query_key_reading entryMember]
  exact ⟨splice.height_le_activated oldOrdered oldDense oldZero newOrdered newDense newZero
    _ _ comparisons _ criterion.mpr,
    fun inactive => splice.height_eq_of_inactive oldOrdered oldDense oldZero newOrdered newDense newZero
      _ _ comparisons (fun retained => inactive (criterion.mpr retained))⟩

end BTnSSBMS.Encoder
