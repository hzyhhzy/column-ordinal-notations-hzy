import BTnSSBMS.InsertionSaving
import BTnSSBMS.EncoderHeadState

/-!
Connect the finite splice calculation to the actual complete-head
operation, including new definitions, skipped/replayed forests and the
restored closing column. The theorem tracks the saved key lists, not the
number or order of all intervening columns.
-/
namespace BTnSSBMS.Encoder

def headFrame (d : Nat) (a : ParentLabel) (hs : Forests ParentLabel)
    (visible : List Nat) (state : State d) : List Binding :=
  let headed := headState d a hs visible state
  frameAt headed (some (headed.length - 1))

theorem frameAt_emit_last (state : State d) (u : Nat → Nat) (height tag : Nat)
    (frame : List Binding) :
    frameAt (emit state u height tag frame) (some ((emit state u height tag frame).length - 1)) = frame := by
  rw [emit_length, Nat.add_sub_cancel]
  simp only [frameAt, Option.bind_some, emit, List.getElem?_concat_length]

theorem headFrame_keys (d : Nat) (a : ParentLabel) (hs : Forests ParentLabel)
    (visible : List Nat) (state : State d) :
    (headFrame d a hs visible state).map Binding.key =
      (smaller (frameAt state (representative visible a (d - 1)))
        (Keys.ofColumn d visible.length a hs)).map Binding.key ++ [Keys.ofColumn d visible.length a hs] := by
  simp only [headFrame, headState, encode]
  split
  next bound found =>
    have keyEq : bound.key = Keys.ofColumn d visible.length a hs :=
      Keys.compare_eq_imp _ _ (by simpa only [beq_iff_eq] using List.find?_some found)
    simp only [frameAt_emit_last, List.map_append, List.map_cons, List.map_nil, keyEq]
  next fresh =>
    simp only [frameAt_emit_last, List.map_append, List.map_cons, List.map_nil]

def FrameKeyInsertion.after_head {d : Nat} {oldState newState : State d}
    {oldVisible newVisible : List Nat} {a b : ParentLabel} {hs ks : Forests ParentLabel}
    (splice : FrameKeyInsertion
      (frameAt oldState (representative oldVisible a (d - 1)))
      (frameAt newState (representative newVisible b (d - 1))))
    (sameKey : Keys.ofColumn d oldVisible.length a hs = Keys.ofColumn d newVisible.length b ks) :
    FrameKeyInsertion (headFrame d a hs oldVisible oldState) (headFrame d b ks newVisible newState) where
  before := (splice.filtered (Keys.ofColumn d oldVisible.length a hs)).before
  inserted := (splice.filtered (Keys.ofColumn d oldVisible.length a hs)).inserted
  after := (splice.filtered (Keys.ofColumn d oldVisible.length a hs)).after ++ [Keys.ofColumn d oldVisible.length a hs]
  old_keys := by
    rw [headFrame_keys, (splice.filtered (Keys.ofColumn d oldVisible.length a hs)).old_keys,
      List.append_assoc]
  new_keys := by
    rw [headFrame_keys, ← sameKey, (splice.filtered (Keys.ofColumn d oldVisible.length a hs)).new_keys,
      List.append_assoc]

theorem FrameKeyInsertion.after_head_interval {d : Nat} {oldState newState : State d}
    {oldVisible newVisible : List Nat} {a b : ParentLabel} {hs ks : Forests ParentLabel}
    (splice : FrameKeyInsertion
      (frameAt oldState (representative oldVisible a (d - 1)))
      (frameAt newState (representative newVisible b (d - 1))))
    (sameKey : Keys.ofColumn d oldVisible.length a hs = Keys.ofColumn d newVisible.length b ks) :
    (splice.after_head sameKey).inserted = splice.inserted.filter
      (fun k => Keys.compare k (Keys.ofColumn d oldVisible.length a hs) == .lt) := rfl

/-- The first differing query settles a real-column comparison, so later
forest material and length differences cannot undo that strict decision.
The numerical coordinates are aligned explicitly; their transport is a
separate obligation in the whole-block proof. -/
theorem FrameKeyInsertion.first_column_decides {left right : List Binding}
    (splice : FrameKeyInsertion left right)
    (oldOrdered : FrameOrdered left) (oldDense : FrameDense left) (oldZero : HasZero left)
    (newOrdered : FrameOrdered right) (newDense : FrameDense right) (newZero : HasZero right)
    (key : Key) (notAbove : ¬ ∀ k ∈ splice.inserted, Keys.compare k key = .lt)
    (d : Nat) (u : Nat → Nat) (oldTag newTag : Nat) (oldTail newTail : Matrix) :
    MatrixFirstLt (row d u (firstHeight right key) newTag :: newTail)
      (row d u (firstHeight left key + 2 * splice.inserted.length) oldTag :: oldTail) := by
  have strict := splice.height_lt_shift oldOrdered oldDense oldZero newOrdered newDense newZero key notAbove
  refine ⟨[], _, _, newTail, oldTail, rfl, rfl, ?_⟩
  apply columnCompare_lt_at _ _ d (by rw [row_width]; omega) (by rw [row_width]; omega)
  · intro j room
    rw [row_numerical_reading d _ _ _ j room, row_numerical_reading d _ _ _ j room]
  · simpa only [row_key_reading] using strict

end BTnSSBMS.Encoder
