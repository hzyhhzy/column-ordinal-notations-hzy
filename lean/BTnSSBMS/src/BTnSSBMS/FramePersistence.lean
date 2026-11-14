import BTnSSBMS.FrameAncestorRecovery

/-!
Every retained binding points to a column whose complete saved frame is
exactly the corresponding prefix of the current frame. Thus surviving
bindings preserve keys, definition pointers and latest pointers together,
not merely their numerical heights. This is a theorem of the real finite
encoder, including skipped forests and restoration after forest exits.
-/
namespace BTnSSBMS.Encoder

def FrameStored (state : State d) (frame : List Binding) : Prop :=
  ∀ i b, frame[i]? = some b → ∀ p, b.latest = some p →
    ∃ col, state[p]? = some col ∧ col.frame = frame.take (i + 1)

def FramesStored (state : State d) : Prop :=
  ∀ col ∈ state, FrameStored state col.frame

theorem empty_frame_stored (state : State d) : FrameStored state [] := by
  intro i b lookup
  simp at lookup

theorem virtual_frame_stored (state : State d) : FrameStored state virtualFrame := by
  intro i b lookup p latest
  have member := List.mem_of_getElem? lookup
  have same : b = zeroBinding := by simpa only [virtualFrame, List.mem_singleton] using member
  simp only [same, zeroBinding] at latest
  cases latest

theorem FrameStored.extends {state next : State d} {frame : List Binding}
    (stored : FrameStored state frame) (initial : state <+: next) : FrameStored next frame := by
  intro i b lookup p latest
  obtain ⟨col, found, saved⟩ := stored i b lookup p latest
  obtain ⟨extra, rfl⟩ := initial
  have inside := (List.getElem?_eq_some_iff.mp found).choose
  exact ⟨col, by rw [List.getElem?_append_left inside]; exact found, saved⟩

theorem FrameStored.restrict {state : State d} {small large : List Binding}
    (stored : FrameStored state large) (initial : small <+: large) : FrameStored state small := by
  obtain ⟨extra, rfl⟩ := initial
  intro i b lookup p latest
  have inside := (List.getElem?_eq_some_iff.mp lookup).choose
  have larger : (small ++ extra)[i]? = some b := by
    rw [List.getElem?_append_left inside]; exact lookup
  obtain ⟨col, found, saved⟩ := stored i b larger p latest
  exact ⟨col, found, by simpa only [List.take_append_of_le_length (by omega : i + 1 ≤ small.length)] using saved⟩

theorem smaller_stored {state : State d} {frame : List Binding}
    (stored : FrameStored state frame) (ordered : FrameOrdered frame) (key : Key) :
    FrameStored state (smaller frame key) := stored.restrict (smaller_prefix ordered key)

theorem framesStored_emit {state : State d} (stored : FramesStored state)
    (u : Nat → Nat) (height tag : Nat) (frame : List Binding)
    (added : FrameStored (emit state u height tag frame) frame) :
    FramesStored (emit state u height tag frame) := by
  intro col member
  rcases List.mem_append.mp member with old | new
  · exact (stored col old).extends (emit_extends ..)
  · have same : col = ⟨row d u height tag, row_width d u height tag, frame⟩ := by simpa using new
    subst col
    exact added

theorem queried_frame_stored {state : State d} (stored : FramesStored state)
    (position : Option Nat) : FrameStored state (frameAt state position) := by
  unfold frameAt
  cases output : position.bind (state[·]?) with
  | none => exact virtual_frame_stored _
  | some col =>
    obtain ⟨p, _, lookup⟩ := Option.bind_eq_some_iff.mp output
    exact stored col (List.mem_of_getElem? lookup)

theorem FrameStored.save {state : State d} {frame : List Binding}
    (stored : FrameStored state frame) (u : Nat → Nat) (height tag : Nat)
    (b : Binding) (latest : b.latest = some state.length) :
    FrameStored (emit state u height tag (frame ++ [b])) (frame ++ [b]) := by
  intro i a lookup p found
  by_cases old : i < frame.length
  · have original : frame[i]? = some a := by simpa only [List.getElem?_append_left old] using lookup
    obtain ⟨col, hit, saved⟩ := (stored.extends (emit_extends state u height tag (frame ++ [b])))
      i a original p found
    refine ⟨col, hit, ?_⟩
    simpa only [List.take_append_of_le_length (by omega : i + 1 ≤ frame.length)] using saved
  · have inside := (List.getElem?_eq_some_iff.mp lookup).choose
    have last : i = frame.length := by simp only [List.length_append, List.length_cons, List.length_nil] at inside; omega
    subst i
    have same : a = b := by simpa only [List.getElem?_concat_length, Option.some.injEq] using lookup.symm
    subst a
    have endpoint : p = state.length := Option.some.inj (found.symm.trans latest)
    subst p
    refine ⟨⟨row d u height tag, row_width d u height tag, frame ++ [b]⟩, List.getElem?_concat_length, ?_⟩
    rw [show frame.length + 1 = (frame ++ [b]).length by simp, List.take_length]

mutual
  theorem encode_framesStored (d : Nat) (e : ParentExpr) (visible : List Nat) (state : State d)
      (ordered : FramesOrdered state) (stored : FramesStored state) :
      FramesStored (encode d e visible state) := by
    cases e with
    | nil => exact stored
    | cons a hs tail =>
      let key := Keys.ofColumn d visible.length a hs
      let frame := frameAt state (representative visible a (d - 1))
      let below := smaller frame key
      let c := (base below).height
      let u := vector state visible a
      let guarded := emit (emit state u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 []
      let forests := encodeForests d hs visible u c below guarded
      have frameOrder : FrameOrdered frame := queried_frame_ordered ordered _
      have belowOrder : FrameOrdered below := smaller_ordered frameOrder key
      have belowStored : FrameStored state below := smaller_stored (queried_frame_stored stored _) frameOrder key
      simp only [encode]
      split
      next bound found =>
        apply encode_framesStored d tail
        · exact framesOrdered_emit ordered _ _ _ _ (reused_frame_ordered frameOrder key bound found _)
        · exact framesStored_emit stored _ _ _ _ (belowStored.save u bound.height 0
            {bound with latest := some state.length} rfl)
      next fresh =>
        have guardOrder : FramesOrdered guarded := framesOrdered_emit
          (framesOrdered_emit ordered u (c + 1) 1 [] (by simp [FrameOrdered]))
          (fun j => u j + 1) (c + 2) 2 [] (by simp [FrameOrdered])
        have guardStored : FramesStored guarded := framesStored_emit
          (framesStored_emit stored u (c + 1) 1 [] (empty_frame_stored _))
          (fun j => u j + 1) (c + 2) 2 [] (empty_frame_stored _)
        have initial : state <+: forests := (emit_extends ..).trans
          ((emit_extends ..).trans (encodeForests_extends ..))
        have forestStored := encodeForests_framesStored d hs visible u c below guarded belowOrder
          (belowStored.extends ((emit_extends ..).trans (emit_extends ..))) guardOrder guardStored
        apply encode_framesStored d tail
        · exact framesOrdered_emit (encodeForests_framesOrdered d hs _ _ _ _ _ belowOrder guardOrder)
            _ _ _ _ (fresh_frame_ordered frameOrder key _ _)
        · exact framesStored_emit forestStored _ _ _ _ ((belowStored.extends initial).save
            (fun j => u j + 1) (c + 2) 0 ⟨key, c + 2, some forests.length, some state.length⟩ rfl)

  theorem encodeForests_framesStored (d : Nat) (hs : Forests ParentLabel) (visible : List Nat)
      (u : Nat → Nat) (c : Nat) (below : List Binding) (state : State d)
      (belowOrder : FrameOrdered below) (belowStored : FrameStored state below)
      (ordered : FramesOrdered state) (stored : FramesStored state) :
      FramesStored (encodeForests d hs visible u c below state) := by
    cases hs with
    | nil => exact stored
    | cons h hs =>
      let slot := emit state (fun j => u j + 2) (c + 2) 0 below
      let forest := encode d h (visible ++ [state.length]) slot
      have slotOrder : FramesOrdered slot := framesOrdered_emit ordered _ _ _ below belowOrder
      have slotStored : FramesStored slot := framesStored_emit stored _ _ _ below (belowStored.extends (emit_extends ..))
      have forestStored := encode_framesStored d h (visible ++ [state.length]) slot slotOrder slotStored
      have initial : state <+: forest := (emit_extends ..).trans (encode_extends ..)
      exact encodeForests_framesStored d hs visible u c below forest belowOrder (belowStored.extends initial)
        (encode_framesOrdered d h _ slot slotOrder) forestStored
end

theorem source_framesStored (d : Nat) (e : NumericalExpr) :
    FramesStored (encode d (Parents.annotate d [] e) [] []) :=
  encode_framesStored d _ [] [] (by intro col member; simp at member) (by intro col member; simp at member)

end BTnSSBMS.Encoder
