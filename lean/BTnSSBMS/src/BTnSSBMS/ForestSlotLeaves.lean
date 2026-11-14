import BTnSSBMS.KeyParentTypes
import BTnSSBMS.SourceFiniteClosure

/-!
Forest slots are leaves in the actual key-row parent forest. Slot positions
are traced from the unchanged encoder, including nested and later forests;
they are not identified by a guessed idealized parent table.
-/
namespace BTnSSBMS.Encoder

theorem KeyAnchor.restrict {state next : State d} {position : Nat}
    (anchor : KeyAnchor next position) (extended : state <+: next) (inside : position < state.length) :
    KeyAnchor state position := by
  rcases anchor with ⟨height, col, lookup, key, tag⟩ | self
  · obtain ⟨extra, rfl⟩ := extended
    exact .inl ⟨height, col, by simpa only [List.getElem?_append_left inside] using lookup, key, tag⟩
  · exact .inr (self.restrict extended inside)

def SlotExcluded (state : State d) (position : Nat) : Prop :=
  position < state.length ∧ ¬ KeyAnchor state position

theorem SlotExcluded.extends {state next : State d} {position : Nat}
    (excluded : SlotExcluded state position) (extended : state <+: next) : SlotExcluded next position := by
  have length := extended.length_le
  exact ⟨Nat.lt_of_lt_of_le excluded.1 length, fun anchor => excluded.2 (anchor.restrict extended excluded.1)⟩

theorem emitted_old_frame_excluded {state : State d} (u : Nat → Nat) (height tag : Nat)
    (frame : List Binding) (known : FrameRealized state frame) (notDefinition : tag ≠ 1) :
    SlotExcluded (emit state u height tag frame) state.length := by
  refine ⟨by rw [emit_length]; omega, ?_⟩
  intro anchor
  rcases anchor with ⟨h, col, lookup, _, tagValue⟩ | ⟨col, lookup, b, member, latest⟩
  · have same : col = ⟨row d u height tag, row_width d u height tag, frame⟩ := by
      simpa only [emit, List.getElem?_concat_length, Option.some.injEq] using lookup.symm
    subst col
    have rowTag : (row d u height tag)[d + 1]? = some tag := by simp [row]
    exact notDefinition (Option.some.inj (rowTag.symm.trans tagValue))
  · have same : col = ⟨row d u height tag, row_width d u height tag, frame⟩ := by
      simpa only [emit, List.getElem?_concat_length, Option.some.injEq] using lookup.symm
    subst col
    have output := (known b member).1
    rw [latest] at output
    have earlier := readout_bound output
    omega

mutual
  def slotPositions (d : Nat) (e : ParentExpr) (visible : List Nat) (state : State d) : List Nat :=
    match e with
    | .nil => []
    | .cons a hs tail =>
      let key := Keys.ofColumn d visible.length a hs
      let u := vector state visible a
      let frame := frameAt state (representative visible a (d - 1))
      let below := smaller frame key
      match equal frame key with
      | some bound =>
        slotPositions d tail (visible ++ [state.length])
          (emit state u bound.height 0 (below ++ [{bound with latest := some state.length}]))
      | none =>
        let c := (base below).height
        let guarded := emit (emit state u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 []
        let forests := encodeForests d hs visible u c below guarded
        forestSlotPositions d hs visible u c below guarded ++
          slotPositions d tail (visible ++ [forests.length])
            (emit forests (fun j => u j + 1) (c + 2) 0
              (below ++ [⟨key, c + 2, some forests.length, some state.length⟩]))
  def forestSlotPositions (d : Nat) (hs : Forests ParentLabel) (visible : List Nat)
      (u : Nat → Nat) (c : Nat) (below : List Binding) (state : State d) : List Nat :=
    match hs with
    | .nil => []
    | .cons h hs =>
      let withSlot := emit state (fun j => u j + 2) (c + 2) 0 below
      let withForest := encode d h (visible ++ [state.length]) withSlot
      state.length :: (slotPositions d h (visible ++ [state.length]) withSlot ++
        forestSlotPositions d hs visible u c below withForest)
end

mutual
  theorem encode_slots_excluded (d : Nat) (e : ParentExpr) (visible : List Nat) (state : State d)
      (known : FramesRealized state) :
      ∀ position ∈ slotPositions d e visible state, SlotExcluded (encode d e visible state) position := by
    cases e with
    | nil => intro position member; simp [slotPositions] at member
    | cons a hs tail =>
      have frameKnown := queried_frame_realized known (representative visible a (d - 1))
      have belowKnown := smaller_realized frameKnown (Keys.ofColumn d visible.length a hs)
      simp only [slotPositions, encode]
      split
      next bound found =>
        rw [found]
        exact encode_slots_excluded d tail _ _
          (framesRealized_emit known _ _ _ _ (reused_frame_realized frameKnown _ bound found _))
      next fresh =>
        rw [fresh]
        let key := Keys.ofColumn d visible.length a hs
        let u := vector state visible a
        let below := smaller (frameAt state (representative visible a (d - 1))) key
        let c := (base below).height
        let guarded := emit (emit state u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 []
        let forests := encodeForests d hs visible u c below guarded
        have guardKnown : FramesRealized guarded := framesRealized_emit
          (framesRealized_emit known u (c + 1) 1 [] (empty_frame_realized _))
          (fun j => u j + 1) (c + 2) 2 [] (empty_frame_realized _)
        have guardExtends : state <+: guarded := (emit_extends ..).trans (emit_extends ..)
        have guardBelow : FrameRealized guarded below := frameRealized_extends guardExtends belowKnown
        have forestExtends : guarded <+: forests := encodeForests_extends ..
        have forestKnown := encodeForests_framesRealized d hs visible u c below guarded guardBelow guardKnown
        have forestExcluded := encodeForests_slots_excluded d hs visible u c below guarded guardBelow guardKnown
        have finalKnown := framesRealized_emit forestKnown (fun j => u j + 1) (c + 2) 0 _
          (fresh_frame_realized below (frameRealized_extends forestExtends guardBelow) key c state.length
            (readout_extends ((emit_extends ..).trans forestExtends) (readout_emit state u (c + 1) 1 [])) _)
        have tailExcluded := encode_slots_excluded d tail (visible ++ [forests.length]) _ finalKnown
        intro position member
        rcases List.mem_append.mp member with inside | later
        · exact (forestExcluded position inside).extends ((emit_extends ..).trans (encode_extends ..))
        · exact tailExcluded position later

  theorem encodeForests_slots_excluded (d : Nat) (hs : Forests ParentLabel) (visible : List Nat)
      (u : Nat → Nat) (c : Nat) (below : List Binding) (state : State d)
      (belowKnown : FrameRealized state below) (known : FramesRealized state) :
      ∀ position ∈ forestSlotPositions d hs visible u c below state,
        SlotExcluded (encodeForests d hs visible u c below state) position := by
    cases hs with
    | nil => intro position member; simp [forestSlotPositions] at member
    | cons h hs =>
      let withSlot := emit state (fun j => u j + 2) (c + 2) 0 below
      let withForest := encode d h (visible ++ [state.length]) withSlot
      have slotKnown := framesRealized_emit known (fun j => u j + 2) (c + 2) 0 below
        (frameRealized_extends (emit_extends ..) belowKnown)
      have forestKnown := encode_framesRealized d h (visible ++ [state.length]) withSlot slotKnown
      have forestExtends : withSlot <+: withForest := encode_extends ..
      have forestExcluded := encode_slots_excluded d h (visible ++ [state.length]) withSlot slotKnown
      have restExcluded := encodeForests_slots_excluded d hs visible u c below withForest
        (frameRealized_extends ((emit_extends ..).trans forestExtends) belowKnown) forestKnown
      intro position member
      rcases List.mem_cons.mp member with first | later
      · have same : position = state.length := first
        subst position
        exact (emitted_old_frame_excluded (fun j => u j + 2) (c + 2) 0 below belowKnown (by decide)).extends
          (forestExtends.trans (encodeForests_extends ..))
      · rcases List.mem_append.mp later with inside | rest
        · exact (forestExcluded position inside).extends (encodeForests_extends ..)
        · exact restExcluded position rest
end

/-- For every actual forest slot, all nested and later output is included.
An ancestor path beginning at that slot can only be the reflexive path. -/
theorem source_slot_no_strict_key_descendant (d : Nat) (e : NumericalExpr) (positive : 0 < d)
    (legal : Source.FiniteLegal d [] e) {position endpoint : Nat}
    (slot : position ∈ slotPositions d (Parents.annotate d [] e) [] [])
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (fromSource d e)) d position endpoint) :
    position = endpoint := by
  have excluded := encode_slots_excluded d (Parents.annotate d [] e) [] []
    (by intro i col lookup; simp at lookup) position slot
  exact keyParentsAnchored_no_strict_descendant (source_keyParentsAnchored d e positive legal) excluded.2 path

theorem standard_keyParentsAnchored {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) : KeyParentsAnchored (encode d (Parents.annotate d [] e) [] []) :=
  source_keyParentsAnchored d e positive (Source.standard_finiteLegal positive standard)

theorem standard_slot_no_strict_key_descendant {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {position endpoint : Nat}
    (slot : position ∈ slotPositions d (Parents.annotate d [] e) [] [])
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (fromSource d e)) d position endpoint) :
    position = endpoint :=
  source_slot_no_strict_key_descendant d e positive (Source.standard_finiteLegal positive standard) slot path

theorem standard_guard_no_strict_key_descendant {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {position height endpoint : Nat}
    (guard : Readout (encode d (Parents.annotate d [] e) [] []) position height 2)
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (fromSource d e)) d position endpoint) :
    position = endpoint :=
  keyParentsAnchored_guard_no_strict_descendant (source_framesRealized d e)
    (standard_keyParentsAnchored positive standard) guard path

end BTnSSBMS.Encoder
