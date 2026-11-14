import BTnSSBMS.ClosingBlockEncoding
import BTnSSBMS.ForestSlotLeaves

/-!
Every self-registered representative in the actual encoder has a source
entry whose closing column is that representative. Inherited forest slots
cannot register themselves: all pointers in their saved frame already
refer to the earlier state. The trace is the existing execution trace,
not a traversal of forests skipped by the encoder's reuse branch.
-/
namespace BTnSSBMS.Encoder

theorem SelfLatest.emit_cases {state : State d} {u : Nat → Nat}
    {height tag : Nat} {frame : List Binding} {position : Nat}
    (self : SelfLatest (emit state u height tag frame) position) :
    SelfLatest state position ∨
      position = state.length ∧ ∃ b ∈ frame, b.latest = some position := by
  by_cases inside : position < state.length
  · exact .inl (self.restrict (emit_extends ..) inside)
  · obtain ⟨col, lookup, binding⟩ := self
    have bound := (List.getElem?_eq_some_iff.mp lookup).choose
    simp only [emit_length] at bound
    have same : position = state.length := by omega
    subst position
    have column : col = ⟨row d u height tag, row_width d u height tag, frame⟩ := by
      simpa only [emit, List.getElem?_concat_length, Option.some.injEq] using lookup.symm
    exact .inr ⟨rfl, by simpa only [column] using binding⟩

theorem selfLatest_emit_inherited {state : State d} (u : Nat → Nat)
    (height tag : Nat) (frame : List Binding) (known : FrameRealized state frame)
    {position : Nat} (self : SelfLatest (emit state u height tag frame) position) :
    SelfLatest state position := by
  rcases self.emit_cases with old | ⟨same, b, member, latest⟩
  · exact old
  · have output := (known b member).1
    rw [latest] at output
    have earlier := readout_bound output
    omega

theorem headState_selfLatest (d : Nat) (a : ParentLabel) (hs : Forests ParentLabel)
    (visible : List Nat) (state : State d) :
    SelfLatest (headState d a hs visible state) ((headState d a hs visible state).length - 1) := by
  simp only [headState, encode]
  split
  next bound found =>
    simp only [emit_length, Nat.add_sub_cancel]
    exact selfLatest_emit _ _ _ _ _ {bound with latest := some state.length}
      (List.mem_append_right _ (by simp)) rfl
  next fresh =>
    simp only [emit_length, Nat.add_sub_cancel]
    exact selfLatest_emit _ _ _ _ _ _ (List.mem_append_right _ (List.mem_singleton_self _)) rfl

mutual
  theorem entries_selfLatest_origins (d : Nat) (e : NumericalExpr) (source : ParentContext)
      (visible owners : List Nat) (materials : List (Forests (List Nat))) (state : State d)
      (known : FramesRealized state) (position : Nat)
      (self : SelfLatest (encode d (Parents.annotate d source e) visible state) position) :
      SelfLatest state position ∨
        ∃ entry ∈ entries d e source visible owners materials state, entry.closing = position := by
    cases e with
    | nil => exact .inl self
    | cons coordinates hs tail =>
      let a := Parents.label d source coordinates
      let annotated := Parents.annotateForests d (source ++ [a]) hs
      let key := Keys.ofColumn d visible.length a annotated
      let frame := frameAt state (representative visible a (d - 1))
      let below := smaller frame key
      let c := (base below).height
      let u := vector state visible a
      let headed := headState d a annotated visible state
      let guarded := emit (emit state u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 []
      let forests := encodeForests d annotated visible u c below guarded
      have headedKnown : FramesRealized headed := encode_framesRealized d (.cons a annotated .nil) visible state known
      have tailSelf : SelfLatest
          (encode d (Parents.annotate d (source ++ [a]) tail) (visible ++ [headed.length - 1]) headed)
          position := by
        simpa only [Parents.annotate, encode_split_head] using self
      rcases entries_selfLatest_origins d tail (source ++ [a]) (visible ++ [headed.length - 1])
          owners (materials ++ [hs]) headed headedKnown position tailSelf with atHead | ⟨entry, member, same⟩
      · cases found : equal frame key with
        | some bound =>
          dsimp only [frame, key] at found
          have atEmit : SelfLatest (emit state u bound.height 0
              (below ++ [{bound with latest := some state.length}])) position := by
            simpa only [headed, headState, encode, found] using atHead
          rcases atEmit.emit_cases with old | ⟨atEnd, _⟩
          · exact .inl old
          · refine .inr ⟨⟨source, coordinates, hs, tail, visible, owners, materials, state⟩,
              List.mem_cons_self, ?_⟩
            change headed.length - 1 = position
            simpa only [headed, headState, encode, found, emit_length, Nat.add_sub_cancel] using atEnd.symm
        | none =>
          dsimp only [frame, key] at found
          have atEmit : SelfLatest (emit forests (fun j => u j + 1) (c + 2) 0
              (below ++ [⟨key, c + 2, some forests.length, some state.length⟩])) position := by
            simpa only [headed, headState, encode, found] using atHead
          rcases atEmit.emit_cases with inForests | ⟨atEnd, _⟩
          · have belowKnown : FrameRealized state below :=
              smaller_realized (queried_frame_realized known _) key
            have guardedKnown : FramesRealized guarded := framesRealized_emit
              (framesRealized_emit known _ _ _ [] (empty_frame_realized _))
              _ _ _ [] (empty_frame_realized _)
            have toGuard : state <+: guarded := (emit_extends ..).trans (emit_extends ..)
            rcases forestEntries_selfLatest_origins d hs source coordinates visible owners materials hs
                u c below guarded (frameRealized_extends toGuard belowKnown) guardedKnown position inForests with
                old | ⟨entry, member, same⟩
            · exact .inl (selfLatest_emit_inherited _ _ _ [] (empty_frame_realized _)
                (selfLatest_emit_inherited _ _ _ [] (empty_frame_realized _) old))
            · refine .inr ⟨entry, ?_, same⟩
              dsimp only [a, annotated] at found
              simp only [entries, found, List.mem_cons, List.mem_append]
              exact .inr (.inl member)
          · refine .inr ⟨⟨source, coordinates, hs, tail, visible, owners, materials, state⟩,
              List.mem_cons_self, ?_⟩
            change headed.length - 1 = position
            simpa only [headed, headState, encode, found, emit_length, Nat.add_sub_cancel] using atEnd.symm
      · refine .inr ⟨entry, ?_, same⟩
        simp only [entries, List.mem_cons, List.mem_append]
        exact .inr (.inr member)

  theorem forestEntries_selfLatest_origins (d : Nat) (hs : Forests (List Nat)) (source : ParentContext)
      (coordinates visible owners : List Nat) (materials : List (Forests (List Nat)))
      (ownerMaterial : Forests (List Nat)) (u : Nat → Nat) (c : Nat) (below : List Binding)
      (state : State d) (belowKnown : FrameRealized state below) (known : FramesRealized state)
      (position : Nat) (self : SelfLatest
        (encodeForests d (Parents.annotateForests d (source ++ [Parents.label d source coordinates]) hs)
          visible u c below state) position) :
      SelfLatest state position ∨
        ∃ entry ∈ forestEntries d hs source coordinates visible owners materials ownerMaterial u c below state,
          entry.closing = position := by
    cases hs with
    | nil => exact .inl self
    | cons h hs =>
      let a := Parents.label d source coordinates
      let withSlot := emit state (fun j => u j + 2) (c + 2) 0 below
      let withForest := encode d (Parents.annotate d (source ++ [a]) h) (visible ++ [state.length]) withSlot
      have slotKnown : FramesRealized withSlot := framesRealized_emit known _ _ _ below
        (frameRealized_extends (emit_extends ..) belowKnown)
      have forestKnown : FramesRealized withForest := encode_framesRealized d _ _ withSlot slotKnown
      have forestPrefix : state <+: withForest := (emit_extends ..).trans (encode_extends ..)
      rcases forestEntries_selfLatest_origins d hs source coordinates visible owners materials ownerMaterial
          u c below withForest (frameRealized_extends forestPrefix belowKnown) forestKnown position self with
          inForest | ⟨entry, member, same⟩
      · rcases entries_selfLatest_origins d h (source ++ [a]) (visible ++ [state.length])
            (owners ++ [source.length]) (materials ++ [ownerMaterial]) withSlot slotKnown position inForest with
            old | ⟨entry, member, same⟩
        · exact .inl (selfLatest_emit_inherited _ _ _ below belowKnown old)
        · refine .inr ⟨entry, ?_, same⟩
          simp only [forestEntries, List.mem_append]
          exact .inl member
      · refine .inr ⟨entry, ?_, same⟩
        simp only [forestEntries, List.mem_append]
        exact .inr member
end

theorem Entry.closing_selfLatest (entry : Entry d) : SelfLatest entry.result entry.closing :=
  (headState_selfLatest d _ _ entry.visible entry.state).extends entry.headed_prefix_result

/-- Exact characterization on the whole finite source language; no source
block inequality or target standardness is a premise. -/
theorem source_selfLatest_iff_closing_entry (d : Nat) (e : NumericalExpr) (position : Nat) :
    SelfLatest (encode d (Parents.annotate d [] e) [] []) position ↔
      ∃ entry ∈ entries d e [] [] [] [] [], entry.closing = position := by
  constructor
  · intro self
    rcases entries_selfLatest_origins d e [] [] [] [] []
        (by intro i col lookup; simp at lookup) position self with old | found
    · obtain ⟨col, lookup, _⟩ := old
      simp at lookup
    · exact found
  · rintro ⟨entry, member, rfl⟩
    exact entry.closing_selfLatest.extends (entries_execution d e [] [] [] [] [] entry member).resultPrefix

theorem standard_zero_key_parent_entry {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {child position height : Nat}
    (parent : Parents.parent (BMS.parentTable (d + 2) (fromSource d e)) d child = some position)
    (zero : Readout (encode d (Parents.annotate d [] e) [] []) position height 0) :
    ∃ entry ∈ entries d e [] [] [] [] [], entry.closing = position := by
  rcases standard_keyParentsAnchored positive standard child position parent with ⟨h, output⟩ | self
  · have contradiction := readout_tag_unique output zero
    cases contradiction
  · exact (source_selfLatest_iff_closing_entry d e position).mp self

/-- Every tag-zero starting point of a strict actual key-row path is a
restored source representative, not an unaccounted auxiliary position. -/
theorem standard_zero_strict_key_ancestor_entry {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {position endpoint height : Nat}
    (zero : Readout (encode d (Parents.annotate d [] e) [] []) position height 0)
    (different : position ≠ endpoint)
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (fromSource d e)) d position endpoint) :
    ∃ entry ∈ entries d e [] [] [] [] [], entry.closing = position := by
  obtain ⟨child, parent, _⟩ := path.first_child different
  exact standard_zero_key_parent_entry positive standard parent zero

end BTnSSBMS.Encoder
