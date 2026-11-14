import BTnSSBMS.BindingAnchors
import BTnSSBMS.SourceLegality

/-!
Every actual key-row parent in the complete encoder is either a definition
column or a column that registered itself as a binding representative.
This statement uses the computed BMS parent table, not an idealized table.
The recursive proof covers every forest and every exit to the outer scope.
-/
namespace BTnSSBMS.Encoder

def KeyAnchor (state : State d) (position : Nat) : Prop :=
  (∃ h, Readout state position h 1) ∨ SelfLatest state position

def KeyParentsAnchored (state : State d) : Prop :=
  ∀ position root,
    Parents.parent (BMS.parentTable (d + 2) (matrix state)) d position = some root →
    KeyAnchor state root

theorem readout_tag_unique {state : State d} {position h k tag other : Nat}
    (left : Readout state position h tag) (right : Readout state position k other) : tag = other := by
  obtain ⟨a, aLookup, _, aTag⟩ := left
  obtain ⟨b, bLookup, _, bTag⟩ := right
  have same : a = b := Option.some.inj (aLookup.symm.trans bLookup)
  subst b
  exact Option.some.inj (aTag.symm.trans bTag)

theorem SelfLatest.readout {state : State d} (known : FramesRealized state) {position : Nat}
    (self : SelfLatest state position) : ∃ height, Readout state position height 0 := by
  obtain ⟨col, lookup, b, member, latest⟩ := self
  have output := (known position col lookup b member).1
  rw [latest] at output
  exact ⟨b.height, readout_extends (List.take_prefix ..) output⟩

theorem KeyAnchor.zero_or_one {state : State d} (known : FramesRealized state) {position : Nat}
    (anchor : KeyAnchor state position) : ∃ height tag, tag ≤ 1 ∧ Readout state position height tag := by
  rcases anchor with ⟨height, output⟩ | self
  · exact ⟨height, 1, by decide, output⟩
  · obtain ⟨height, output⟩ := self.readout known
    exact ⟨height, 0, by decide, output⟩

theorem KeyAnchor.extends {state next : State d} {position : Nat}
    (anchor : KeyAnchor state position) (extended : state <+: next) : KeyAnchor next position := by
  rcases anchor with ⟨h, output⟩ | self
  · exact .inl ⟨h, readout_extends extended output⟩
  · exact .inr (self.extends extended)

theorem keyParentsAnchored_emit {state : State d} (anchored : KeyParentsAnchored state)
    (u : Nat → Nat) (height tag : Nat) (frame : List Binding)
    (added : ∀ root,
      Parents.parent (BMS.parentTable (d + 2) (matrix (emit state u height tag frame)))
        d state.length = some root → KeyAnchor (emit state u height tag frame) root) :
    KeyParentsAnchored (emit state u height tag frame) := by
  intro position root edge
  by_cases old : position < state.length
  · have oldEdge := (Parents.parent_prefix_eq (table_emit_prefix state u height tag frame)
      d position (by rwa [table_length])).trans edge
    exact (anchored position root oldEdge).extends (emit_extends ..)
  · obtain ⟨col, lookup, _⟩ := Option.bind_eq_some_iff.mp edge
    have inside := (List.getElem?_eq_some_iff.mp lookup).choose
    rw [table_length, emit_length] at inside
    have atEnd : position = state.length := by omega
    subst position
    exact added root edge

theorem keyAnchor_of_definition {state : State d} {b : Binding}
    (known : BindingRealized state b) {position : Nat} (found : b.definition = some position) :
    KeyAnchor state position := by
  have definition := known.2.1
  rw [found] at definition
  obtain ⟨h, _, output⟩ := definition
  exact .inl ⟨h, output⟩

theorem keyParentsAnchored_no_strict_descendant {state : State d}
    (anchored : KeyParentsAnchored state) {position : Nat} (notAnchor : ¬ KeyAnchor state position)
    {endpoint : Nat}
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (matrix state)) d position endpoint) :
    position = endpoint := by
  by_cases same : position = endpoint
  · exact same
  · obtain ⟨child, first, _⟩ := path.first_child same
    exact False.elim (notAnchor (anchored child position first))

theorem keyParentsAnchored_guard_no_strict_descendant {state : State d}
    (known : FramesRealized state) (anchored : KeyParentsAnchored state) {position height endpoint : Nat}
    (guard : Readout state position height 2)
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (matrix state)) d position endpoint) :
    position = endpoint := by
  apply keyParentsAnchored_no_strict_descendant anchored ?_ path
  intro anchor
  obtain ⟨h, tag, bound, output⟩ := anchor.zero_or_one known
  have same := readout_tag_unique output guard
  omega

mutual
  theorem encode_keyParentsAnchored (d : Nat) (e : NumericalExpr)
      (source : ParentContext) (visible : List Nat) (state : State d)
      (positive : 0 < d) (sourceCoherent : Parents.Coherent d source)
      (sourceValid : Parents.ContextValid source)
      (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
      (separated : Source.ForestSeparated e) (parented : Source.ParentedAttachments d source e)
      (ordered : FramesOrdered state) (realized : FramesRealized state) (paths : FramesAncestral state)
      (self : FramesSelfLatest state) (anchored : KeyParentsAnchored state)
      (safe : NoFallback d (Parents.annotate d source e) visible state) :
      KeyParentsAnchored (encode d (Parents.annotate d source e) visible state) := by
    cases e with
    | nil => exact anchored
    | cons coordinates hs tail =>
      have nextCoherent := Parents.coherent_append_label sourceCoherent coordinates
      have nextValid := Parents.context_valid_append_label d source sourceValid coordinates
      let a := Parents.label d source coordinates
      let annotated := Parents.annotateForests d (source ++ [a]) hs
      let key := Keys.ofColumn d visible.length a annotated
      let frame := frameAt state (representative visible a (d - 1))
      let below := smaller frame key
      let u := vector state visible a
      have frameOrder : FrameOrdered frame := queried_frame_ordered ordered _
      have frameKnown : FrameRealized state frame := queried_frame_realized realized _
      have frameSelf : FrameSelfLatest state frame := queried_frame_selfLatest self _
      have belowSelf : FrameSelfLatest state below := smaller_selfLatest frameSelf key
      simp only [Parents.annotate, NoFallback, encode] at safe ⊢
      split at safe
      next bound found =>
        rw [found]
        have result := reused_head_result state sourceCoherent sourceValid view ordered realized paths
          coordinates key bound positive found
        apply encode_keyParentsAnchored d tail _ _ _ positive nextCoherent nextValid
          (emit_numerical_view state sourceCoherent sourceValid view coordinates bound.height 0 _)
          separated.2 parented.2.2
        · exact framesOrdered_emit ordered _ _ _ _ (reused_frame_ordered frameOrder key bound found _)
        · exact framesRealized_emit realized _ _ _ _ (reused_frame_realized frameKnown key bound found _)
        · exact framesAncestral_emit paths _ _ _ _ result.2
        · exact framesSelfLatest_emit self _ _ _ _
            (updated_frame_selfLatest belowSelf {bound with latest := some state.length} rfl _ _ _)
        · apply keyParentsAnchored_emit anchored
          intro root edge
          have definition := result.1.symm.trans edge
          exact (keyAnchor_of_definition (frameKnown bound (List.mem_of_find?_eq_some found))
            definition).extends (emit_extends ..)
        · exact safe
      next fresh =>
        rw [fresh]
        obtain ⟨nonempty, forestSafe, tailSafe⟩ := safe
        obtain ⟨position, selected⟩ := fresh_has_representative state view coordinates hs parented.1 fresh
        obtain ⟨root, latest, output, keyParent, belowPaths⟩ := fresh_head_result state sourceCoherent sourceValid
          view ordered realized paths coordinates key positive position selected
          (by simpa only [← selected] using nonempty)
        let c := (base below).height
        let withD := emit state u (c + 1) 1 []
        let withH := emit withD (fun j => u j + 1) (c + 2) 2 []
        let withForests := encodeForests d annotated visible u c below withH
        have belowPathsD : FrameAncestral withD state.length below := by
          simpa only [← selected] using belowPaths
        have rootSelf : SelfLatest state root := belowSelf (base below)
          (base_member nonempty) root (by simpa only [← selected] using latest)
        have anchoredD : KeyParentsAnchored withD := by
          apply keyParentsAnchored_emit anchored
          intro q edge
          have actual : Parents.parent (BMS.parentTable (d + 2) (matrix withD)) d state.length = some root := by
            simpa only [← selected] using keyParent
          have same : q = root := Option.some.inj (edge.symm.trans actual)
          subst q
          exact .inr (rootSelf.extends (emit_extends ..))
        have anchoredH : KeyParentsAnchored withH := by
          apply keyParentsAnchored_emit anchoredD
          intro q edge
          have actual : Parents.parent (BMS.parentTable (d + 2) (matrix withH)) d withD.length = some state.length := by
            simpa only [withH, withD, emit_length] using guard_key_parent state u c positive
          have same : q = state.length := Option.some.inj (edge.symm.trans actual)
          subst q
          exact .inl ⟨c + 1, readout_extends (emit_extends ..) (readout_emit ..)⟩
        have gate : KeyGate d source coordinates visible state withH u c below :=
          ⟨initial_numerical_gate state sourceCoherent sourceValid view coordinates c,
            List.prefix_refl _, belowPathsD.extends (emit_extends ..)⟩
        have orderH : FramesOrdered withH := framesOrdered_emit
          (framesOrdered_emit ordered u (c + 1) 1 [] (by simp [FrameOrdered]))
          (fun j => u j + 1) (c + 2) 2 [] (by simp [FrameOrdered])
        have realizedH : FramesRealized withH := framesRealized_emit
          (framesRealized_emit realized u (c + 1) 1 [] (empty_frame_realized _))
          (fun j => u j + 1) (c + 2) 2 [] (empty_frame_realized _)
        have pathsH : FramesAncestral withH := framesAncestral_emit
          (framesAncestral_emit paths u (c + 1) 1 [] (empty_frame_ancestral _ _))
          (fun j => u j + 1) (c + 2) 2 [] (empty_frame_ancestral _ _)
        have selfH : FramesSelfLatest withH := framesSelfLatest_emit
          (framesSelfLatest_emit self u (c + 1) 1 [] (empty_frame_selfLatest _))
          (fun j => u j + 1) (c + 2) 2 [] (empty_frame_selfLatest _)
        have belowOrder : FrameOrdered below := smaller_ordered frameOrder key
        have belowKnown : FrameRealized withH below :=
          frameRealized_extends ((emit_extends ..).trans (emit_extends ..)) (smaller_realized frameKnown key)
        have belowSelfH : FrameSelfLatest withH below :=
          belowSelf.extends ((emit_extends ..).trans (emit_extends ..))
        have forestAnchors := encodeForests_keyParentsAnchored d hs source coordinates visible state withH u c below
          positive sourceCoherent sourceValid view separated.1 parented.2.1 gate
          belowOrder belowKnown belowSelfH orderH realizedH pathsH selfH anchoredH forestSafe
        have forestPaths := encodeForests_framesAncestral d hs source coordinates visible state withH u c below
          positive sourceCoherent sourceValid view separated.1 parented.2.1 gate
          belowOrder belowKnown orderH realizedH pathsH forestSafe
        have forestOrder := encodeForests_framesOrdered d annotated visible u c below withH belowOrder orderH
        have forestKnown := encodeForests_framesRealized d annotated visible u c below withH belowKnown realizedH
        have forestSelf := encodeForests_framesSelfLatest d annotated visible u c below withH belowSelfH selfH
        have afterGate := gate.encodeForests hs positive sourceCoherent sourceValid view separated.1
        have forestBelow := frameRealized_extends (encodeForests_extends d annotated visible u c below withH) belowKnown
        have finalView := closing_numerical_view state withForests sourceValid view coordinates c
          (below ++ [⟨key, c + 2, some withForests.length, some state.length⟩]) afterGate.numerical
          afterGate.headed positive sourceCoherent
        apply encode_keyParentsAnchored d tail _ _ _ positive nextCoherent nextValid finalView separated.2 parented.2.2
        · exact framesOrdered_emit forestOrder _ _ _ _ (fresh_frame_ordered frameOrder key _ _)
        · exact framesRealized_emit forestKnown _ _ _ _
            (fresh_frame_realized below forestBelow key c state.length afterGate.definition_readout _)
        · exact framesAncestral_emit forestPaths _ _ _ _ (afterGate.closing_ancestral positive key)
        · exact framesSelfLatest_emit forestSelf _ _ _ _
            (updated_frame_selfLatest (belowSelfH.extends (encodeForests_extends ..))
              ⟨key, c + 2, some withForests.length, some state.length⟩ rfl _ _ _)
        · apply keyParentsAnchored_emit forestAnchors
          intro q edge
          have actual := afterGate.closing_key_parent positive
            (below ++ [⟨key, c + 2, some withForests.length, some state.length⟩])
          have same : q = state.length := Option.some.inj (edge.symm.trans actual)
          subst q
          exact .inl ⟨c + 1, readout_extends (emit_extends ..) afterGate.definition_readout⟩
        · exact tailSafe

  theorem encodeForests_keyParentsAnchored (d : Nat) (hs : Forests (List Nat))
      (source : ParentContext) (coordinates : List Nat) (visible : List Nat)
      (original state : State d) (u : Nat → Nat) (c : Nat) (below : List Binding)
      (positive : 0 < d) (sourceCoherent : Parents.Coherent d source)
      (sourceValid : Parents.ContextValid source)
      (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix original)) visible)
      (separated : Source.ForestsAbove (coordinates[0]?.getD 0) hs)
      (parented : Source.ParentedForestList d (source ++ [Parents.label d source coordinates]) hs)
      (scope : KeyGate d source coordinates visible original state u c below)
      (belowOrder : FrameOrdered below) (belowKnown : FrameRealized state below)
      (belowSelf : FrameSelfLatest state below)
      (ordered : FramesOrdered state) (realized : FramesRealized state) (paths : FramesAncestral state)
      (self : FramesSelfLatest state) (anchored : KeyParentsAnchored state)
      (safe : NoFallbackForests d
        (Parents.annotateForests d (source ++ [Parents.label d source coordinates]) hs) visible u c below state) :
      KeyParentsAnchored (encodeForests d
        (Parents.annotateForests d (source ++ [Parents.label d source coordinates]) hs) visible u c below state) := by
    cases hs with
    | nil => exact anchored
    | cons h hs =>
      obtain ⟨childSafe, restSafe⟩ := safe
      let a := Parents.label d source coordinates
      let withSlot := emit state (fun j => u j + 2) (c + 2) 0 below
      have nextCoherent := Parents.coherent_append_label sourceCoherent coordinates
      have nextValid := Parents.context_valid_append_label d source sourceValid coordinates
      have slotView := scope.numerical.slot_view sourceValid view (c + 2) below
      have slotOrder := framesOrdered_emit ordered (fun j => u j + 2) (c + 2) 0 below belowOrder
      have slotKnown := framesRealized_emit realized (fun j => u j + 2) (c + 2) 0 below
        (frameRealized_extends (emit_extends ..) belowKnown)
      have slotPaths := framesAncestral_emit paths (fun j => u j + 2) (c + 2) 0 below (scope.slot_ancestral positive)
      have slotSelf := framesSelfLatest_emit self (fun j => u j + 2) (c + 2) 0 below
        (belowSelf.extends (emit_extends ..))
      have slotAnchors : KeyParentsAnchored withSlot := by
        apply keyParentsAnchored_emit anchored
        intro q edge
        have same : q = original.length := Option.some.inj (edge.symm.trans (scope.slot_key_parent positive))
        subst q
        exact .inl ⟨c + 1, readout_extends (emit_extends ..) scope.definition_readout⟩
      have forestAnchors := encode_keyParentsAnchored d h (source ++ [a]) (visible ++ [state.length]) withSlot
        positive nextCoherent nextValid slotView separated.2.1 parented.1 slotOrder slotKnown slotPaths
        slotSelf slotAnchors childSafe
      have forestPaths := encode_framesAncestral d h (source ++ [a]) (visible ++ [state.length]) withSlot
        positive nextCoherent nextValid slotView separated.2.1 parented.1 slotOrder slotKnown slotPaths childSafe
      obtain ⟨finalVisible, extended, forestView⟩ := encode_numerical_view d h (source ++ [a])
        (visible ++ [state.length]) withSlot positive nextCoherent nextValid slotView separated.2.1
      have nextScope := scope.after_forest positive sourceCoherent sourceValid view.length
        (Source.labels h) (encode_extends d _ _ _) extended separated.1 forestView
      have forestOrder := encode_framesOrdered d (Parents.annotate d (source ++ [a]) h)
        (visible ++ [state.length]) withSlot slotOrder
      have forestKnown := encode_framesRealized d (Parents.annotate d (source ++ [a]) h)
        (visible ++ [state.length]) withSlot slotKnown
      have forestSelf := encode_framesSelfLatest d (Parents.annotate d (source ++ [a]) h)
        (visible ++ [state.length]) withSlot slotSelf
      exact encodeForests_keyParentsAnchored d hs source coordinates visible original
        (encode d (Parents.annotate d (source ++ [a]) h) (visible ++ [state.length]) withSlot)
        u c below positive sourceCoherent sourceValid view separated.2.2 parented.2 nextScope
        belowOrder (frameRealized_extends ((emit_extends ..).trans (encode_extends d _ _ _)) belowKnown)
        (belowSelf.extends ((emit_extends ..).trans (encode_extends d _ _ _)))
        forestOrder forestKnown forestPaths forestSelf forestAnchors restSafe
end

theorem source_keyParentsAnchored (d : Nat) (e : NumericalExpr) (positive : 0 < d)
    (legal : Source.FiniteLegal d [] e) :
    KeyParentsAnchored (encode d (Parents.annotate d [] e) [] []) :=
  encode_keyParentsAnchored d e [] [] [] positive (Parents.empty_coherent d) Parents.empty_context_valid
    (Parents.empty_numerical_view d) legal.separated (legal.parented positive)
    (by intro col member; simp at member) (by intro i col lookup; simp at lookup)
    (by intro i col lookup; simp at lookup) (by intro col member; simp at member)
    (by intro i root edge; simp [Parents.parent, BMS.parentTable, BMS.parentTableAux, matrix] at edge)
    (source_noFallback d e)

end BTnSSBMS.Encoder
