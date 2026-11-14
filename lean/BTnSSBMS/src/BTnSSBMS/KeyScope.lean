import BTnSSBMS.KeyForestScope

/-!
The saved-frame ancestry invariant for the complete real recursive encoder.
The source premise only says that a column carrying attachments has a
highest numerical parent in its actual local context. This is a finite
condition, not standardness or an assumed target ancestry statement.
-/
namespace BTnSSBMS.Source

mutual
  def ParentedAttachments (d : Nat) (context : ParentContext) : NumericalExpr → Prop
    | .nil => True
    | .cons a hs t =>
      (hs ≠ .nil → ∃ p, (Parents.label d context a).parents[d - 1]?.join = some p) ∧
      ParentedForestList d (context ++ [Parents.label d context a]) hs ∧
      ParentedAttachments d (context ++ [Parents.label d context a]) t
  def ParentedForestList (d : Nat) (context : ParentContext) : Forests (List Nat) → Prop
    | .nil => True
    | .cons h hs => ParentedAttachments d context h ∧ ParentedForestList d context hs
end

end BTnSSBMS.Source

namespace BTnSSBMS.Encoder

theorem fresh_has_representative {d : Nat} {source : ParentContext} {visible : List Nat}
    (state : State d)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (coordinates : List Nat) (hs : Forests (List Nat))
    (parented : hs ≠ .nil → ∃ p, (Parents.label d source coordinates).parents[d - 1]?.join = some p)
    (fresh : equal (frameAt state (representative visible (Parents.label d source coordinates) (d - 1)))
      (Keys.ofColumn d visible.length (Parents.label d source coordinates)
        (Parents.annotateForests d (source ++ [Parents.label d source coordinates]) hs)) = none) :
    ∃ p, representative visible (Parents.label d source coordinates) (d - 1) = some p := by
  by_cases empty : hs = .nil
  · subst hs
    cases selected : representative visible (Parents.label d source coordinates) (d - 1) with
    | some p => exact ⟨p, rfl⟩
    | none =>
      simp [selected, frameAt, Parents.annotateForests, Keys.leaf_key, equal,
        virtualFrame, zeroBinding, Keys.compare, Forests.compare] at fresh
  · obtain ⟨p, selected⟩ := parented empty
    exact ⟨Parents.point visible p, by rw [representative_eq_point view, selected]; rfl⟩

theorem KeyGate.encodeForests {d : Nat} {source : ParentContext} {coordinates : List Nat}
    {visible : List Nat} {original state : State d} {u : Nat → Nat} {c : Nat} {below : List Binding}
    (scope : KeyGate d source coordinates visible original state u c below)
    (hs : Forests (List Nat)) (positive : 0 < d) (sourceCoherent : Parents.Coherent d source)
    (sourceValid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix original)) visible)
    (separated : Source.ForestsAbove (coordinates[0]?.getD 0) hs) :
    KeyGate d source coordinates visible original
      (Encoder.encodeForests d (Parents.annotateForests d (source ++ [Parents.label d source coordinates]) hs)
        visible u c below state) u c below :=
  ⟨encodeForests_numerical_gate d hs source coordinates visible original state u (original.length + 1)
      c below positive sourceCoherent sourceValid view scope.numerical separated,
    scope.headed.trans (encodeForests_extends ..), scope.retained.extends (encodeForests_extends ..)⟩

mutual
  theorem encode_framesAncestral (d : Nat) (e : NumericalExpr)
      (source : ParentContext) (visible : List Nat) (state : State d)
      (positive : 0 < d) (sourceCoherent : Parents.Coherent d source)
      (sourceValid : Parents.ContextValid source)
      (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
      (separated : Source.ForestSeparated e) (parented : Source.ParentedAttachments d source e)
      (ordered : FramesOrdered state) (realized : FramesRealized state) (paths : FramesAncestral state)
      (safe : NoFallback d (Parents.annotate d source e) visible state) :
      FramesAncestral (encode d (Parents.annotate d source e) visible state) := by
    cases e with
    | nil => exact paths
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
      simp only [Parents.annotate, NoFallback, encode] at safe ⊢
      split at safe
      next bound found =>
        rw [found]
        have result := reused_head_result state sourceCoherent sourceValid view ordered realized paths
          coordinates key bound positive found
        apply encode_framesAncestral d tail _ _ _ positive nextCoherent nextValid
          (emit_numerical_view state sourceCoherent sourceValid view coordinates bound.height 0 _)
          separated.2 parented.2.2
        · exact framesOrdered_emit ordered _ _ _ _ (reused_frame_ordered frameOrder key bound found _)
        · exact framesRealized_emit realized _ _ _ _ (reused_frame_realized frameKnown key bound found _)
        · exact framesAncestral_emit paths _ _ _ _ result.2
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
        have belowOrder : FrameOrdered below := smaller_ordered frameOrder key
        have belowKnown : FrameRealized withH below :=
          frameRealized_extends ((emit_extends ..).trans (emit_extends ..)) (smaller_realized frameKnown key)
        have forestPaths := encodeForests_framesAncestral d hs source coordinates visible state withH u c below
          positive sourceCoherent sourceValid view separated.1 parented.2.1 gate
          belowOrder belowKnown orderH realizedH pathsH forestSafe
        have forestOrder := encodeForests_framesOrdered d annotated visible u c below withH belowOrder orderH
        have forestKnown := encodeForests_framesRealized d annotated visible u c below withH belowKnown realizedH
        have afterGate := gate.encodeForests hs positive sourceCoherent sourceValid view separated.1
        have forestBelow := frameRealized_extends (encodeForests_extends d annotated visible u c below withH) belowKnown
        have finalView := closing_numerical_view state withForests sourceValid view coordinates c
          (below ++ [⟨key, c + 2, some withForests.length, some state.length⟩]) afterGate.numerical
          afterGate.headed positive sourceCoherent
        apply encode_framesAncestral d tail _ _ _ positive nextCoherent nextValid finalView separated.2 parented.2.2
        · exact framesOrdered_emit forestOrder _ _ _ _ (fresh_frame_ordered frameOrder key _ _)
        · exact framesRealized_emit forestKnown _ _ _ _
            (fresh_frame_realized below forestBelow key c state.length afterGate.definition_readout _)
        · exact framesAncestral_emit forestPaths _ _ _ _ (afterGate.closing_ancestral positive key)
        · exact tailSafe

  theorem encodeForests_framesAncestral (d : Nat) (hs : Forests (List Nat))
      (source : ParentContext) (coordinates : List Nat) (visible : List Nat)
      (original state : State d) (u : Nat → Nat) (c : Nat) (below : List Binding)
      (positive : 0 < d) (sourceCoherent : Parents.Coherent d source)
      (sourceValid : Parents.ContextValid source)
      (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix original)) visible)
      (separated : Source.ForestsAbove (coordinates[0]?.getD 0) hs)
      (parented : Source.ParentedForestList d (source ++ [Parents.label d source coordinates]) hs)
      (scope : KeyGate d source coordinates visible original state u c below)
      (belowOrder : FrameOrdered below) (belowKnown : FrameRealized state below)
      (ordered : FramesOrdered state) (realized : FramesRealized state) (paths : FramesAncestral state)
      (safe : NoFallbackForests d
        (Parents.annotateForests d (source ++ [Parents.label d source coordinates]) hs) visible u c below state) :
      FramesAncestral (encodeForests d
        (Parents.annotateForests d (source ++ [Parents.label d source coordinates]) hs) visible u c below state) := by
    cases hs with
    | nil => exact paths
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
      exact encodeForests_framesAncestral d hs source coordinates visible original
        (encode d (Parents.annotate d (source ++ [a]) h) (visible ++ [state.length]) withSlot)
        u c below positive sourceCoherent sourceValid view separated.2.2 parented.2 nextScope
        belowOrder (frameRealized_extends ((emit_extends ..).trans (encode_extends d _ _ _)) belowKnown)
        forestOrder forestKnown forestPaths restSafe
end

/-- Every binding saved by the complete encoding is on the actual
key-row ancestor chain of the column carrying that saved frame. -/
theorem source_framesAncestral (d : Nat) (e : NumericalExpr) (positive : 0 < d)
    (separated : Source.ForestSeparated e) (parented : Source.ParentedAttachments d [] e) :
    FramesAncestral (encode d (Parents.annotate d [] e) [] []) :=
  encode_framesAncestral d e [] [] [] positive (Parents.empty_coherent d) Parents.empty_context_valid
    (Parents.empty_numerical_view d) separated parented (by intro col member; simp at member)
    (by intro i col lookup; simp at lookup) (by intro i col lookup; simp at lookup) (source_noFallback d e)

end BTnSSBMS.Encoder
