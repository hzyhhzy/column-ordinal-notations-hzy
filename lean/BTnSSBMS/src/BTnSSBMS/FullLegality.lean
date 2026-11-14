import BTnSSBMS.KeyScope

/-!
Complete numerical legality, including the key and tag rows. The final
result is for every finite input meeting two explicit finite conditions;
their preservation by source fundamental sequences remains unproved here.
-/
namespace BTnSSBMS.Parents

theorem UnitSteps.mono {d rows : Nat} {context : ParentContext}
    (unit : UnitSteps rows context) (bound : d ≤ rows) : UnitSteps d context := by
  intro position inside j room
  exact unit position inside j (by omega)

end BTnSSBMS.Parents

namespace BTnSSBMS.Encoder

theorem emit_full_unitSteps (state : State d) (u : Nat → Nat) (height tag : Nat) (frame : List Binding)
    (unit : Parents.UnitSteps (d + 2) (BMS.parentTable (d + 2) (matrix state)))
    (numerical : Parents.UnitSteps d (BMS.parentTable (d + 2) (matrix (emit state u height tag frame))))
    (upper : ∀ j, d ≤ j → j < d + 2 →
      Parents.reading (BMS.parentTable (d + 2) (matrix (emit state u height tag frame))) j state.length =
        ((Parents.parent (BMS.parentTable (d + 2) (matrix (emit state u height tag frame))) j state.length).map
          fun p => Parents.reading (BMS.parentTable (d + 2) (matrix (emit state u height tag frame))) j p + 1).getD 0) :
    Parents.UnitSteps (d + 2) (BMS.parentTable (d + 2) (matrix (emit state u height tag frame))) := by
  apply unit.extend_one (BMS.parentTable_valid _ _) (table_emit_prefix ..)
    (by rw [table_length, table_length, emit_length])
  intro j room
  rw [table_length]
  by_cases low : j < d
  · exact numerical state.length (by rw [table_length, emit_length]; omega) j low
  · exact upper j (by omega) room

theorem emit_full_zero (state : State d) (u : Nat → Nat) (frame : List Binding)
    (unit : Parents.UnitSteps (d + 2) (BMS.parentTable (d + 2) (matrix state)))
    (numerical : Parents.UnitSteps d (BMS.parentTable (d + 2) (matrix (emit state u 0 0 frame)))) :
    Parents.UnitSteps (d + 2) (BMS.parentTable (d + 2) (matrix (emit state u 0 0 frame))) := by
  apply emit_full_unitSteps state u 0 0 frame unit numerical
  intro j high room
  have cases : j = d ∨ j = d + 1 := by omega
  rcases cases with rfl | rfl
  · rw [(readout_emit state u 0 0 frame).key_reading, emitted_key_zero]
    rfl
  · rw [(readout_emit state u 0 0 frame).tag_reading, emitted_tag_zero]
    rfl

theorem emit_full_with_parent (state : State d) (u : Nat → Nat) (height tag : Nat) (frame : List Binding)
    (unit : Parents.UnitSteps (d + 2) (BMS.parentTable (d + 2) (matrix state)))
    (numerical : Parents.UnitSteps d (BMS.parentTable (d + 2) (matrix (emit state u height tag frame))))
    (root h t : Nat) (output : Readout state root h t) (heightEq : height = h + 1)
    (keyParent : Parents.parent (BMS.parentTable (d + 2) (matrix (emit state u height tag frame))) d state.length = some root)
    (tagCase : tag = 0 ∨ tag = t + 1) :
    Parents.UnitSteps (d + 2) (BMS.parentTable (d + 2) (matrix (emit state u height tag frame))) := by
  have outputNext := readout_extends (emit_extends state u height tag frame) output
  apply emit_full_unitSteps state u height tag frame unit numerical
  intro j high room
  have cases : j = d ∨ j = d + 1 := by omega
  rcases cases with rfl | rfl
  · rw [(readout_emit state u height tag frame).key_reading, keyParent]
    simp only [Option.map_some, Option.getD_some, outputNext.key_reading]
    exact heightEq
  · rcases tagCase with zero | successor
    · subst tag
      rw [(readout_emit state u height 0 frame).tag_reading, emitted_tag_zero]
      rfl
    · have tagParent := emitted_tag_parent state u height tag frame root keyParent
        (by rw [output.tag_reading]; exact successor)
      rw [(readout_emit state u height tag frame).tag_reading, tagParent]
      simp only [Option.map_some, Option.getD_some, outputNext.tag_reading]
      exact successor

theorem reused_full_unitSteps {d : Nat} {source : ParentContext} {visible : List Nat}
    (state : State d) (sourceCoherent : Parents.Coherent d source)
    (sourceValid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (ordered : FramesOrdered state) (realized : FramesRealized state) (paths : FramesAncestral state)
    (unit : Parents.UnitSteps (d + 2) (BMS.parentTable (d + 2) (matrix state)))
    (coordinates : List Nat) (key : Key) (bound : Binding) (positive : 0 < d)
    (found : equal (frameAt state (representative visible (Parents.label d source coordinates) (d - 1))) key = some bound) :
    let frame := frameAt state (representative visible (Parents.label d source coordinates) (d - 1))
    let updated := smaller frame key ++ [{bound with latest := some state.length}]
    Parents.UnitSteps (d + 2) (BMS.parentTable (d + 2) (matrix
      (emit state (vector state visible (Parents.label d source coordinates)) bound.height 0 updated))) := by
  dsimp only
  let u := vector state visible (Parents.label d source coordinates)
  let frame := frameAt state (representative visible (Parents.label d source coordinates) (d - 1))
  let updated := smaller frame key ++ [{bound with latest := some state.length}]
  have lower := emit_represented_unitSteps state sourceCoherent sourceValid view (unit.mono (by omega))
    coordinates bound.height 0 updated
  have result := reused_head_result state sourceCoherent sourceValid view ordered realized paths
    coordinates key bound positive found
  have keyParent : Parents.parent (BMS.parentTable (d + 2) (matrix
      (emit state u bound.height 0 updated))) d state.length = bound.definition := result.1
  change Parents.UnitSteps (d + 2) (BMS.parentTable (d + 2) (matrix (emit state u bound.height 0 updated)))
  have known := (queried_frame_realized realized _ bound (List.mem_of_find?_eq_some found)).2.1
  cases definition : bound.definition with
  | none =>
    have zero : bound.height = 0 := by simpa only [definition] using known
    rw [zero] at lower ⊢
    exact emit_full_zero state u updated unit lower
  | some root =>
    rw [definition] at known
    obtain ⟨h, heightEq, output⟩ := known
    exact emit_full_with_parent state u bound.height 0 updated unit lower root h 1 output heightEq
      (by simpa only [definition] using keyParent) (Or.inl rfl)

theorem guard_full_unitSteps (state : State d) (u : Nat → Nat) (c : Nat) (positive : 0 < d)
    (unit : Parents.UnitSteps (d + 2) (BMS.parentTable (d + 2) (matrix (emit state u (c + 1) 1 [])))) :
    Parents.UnitSteps (d + 2) (BMS.parentTable (d + 2) (matrix
      (emit (emit state u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 []))) :=
  emit_full_with_parent (emit state u (c + 1) 1 []) _ (c + 2) 2 [] unit
    (guard_unitSteps state u c (unit.mono (by omega))) state.length (c + 1) 1
    (readout_emit ..) rfl (by simpa only [emit_length] using guard_key_parent state u c positive) (Or.inr rfl)

theorem KeyGate.slot_full_unitSteps {d : Nat} {source : ParentContext} {coordinates : List Nat}
    {visible : List Nat} {original state : State d} {u : Nat → Nat} {c : Nat} {below : List Binding}
    (scope : KeyGate d source coordinates visible original state u c below) (positive : 0 < d)
    (unit : Parents.UnitSteps (d + 2) (BMS.parentTable (d + 2) (matrix state))) :
    Parents.UnitSteps (d + 2) (BMS.parentTable (d + 2) (matrix
      (emit state (fun j => u j + 2) (c + 2) 0 below))) :=
  emit_full_with_parent state _ (c + 2) 0 below unit
    (scope.numerical.slot_unitSteps (c + 2) below (unit.mono (by omega))) original.length (c + 1) 1
    scope.definition_readout rfl (scope.slot_key_parent positive) (Or.inl rfl)

theorem KeyGate.closing_full_unitSteps {d : Nat} {source : ParentContext} {coordinates : List Nat}
    {visible : List Nat} {original state : State d} {u : Nat → Nat} {c : Nat} {below : List Binding}
    (scope : KeyGate d source coordinates visible original state u c below) (positive : 0 < d)
    (frame : List Binding)
    (unit : Parents.UnitSteps (d + 2) (BMS.parentTable (d + 2) (matrix state))) :
    Parents.UnitSteps (d + 2) (BMS.parentTable (d + 2) (matrix
      (emit state (fun j => u j + 1) (c + 2) 0 frame))) := by
  have lower : Parents.UnitSteps d (BMS.parentTable (d + 2) (matrix
      (emit state (fun j => u j + 1) (c + 2) 0 frame))) := by
    apply emit_unitSteps state _ (c + 2) 0 frame (unit.mono (by omega))
    intro j room
    rw [scope.closing_numerical_parent positive frame j room]
    simp only [Option.map_some, Option.getD_some]
    have dExtends := (emit_extends ..).trans
      (scope.headed.trans (emit_extends state (fun j => u j + 1) (c + 2) 0 frame))
    rw [← Parents.reading_prefix (table_prefix dExtends) j original.length
      (by rw [table_length, emit_length]; omega), emitted_numerical_value original u (c + 1) 1 [] j room]
  exact emit_full_with_parent state _ (c + 2) 0 frame unit lower original.length (c + 1) 1
    scope.definition_readout rfl (scope.closing_key_parent positive frame) (Or.inl rfl)

mutual
  theorem encode_full_unitSteps (d : Nat) (e : NumericalExpr)
      (source : ParentContext) (visible : List Nat) (state : State d)
      (positive : 0 < d) (sourceCoherent : Parents.Coherent d source)
      (sourceValid : Parents.ContextValid source)
      (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
      (separated : Source.ForestSeparated e) (parented : Source.ParentedAttachments d source e)
      (ordered : FramesOrdered state) (realized : FramesRealized state) (paths : FramesAncestral state)
      (unit : Parents.UnitSteps (d + 2) (BMS.parentTable (d + 2) (matrix state)))
      (safe : NoFallback d (Parents.annotate d source e) visible state) :
      Parents.UnitSteps (d + 2)
        (BMS.parentTable (d + 2) (matrix (encode d (Parents.annotate d source e) visible state))) := by
    cases e with
    | nil => exact unit
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
        apply encode_full_unitSteps d tail _ _ _ positive nextCoherent nextValid
          (emit_numerical_view state sourceCoherent sourceValid view coordinates bound.height 0 _)
          separated.2 parented.2.2
        · exact framesOrdered_emit ordered _ _ _ _ (reused_frame_ordered frameOrder key bound found _)
        · exact framesRealized_emit realized _ _ _ _ (reused_frame_realized frameKnown key bound found _)
        · exact framesAncestral_emit paths _ _ _ _ result.2
        · exact reused_full_unitSteps state sourceCoherent sourceValid view ordered realized paths unit
            coordinates key bound positive found
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
        have belowPathsD : FrameAncestral withD state.length below := by simpa only [← selected] using belowPaths
        have outputD : Readout state root c 0 := by simpa only [← selected] using output
        have keyParentD : Parents.parent (BMS.parentTable (d + 2) (matrix withD)) d state.length = some root := by
          simpa only [← selected] using keyParent
        have unitD := emit_full_with_parent state u (c + 1) 1 [] unit
          (emit_represented_unitSteps state sourceCoherent sourceValid view (unit.mono (by omega)) coordinates (c + 1) 1 [])
          root c 0 outputD rfl keyParentD (Or.inr rfl)
        have unitH := guard_full_unitSteps state u c positive unitD
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
        have forestUnit := encodeForests_full_unitSteps d hs source coordinates visible state withH u c below
          positive sourceCoherent sourceValid view separated.1 parented.2.1 gate belowOrder belowKnown
          orderH realizedH pathsH unitH forestSafe
        have forestPaths := encodeForests_framesAncestral d hs source coordinates visible state withH u c below
          positive sourceCoherent sourceValid view separated.1 parented.2.1 gate belowOrder belowKnown
          orderH realizedH pathsH forestSafe
        have forestOrder := encodeForests_framesOrdered d annotated visible u c below withH belowOrder orderH
        have forestKnown := encodeForests_framesRealized d annotated visible u c below withH belowKnown realizedH
        have afterGate := gate.encodeForests hs positive sourceCoherent sourceValid view separated.1
        have forestBelow := frameRealized_extends (encodeForests_extends d annotated visible u c below withH) belowKnown
        have finalView := closing_numerical_view state withForests sourceValid view coordinates c
          (below ++ [⟨key, c + 2, some withForests.length, some state.length⟩]) afterGate.numerical
          afterGate.headed positive sourceCoherent
        apply encode_full_unitSteps d tail _ _ _ positive nextCoherent nextValid finalView separated.2 parented.2.2
        · exact framesOrdered_emit forestOrder _ _ _ _ (fresh_frame_ordered frameOrder key _ _)
        · exact framesRealized_emit forestKnown _ _ _ _
            (fresh_frame_realized below forestBelow key c state.length afterGate.definition_readout _)
        · exact framesAncestral_emit forestPaths _ _ _ _ (afterGate.closing_ancestral positive key)
        · exact afterGate.closing_full_unitSteps positive _ forestUnit
        · exact tailSafe

  theorem encodeForests_full_unitSteps (d : Nat) (hs : Forests (List Nat))
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
      (unit : Parents.UnitSteps (d + 2) (BMS.parentTable (d + 2) (matrix state)))
      (safe : NoFallbackForests d
        (Parents.annotateForests d (source ++ [Parents.label d source coordinates]) hs) visible u c below state) :
      Parents.UnitSteps (d + 2) (BMS.parentTable (d + 2) (matrix (encodeForests d
        (Parents.annotateForests d (source ++ [Parents.label d source coordinates]) hs) visible u c below state))) := by
    cases hs with
    | nil => exact unit
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
      have forestUnit := encode_full_unitSteps d h (source ++ [a]) (visible ++ [state.length]) withSlot
        positive nextCoherent nextValid slotView separated.2.1 parented.1 slotOrder slotKnown slotPaths
        (scope.slot_full_unitSteps positive unit) childSafe
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
      exact encodeForests_full_unitSteps d hs source coordinates visible original
        (encode d (Parents.annotate d (source ++ [a]) h) (visible ++ [state.length]) withSlot)
        u c below positive sourceCoherent sourceValid view separated.2.2 parented.2 nextScope belowOrder
        (frameRealized_extends ((emit_extends ..).trans (encode_extends d _ _ _)) belowKnown)
        forestOrder forestKnown forestPaths forestUnit restSafe
end

/-- Full d+2-row numerical legality for the actual encoding. These are
literal finite input premises, not an assumed target parent table. -/
theorem source_numericallyLegal (d : Nat) (e : NumericalExpr) (positive : 0 < d)
    (separated : Source.ForestSeparated e) (parented : Source.ParentedAttachments d [] e) :
    BMS.NumericallyLegal (d + 2) (fromSource d e) := by
  refine ⟨source_width d e, ?_⟩
  exact encode_full_unitSteps d e [] [] [] positive (Parents.empty_coherent d) Parents.empty_context_valid
    (Parents.empty_numerical_view d) separated parented (by intro col member; simp at member)
    (by intro i col lookup; simp at lookup) (by intro i col lookup; simp at lookup)
    (Parents.empty_unitSteps (d + 2)) (source_noFallback d e)

theorem source_bms_expand_total (d : Nat) (e : NumericalExpr) (positive : 0 < d)
    (separated : Source.ForestSeparated e) (parented : Source.ParentedAttachments d [] e) (index : Nat) :
    ∃ result, BMS.expand? (d + 2) (fromSource d e) index = some result :=
  BMS.expand_total (d + 2) (fromSource d e) index (source_numericallyLegal d e positive separated parented)

end BTnSSBMS.Encoder
