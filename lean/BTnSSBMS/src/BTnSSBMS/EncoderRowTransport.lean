import BTnSSBMS.RowRebaseValues

/-!
All internal numerical output columns under canonical relocation.
The shift at each column is selected by its actual old BMS ancestry.
Root initialization and identifying a complete zeroth block are separate.
-/
namespace BTnSSBMS.Encoder

private theorem width_append {d : Nat} {source : ParentContext} {coordinates : List Nat}
    (width : ∀ i, i < source.length → (source[i]?.getD default).coordinates.length = d)
    (headWidth : coordinates.length = d) :
    ∀ i, i < (source ++ [Parents.label d source coordinates]).length →
      ((source ++ [Parents.label d source coordinates])[i]?.getD default).coordinates.length = d := by
  intro i inside
  by_cases old : i < source.length
  · simpa only [List.getElem?_append_left old] using width i old
  · have last : i = source.length := by simp only [List.length_append, List.length_cons, List.length_nil] at inside; omega
    subst i
    simpa only [List.getElem?_concat_length, Option.getD_some, Parents.label] using headWidth

mutual
  theorem encode_relocation_row (d : Nat) (e : NumericalExpr) (source target : ParentContext)
      (moved visible nextVisible owners : List Nat) (materials : List (Forests (List Nat)))
      (state next : State d) (positive : 0 < d)
      (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
      (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
      (targetUnit : Parents.UnitSteps d target)
      (view : Parents.NumericalView d source target moved)
      (oldView : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
      (newView : Parents.NumericalView d target (BMS.parentTable (d + 2) (matrix next)) nextVisible)
      (targetWidth : ∀ i, i < target.length → (target[i]?.getD default).coordinates.length = d)
      (known : VisibleMaterials d source visible owners materials state)
      (related : CoupledFrames d source target moved visible nextVisible materials state next)
      (legal : Source.FiniteLegal d source e)
      (j root amount : Nat) (room : j < d) (rootBefore : root < state.length)
      (values : RowRebaseValues j root amount source.length moved visible nextVisible state next) :
      RowRebaseTrace j root amount state next (encode d (Parents.annotate d source e) visible state)
        (encode d (Parents.annotate d target (Source.relocate d source target moved e)) nextVisible next) := by
    cases e with
    | nil => exact RowRebaseTrace.refl j root amount state next
    | cons coordinates hs tail =>
      let a := Parents.label d source coordinates
      let newCoordinates := Source.relocationHead d source target moved coordinates
      let newA := Parents.label d target newCoordinates
      let newHs := Source.relocateForests d (source ++ [a]) (target ++ [newA]) (moved ++ [target.length]) hs
      let annotated := Parents.annotateForests d (source ++ [a]) hs
      let newAnnotated := Parents.annotateForests d (target ++ [newA]) newHs
      let headed := headState d a annotated visible state
      let newHeaded := headState d newA newAnnotated nextVisible next
      let key := queryKey d source coordinates hs
      let newKey := queryKey d target newCoordinates newHs
      let frame := frameAt state (representative visible a (d - 1))
      let newFrame := frameAt next (representative nextVisible newA (d - 1))
      let below := smaller frame key
      let newBelow := smaller newFrame newKey
      let c := (base below).height
      let u := vector state visible a
      let v := vector next nextVisible newA
      have query : MaterialQuery d source coordinates visible owners materials state hs :=
        ⟨queried_frame_inheritedMaterials known oldView coordinates, sourceCoherent, sourceValid,
          oldView, legal.1, legal.2.1, legal.2.2.2.1⟩
      have tests := related.query_tests query newView targetCoherent targetValid targetUnit view targetWidth positive
      have lookups : match equal frame key with
          | none => equal newFrame newKey = none
          | some old => ∃ new, equal newFrame newKey = some new ∧
              KeyBindingRel (fun b => (rekeyBinding d source target visible moved materials b).key) old new := tests.2.2
      have heights : (base newBelow).height = c := tests.1.base_height
      have newLegal := Source.relocate_finiteLegal d (.cons coordinates hs tail) source target moved
        sourceCoherent sourceValid targetCoherent targetValid targetUnit view positive legal
      have headValue (height tag : Nat) (saved : List Binding) :
          v j = u j + rowBump (emit state u height tag saved) j root amount state.length :=
        values.head_values sourceCoherent sourceValid targetCoherent targetValid view oldView newView
          coordinates height tag saved room rootBefore
      have headTrace : RowRebaseTrace j root amount state next headed newHeaded := by
        cases found : equal frame key with
        | some bound =>
          obtain ⟨newBound, newFound, pair⟩ := (show ∃ newBound,
            equal newFrame newKey = some newBound ∧
            KeyBindingRel (fun b => (rekeyBinding d source target visible moved materials b).key) bound newBound from
              by simpa only [found] using lookups)
          have result := RowRebaseTrace.emit state next u v bound.height 0 newBound.height 0
            (below ++ [{bound with latest := some state.length}])
            (newBelow ++ [{newBound with latest := some next.length}]) j root amount room (headValue ..)
          dsimp only [frame, key, newFrame, newKey, queryKey, a, newA, newCoordinates, newHs] at found newFound
          dsimp only [headed, newHeaded, annotated, newAnnotated, a, newA, newCoordinates, newHs]
          simp only [headState, encode, oldView.length, newView.length, found, newFound]
          exact result
        | none =>
          have newFresh : equal newFrame newKey = none := by simpa only [found] using lookups
          let first := emit state u (c + 1) 1 []
          let newFirst := emit next v (c + 1) 1 []
          let guarded := emit first (fun k => u k + 1) (c + 2) 2 []
          let newGuarded := emit newFirst (fun k => v k + 1) (c + 2) 2 []
          let forests := encodeForests d annotated visible u c below guarded
          let newForests := encodeForests d newAnnotated nextVisible v c newBelow newGuarded
          have headNumerical := headValue (c + 1) 1 []
          change v j = u j + rowBump first j root amount state.length at headNumerical
          have guardedNumerical : v j = u j + rowBump guarded j root amount (state.length + 1) := by
            rw [rowBump_guard state u c j root amount room (by omega)]
            exact headNumerical
          have forestTrace := encodeForests_relocation_row d hs source target coordinates moved visible nextVisible owners
            materials hs state next guarded newGuarded u v (state.length + 1) (next.length + 1) c below newBelow
            positive sourceCoherent sourceValid targetCoherent targetValid targetUnit view oldView newView
            targetWidth known related (initial_numerical_gate state sourceCoherent sourceValid oldView coordinates c)
            (initial_numerical_gate next targetCoherent targetValid newView newCoordinates c)
            (smaller_inheritedMaterials query.inherited key) tests.1 legal.1 legal.2.1 legal.2.2.2.1 legal.2.2.2.1
            j root amount room (by dsimp only [guarded, first]; simp only [emit_length]; omega)
            values guardedNumerical
          have initialTrace := (RowRebaseTrace.emit state next u v (c + 1) 1 (c + 1) 1 [] []
            j root amount room headNumerical).trans
            (RowRebaseTrace.emit first newFirst (fun k => u k + 1) (fun k => v k + 1)
              (c + 2) 2 (c + 2) 2 [] [] j root amount room (by
                have atGuard := rowBump_guard state u c j root amount room (by omega)
                dsimp only [first]
                rw [emit_length, atGuard]
                simpa only [first, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                  congrArg (fun z : Nat => z + 1) headNumerical))
          have scope := encodeForests_numerical_gate d hs source coordinates visible state guarded u (state.length + 1)
            c below positive sourceCoherent sourceValid oldView
            (initial_numerical_gate state sourceCoherent sourceValid oldView coordinates c) legal.2.2.2.1.separated
          let finalFrame := below ++ [⟨key, c + 2, some forests.length, some state.length⟩]
          let newFinalFrame := newBelow ++ [⟨newKey, c + 2, some newForests.length, some next.length⟩]
          have definitionPrefix : first <+: forests := (emit_extends ..).trans (encodeForests_extends ..)
          have closeValue : v j + 1 = u j + 1 +
              rowBump (emit forests (fun k => u k + 1) (c + 2) 0 finalFrame) j root amount forests.length := by
            have longer := definitionPrefix.length_le
            have edge := scope.closing_parents (encodeForests_extends ..) positive (c + 2) 0 finalFrame j room
            change Parents.parent (BMS.parentTable (d + 2) (matrix
              (emit forests (fun k => u k + 1) (c + 2) 0 finalFrame))) j forests.length = some state.length at edge
            rw [rowBump_parent (show root ≠ forests.length by dsimp only [first] at longer; rw [emit_length] at longer; omega) edge,
              rowBump_prefix (definitionPrefix.trans (emit_extends ..)) j root amount state.length
                (by dsimp only [first]; rw [emit_length]; omega)]
            omega
          have result := (initialTrace.trans forestTrace).trans
            (RowRebaseTrace.emit forests newForests (fun k => u k + 1) (fun k => v k + 1)
              (c + 2) 0 (c + 2) 0 finalFrame newFinalFrame j root amount room closeValue)
          dsimp only [frame, key, newFrame, newKey, queryKey, a, newA, newCoordinates, newHs] at found newFresh
          dsimp only [newBelow, newFrame, newKey, queryKey, a, newA, newCoordinates, newHs] at heights
          dsimp only [headed, newHeaded, annotated, newAnnotated, a, newA, newCoordinates, newHs]
          simp only [headState, encode, oldView.length, newView.length, found, newFresh, heights]
          exact result
      have headNonempty : state.length < headed.length := by
        have before := headState_first_before_last d a annotated visible state
        have nonempty := headState_nonempty d a annotated visible state
        change state.length ≤ headed.length - 1 at before
        change 0 < headed.length at nonempty
        omega
      have extendedValues := values.extends (result := headed) (newResult := newHeaded)
        (fun p inside => by simpa only [table_length] using oldView.bounded p inside)
        (fun p inside => by simpa only [table_length] using newView.bounded _ (view.bounded p inside))
        headTrace.oldPrefix headTrace.newPrefix
      have finalValues := extendedValues.append view.length oldView.length
        (fun p inside => by rw [newView.length]; exact view.bounded p inside)
        (headed.length - 1) (newHeaded.length - 1) (headTrace.last headNonempty)
      rw [newView.length] at finalValues
      have tailTrace := encode_relocation_row d tail (source ++ [a]) (target ++ [newA])
        (moved ++ [target.length]) (visible ++ [headed.length - 1]) (nextVisible ++ [newHeaded.length - 1])
        owners (materials ++ [hs]) headed newHeaded positive
        (Parents.coherent_append_label sourceCoherent coordinates)
        (Parents.context_valid_append_label d source sourceValid coordinates)
        (Parents.coherent_append_label targetCoherent newCoordinates)
        (Parents.context_valid_append_label d target targetValid newCoordinates)
        (Source.relocationHead_unitSteps sourceCoherent sourceValid targetCoherent targetValid targetUnit view coordinates)
        (Source.relocation_view_append sourceCoherent sourceValid targetCoherent targetValid view coordinates)
        (headState_view state positive sourceCoherent sourceValid oldView coordinates hs legal.2.2.2.1.separated)
        (headState_view next positive targetCoherent targetValid newView newCoordinates newHs newLegal.2.2.2.1.separated)
        (width_append targetWidth (Source.relocationHead_width d source target moved coordinates))
        (headState_materials known oldView coordinates hs legal.1 legal.2.2.2.1)
        (related.head known query newView targetCoherent targetValid targetUnit view targetWidth positive)
        legal.2.2.2.2 j root amount room (by omega)
        (by simpa only [List.length_append, List.length_cons, List.length_nil] using finalValues)
      simpa only [Parents.annotate, Source.relocate, encode_split_head] using headTrace.trans tailTrace

  theorem encodeForests_relocation_row (d : Nat) (hs : Forests (List Nat)) (source target : ParentContext)
      (coordinates moved visible nextVisible owners : List Nat) (materials : List (Forests (List Nat)))
      (ownerMaterial : Forests (List Nat)) (original newOriginal state next : State d)
      (u v : Nat → Nat) (gate newGate c : Nat) (below newBelow : List Binding)
      (positive : 0 < d) (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
      (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
      (targetUnit : Parents.UnitSteps d target) (view : Parents.NumericalView d source target moved)
      (oldView : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix original)) visible)
      (newView : Parents.NumericalView d target (BMS.parentTable (d + 2) (matrix newOriginal)) nextVisible)
      (targetWidth : ∀ i, i < target.length → (target[i]?.getD default).coordinates.length = d)
      (known : VisibleMaterials d source visible owners materials original)
      (related : CoupledFrames d source target moved visible nextVisible materials original newOriginal)
      (scope : NumericalGate d source coordinates visible original state u gate)
      (newScope : NumericalGate d target (Source.relocationHead d source target moved coordinates) nextVisible newOriginal next v newGate)
      (inherited : InheritedMaterials d source coordinates visible owners materials below)
      (belowRelated : KeyFrameRel (fun b => (rekeyBinding d source target visible moved materials b).key) below newBelow)
      (width : coordinates.length = d)
      (unit : Parents.UnitSteps d (source ++ [Parents.label d source coordinates]))
      (ownerLegal : Source.FiniteLegalForests d (source ++ [Parents.label d source coordinates]) (coordinates[0]?.getD 0) ownerMaterial)
      (legal : Source.FiniteLegalForests d (source ++ [Parents.label d source coordinates]) (coordinates[0]?.getD 0) hs)
      (j root amount : Nat) (room : j < d) (rootBefore : root < state.length)
      (values : RowRebaseValues j root amount source.length moved visible nextVisible original newOriginal)
      (gateValue : v j = u j + rowBump state j root amount gate) :
      let a := Parents.label d source coordinates
      let newCoordinates := Source.relocationHead d source target moved coordinates
      let newA := Parents.label d target newCoordinates
      RowRebaseTrace j root amount state next
        (encodeForests d (Parents.annotateForests d (source ++ [a]) hs) visible u c below state)
        (encodeForests d (Parents.annotateForests d (target ++ [newA])
          (Source.relocateForests d (source ++ [a]) (target ++ [newA]) (moved ++ [target.length]) hs)) nextVisible v c newBelow next) := by
    cases hs with
    | nil => exact RowRebaseTrace.refl j root amount state next
    | cons h hs =>
      let a := Parents.label d source coordinates
      let newCoordinates := Source.relocationHead d source target moved coordinates
      let newA := Parents.label d target newCoordinates
      let newH := Source.relocate d (source ++ [a]) (target ++ [newA]) (moved ++ [target.length]) h
      let withSlot := emit state (fun k => u k + 2) (c + 2) 0 below
      let newSlot := emit next (fun k => v k + 2) (c + 2) 0 newBelow
      let withForest := encode d (Parents.annotate d (source ++ [a]) h) (visible ++ [state.length]) withSlot
      let newForest := encode d (Parents.annotate d (target ++ [newA]) newH) (nextVisible ++ [next.length]) newSlot
      have sourceCoherent' := Parents.coherent_append_label sourceCoherent coordinates
      have sourceValid' := Parents.context_valid_append_label d source sourceValid coordinates
      have targetCoherent' := Parents.coherent_append_label targetCoherent newCoordinates
      have targetValid' := Parents.context_valid_append_label d target targetValid newCoordinates
      have view' := Source.relocation_view_append sourceCoherent sourceValid targetCoherent targetValid view coordinates
      have targetUnit' := Source.relocationHead_unitSteps sourceCoherent sourceValid targetCoherent targetValid targetUnit view coordinates
      have width' := width_append targetWidth (Source.relocationHead_width d source target moved coordinates)
      have slotView := scope.slot_view sourceValid oldView (c + 2) below
      have newSlotView := newScope.slot_view targetValid newView (c + 2) newBelow
      have slotKnown := (known.extends scope.extended).inherit_slot inherited ownerMaterial width ownerLegal (fun k => u k + 2) (c + 2)
      have slotPair := (related.extends scope.extended newScope.extended).append_emit
        (known.extends scope.extended) oldView view newView.length a newA ownerMaterial
        (fun k => u k + 2) (fun k => v k + 2) (c + 2) (c + 2) below newBelow
        (inherited.keys.rekey_prefix oldView view known.materialContext.length
          (List.prefix_append source [a]) (List.prefix_append target [newA]) (List.prefix_append visible [state.length])
          (List.prefix_append moved [target.length]) (List.prefix_append materials [ownerMaterial]) belowRelated)
      have slotTrace := RowRebaseTrace.emit state next (fun k => u k + 2) (fun k => v k + 2)
        (c + 2) 0 (c + 2) 0 below newBelow j root amount room (by
          rw [scope.rowBump_slot (c + 2) below j root amount room rootBefore]
          omega)
      have extendedValues := values.extends (result := withSlot) (newResult := newSlot)
        (fun p inside => by simpa only [table_length] using oldView.bounded p inside)
        (fun p inside => by simpa only [table_length] using newView.bounded _ (view.bounded p inside))
        (scope.extended.trans (emit_extends ..)) (newScope.extended.trans (emit_extends ..))
      have slotValues := extendedValues.append view.length oldView.length
        (fun p inside => by rw [newView.length]; exact view.bounded p inside)
        state.length next.length (by
          simpa only [emit_length, Nat.add_sub_cancel] using slotTrace.last (by rw [emit_length]; omega))
      rw [newView.length] at slotValues
      have forestTrace := encode_relocation_row d h (source ++ [a]) (target ++ [newA]) (moved ++ [target.length])
        (visible ++ [state.length]) (nextVisible ++ [next.length]) (owners ++ [source.length])
        (materials ++ [ownerMaterial]) withSlot newSlot positive sourceCoherent' sourceValid' targetCoherent' targetValid'
        targetUnit' view' slotView newSlotView width' slotKnown slotPair legal.2.1
        j root amount room (by dsimp only [withSlot]; rw [emit_length]; omega)
        (by simpa only [List.length_append, List.length_cons, List.length_nil] using slotValues)
      obtain ⟨finalVisible, extended, forestView⟩ := encode_numerical_view d h (source ++ [a])
        (visible ++ [state.length]) withSlot positive sourceCoherent' sourceValid' slotView legal.2.1.separated
      have nextScope := scope.after_forest positive sourceCoherent sourceValid oldView.length (c + 2) below
        (Source.labels h) (encode_extends d _ _ _) extended legal.1 forestView
      have newLegal := Source.relocateForests_finiteLegal d (.cons h hs) (source ++ [a]) (target ++ [newA]) (moved ++ [target.length])
        sourceCoherent' sourceValid' targetCoherent' targetValid' targetUnit' view' positive source.length
        (by simp) (by simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_sub_cancel]; exact .refl _)
        (by simpa only [a, Parents.reading_append_label] using legal)
      simp only [← view.length, Parents.point_append_last, newA, Parents.reading_append_label] at newLegal
      obtain ⟨finalNewVisible, newExtended, newForestView⟩ := encode_numerical_view d newH (target ++ [newA])
        (nextVisible ++ [next.length]) newSlot positive targetCoherent' targetValid' newSlotView newLegal.2.1.separated
      have nextNewScope := newScope.after_forest positive targetCoherent targetValid newView.length (c + 2) newBelow
        (Source.labels newH) (encode_extends d _ _ _) newExtended newLegal.1 newForestView
      have statePrefix : state <+: withForest := (emit_extends ..).trans (encode_extends ..)
      have tailTrace := encodeForests_relocation_row d hs source target coordinates moved visible nextVisible owners materials
        ownerMaterial original newOriginal withForest newForest u v gate newGate c below newBelow positive
        sourceCoherent sourceValid targetCoherent targetValid targetUnit view oldView newView targetWidth known related
        nextScope nextNewScope inherited belowRelated width unit ownerLegal legal.2.2
        j root amount room (by have := statePrefix.length_le; omega) values
        (by rw [rowBump_prefix statePrefix j root amount gate scope.bounded]; exact gateValue)
      exact (slotTrace.trans forestTrace).trans tailTrace
end

end BTnSSBMS.Encoder
