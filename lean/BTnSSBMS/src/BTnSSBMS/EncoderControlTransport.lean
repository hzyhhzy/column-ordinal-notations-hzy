import BTnSSBMS.ControlTrace

/-!
Transport the actual key/tag output through the whole mutual encoder.
Attached lists are moved canonically, with their full original material
at each owner. This theorem does not cover replacement by a donated list.
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
  theorem encode_relocation_control (d : Nat) (e : NumericalExpr) (source target : ParentContext)
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
      (legal : Source.FiniteLegal d source e) :
      SharedTrace state next (encode d (Parents.annotate d source e) visible state)
        (encode d (Parents.annotate d target (Source.relocate d source target moved e)) nextVisible next) := by
    cases e with
    | nil => exact SharedTrace.refl state next
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
      have sourceCoherent' := Parents.coherent_append_label sourceCoherent coordinates
      have sourceValid' := Parents.context_valid_append_label d source sourceValid coordinates
      have targetCoherent' := Parents.coherent_append_label targetCoherent newCoordinates
      have targetValid' := Parents.context_valid_append_label d target targetValid newCoordinates
      have view' := Source.relocation_view_append sourceCoherent sourceValid targetCoherent targetValid view coordinates
      have targetUnit' := Source.relocationHead_unitSteps sourceCoherent sourceValid targetCoherent targetValid targetUnit view coordinates
      have newLegal := Source.relocate_finiteLegal d (.cons coordinates hs tail) source target moved
        sourceCoherent sourceValid targetCoherent targetValid targetUnit view positive legal
      have afterHead := related.head known query newView targetCoherent targetValid targetUnit view targetWidth positive
      have tailTrace := encode_relocation_control d tail (source ++ [a]) (target ++ [newA])
        (moved ++ [target.length]) (visible ++ [headed.length - 1]) (nextVisible ++ [newHeaded.length - 1])
        owners (materials ++ [hs]) headed newHeaded positive sourceCoherent' sourceValid' targetCoherent' targetValid'
        targetUnit' view'
        (headState_view state positive sourceCoherent sourceValid oldView coordinates hs legal.2.2.2.1.separated)
        (headState_view next positive targetCoherent targetValid newView newCoordinates newHs newLegal.2.2.2.1.separated)
        (width_append targetWidth (Source.relocationHead_width d source target moved coordinates))
        (headState_materials known oldView coordinates hs legal.1 legal.2.2.2.1) afterHead legal.2.2.2.2
      have headTrace : SharedTrace state next headed newHeaded := by
        cases found : equal frame key with
        | some bound =>
          obtain ⟨newBound, newFound, pair⟩ := (show ∃ newBound,
            equal newFrame newKey = some newBound ∧
            KeyBindingRel (fun b => (rekeyBinding d source target visible moved materials b).key) bound newBound from
              by simpa only [found] using lookups)
          have result := SharedTrace.emit state next u v bound.height 0
            (below ++ [{bound with latest := some state.length}]) (newBelow ++ [{newBound with latest := some next.length}])
          dsimp only [frame, key, newFrame, newKey, queryKey, a, newA, newCoordinates, newHs] at found newFound
          dsimp only [headed, newHeaded, annotated, newAnnotated, a, newA, newCoordinates, newHs]
          simp only [headState, encode, oldView.length, newView.length, found, newFound, pair.2]
          dsimp only [u, v, below, newBelow, frame, newFrame, key, newKey, queryKey, a, newA, newCoordinates, newHs] at result
          simpa only [pair.2] using result
        | none =>
          have newFresh : equal newFrame newKey = none := by simpa only [found] using lookups
          let guarded := emit (emit state u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 []
          let newGuarded := emit (emit next v (c + 1) 1 []) (fun j => v j + 1) (c + 2) 2 []
          let forests := encodeForests d annotated visible u c below guarded
          let newForests := encodeForests d newAnnotated nextVisible v c newBelow newGuarded
          have forestTrace := encodeForests_relocation_control d hs source target coordinates moved visible nextVisible owners
            materials hs state next guarded newGuarded u v (state.length + 1) (next.length + 1) c below newBelow
            positive sourceCoherent sourceValid targetCoherent targetValid targetUnit view oldView newView
            targetWidth known related (initial_numerical_gate state sourceCoherent sourceValid oldView coordinates c)
            (initial_numerical_gate next targetCoherent targetValid newView newCoordinates c)
            (smaller_inheritedMaterials query.inherited key) tests.1 legal.1 legal.2.1 legal.2.2.2.1 legal.2.2.2.1
          have introTrace : SharedTrace state next guarded newGuarded :=
            (SharedTrace.emit state next u v (c + 1) 1 [] []).trans
              (SharedTrace.emit _ _ (fun j => u j + 1) (fun j => v j + 1) (c + 2) 2 [] [])
          have closeTrace := SharedTrace.emit forests newForests (fun j => u j + 1) (fun j => v j + 1) (c + 2) 0
            (below ++ [⟨key, c + 2, some forests.length, some state.length⟩])
            (newBelow ++ [⟨newKey, c + 2, some newForests.length, some next.length⟩])
          have result := (introTrace.trans forestTrace).trans closeTrace
          dsimp only [frame, key, newFrame, newKey, queryKey, a, newA, newCoordinates, newHs] at found newFresh
          dsimp only [newBelow, newFrame, newKey, queryKey, a, newA, newCoordinates, newHs] at heights
          dsimp only [headed, newHeaded, annotated, newAnnotated, a, newA, newCoordinates, newHs]
          simp only [headState, encode, oldView.length, newView.length, found, newFresh, heights]
          exact result
      simpa only [Parents.annotate, Source.relocate, encode_split_head] using headTrace.trans tailTrace

  theorem encodeForests_relocation_control (d : Nat) (hs : Forests (List Nat)) (source target : ParentContext)
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
      (legal : Source.FiniteLegalForests d (source ++ [Parents.label d source coordinates]) (coordinates[0]?.getD 0) hs) :
      let a := Parents.label d source coordinates
      let newCoordinates := Source.relocationHead d source target moved coordinates
      let newA := Parents.label d target newCoordinates
      SharedTrace state next (encodeForests d (Parents.annotateForests d (source ++ [a]) hs) visible u c below state)
        (encodeForests d (Parents.annotateForests d (target ++ [newA])
          (Source.relocateForests d (source ++ [a]) (target ++ [newA]) (moved ++ [target.length]) hs)) nextVisible v c newBelow next) := by
    cases hs with
    | nil => exact SharedTrace.refl state next
    | cons h hs =>
      let a := Parents.label d source coordinates
      let newCoordinates := Source.relocationHead d source target moved coordinates
      let newA := Parents.label d target newCoordinates
      let newH := Source.relocate d (source ++ [a]) (target ++ [newA]) (moved ++ [target.length]) h
      let withSlot := emit state (fun j => u j + 2) (c + 2) 0 below
      let newSlot := emit next (fun j => v j + 2) (c + 2) 0 newBelow
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
      have slotKnown := (known.extends scope.extended).inherit_slot inherited ownerMaterial width ownerLegal (fun j => u j + 2) (c + 2)
      have slotPair := (related.extends scope.extended newScope.extended).append_emit
        (known.extends scope.extended) oldView view newView.length a newA ownerMaterial
        (fun j => u j + 2) (fun j => v j + 2) (c + 2) (c + 2) below newBelow
        (inherited.keys.rekey_prefix oldView view known.materialContext.length
          (List.prefix_append source [a]) (List.prefix_append target [newA]) (List.prefix_append visible [state.length])
          (List.prefix_append moved [target.length]) (List.prefix_append materials [ownerMaterial]) belowRelated)
      have forestTrace := encode_relocation_control d h (source ++ [a]) (target ++ [newA]) (moved ++ [target.length])
        (visible ++ [state.length]) (nextVisible ++ [next.length]) (owners ++ [source.length])
        (materials ++ [ownerMaterial]) withSlot newSlot positive sourceCoherent' sourceValid' targetCoherent' targetValid'
        targetUnit' view' slotView newSlotView width' slotKnown slotPair legal.2.1
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
      have tailTrace := encodeForests_relocation_control d hs source target coordinates moved visible nextVisible owners materials
        ownerMaterial original newOriginal withForest newForest u v gate newGate c below newBelow positive
        sourceCoherent sourceValid targetCoherent targetValid targetUnit view oldView newView targetWidth known related
        nextScope nextNewScope inherited belowRelated width unit ownerLegal legal.2.2
      exact ((SharedTrace.emit state next (fun j => u j + 2) (fun j => v j + 2) (c + 2) 0 below newBelow).trans forestTrace).trans tailTrace
end

end BTnSSBMS.Encoder
