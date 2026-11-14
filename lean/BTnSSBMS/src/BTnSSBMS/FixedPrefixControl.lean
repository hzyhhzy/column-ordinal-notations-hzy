import BTnSSBMS.PartialRebaseCoupling
import BTnSSBMS.EncoderControlTransport

/-!
Transport the forests of a root appended after a longer shared prefix.
Only the after-root numerical view is needed. Each real forest slot is
initialized from fixed old frames, then the full recursive transport
theorem applies inside that forest. Sibling exits restore both scopes.
-/
namespace BTnSSBMS.Encoder

theorem prefix_rebase_forests_control (d : Nat) (hs : Forests (List Nat)) (source target : ParentContext)
    (coordinates newCoordinates visible nextVisible owners : List Nat)
    (materials : List (Forests (List Nat))) (ownerMaterial : Forests (List Nat))
    (original newOriginal state next : State d) (u v : Nat → Nat)
    (gate newGate c : Nat) (below : List Binding) (positive : 0 < d)
    (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
    (sourceUnit : Parents.UnitSteps d source) (initial : source <+: target)
    (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
    (targetUnit : Parents.UnitSteps d (target ++ [Parents.label d target newCoordinates]))
    (view : Parents.NumericalView d (source ++ [Parents.label d source coordinates])
      (target ++ [Parents.label d target newCoordinates]) (List.range source.length ++ [target.length]))
    (oldView : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix original)) visible)
    (newView : Parents.NumericalView d target (BMS.parentTable (d + 2) (matrix newOriginal)) nextVisible)
    (targetWidth : ∀ i, i < (target ++ [Parents.label d target newCoordinates]).length →
      ((target ++ [Parents.label d target newCoordinates])[i]?.getD default).coordinates.length = d)
    (known : VisibleMaterials d source visible owners materials original)
    (visiblePrefix : visible <+: nextVisible) (statePrefix : original <+: newOriginal)
    (scope : NumericalGate d source coordinates visible original state u gate)
    (newScope : NumericalGate d target newCoordinates nextVisible newOriginal next v newGate)
    (inherited : InheritedMaterials d source coordinates visible owners materials below)
    (width : coordinates.length = d)
    (ownerLegal : Source.FiniteLegalForests d (source ++ [Parents.label d source coordinates])
      (coordinates[0]?.getD 0) ownerMaterial)
    (legal : Source.FiniteLegalForests d (source ++ [Parents.label d source coordinates])
      (coordinates[0]?.getD 0) hs) :
    SharedTrace state next
      (encodeForests d (Parents.annotateForests d (source ++ [Parents.label d source coordinates]) hs) visible u c below state)
      (encodeForests d (Parents.annotateForests d (target ++ [Parents.label d target newCoordinates])
        (Source.relocateForests d (source ++ [Parents.label d source coordinates])
          (target ++ [Parents.label d target newCoordinates]) (List.range source.length ++ [target.length]) hs))
        nextVisible v c below next) := by
  cases hs with
  | nil => exact SharedTrace.refl state next
  | cons h hs =>
    let a := Parents.label d source coordinates
    let newA := Parents.label d target newCoordinates
    let newH := Source.relocate d (source ++ [a]) (target ++ [newA]) (List.range source.length ++ [target.length]) h
    let withSlot := emit state (fun j => u j + 2) (c + 2) 0 below
    let newSlot := emit next (fun j => v j + 2) (c + 2) 0 below
    let withForest := encode d (Parents.annotate d (source ++ [a]) h) (visible ++ [state.length]) withSlot
    let newForest := encode d (Parents.annotate d (target ++ [newA]) newH) (nextVisible ++ [next.length]) newSlot
    have sourceCoherent' := Parents.coherent_append_label sourceCoherent coordinates
    have sourceValid' := Parents.context_valid_append_label d source sourceValid coordinates
    have targetCoherent' := Parents.coherent_append_label targetCoherent newCoordinates
    have targetValid' := Parents.context_valid_append_label d target targetValid newCoordinates
    have slotView := scope.slot_view sourceValid oldView (c + 2) below
    have newSlotView := newScope.slot_view targetValid newView (c + 2) below
    have slotKnown := (known.extends scope.extended).inherit_slot inherited ownerMaterial width ownerLegal (fun j => u j + 2) (c + 2)
    have belowPair := inherited.keys.fixed_prefix sourceCoherent sourceValid sourceUnit known.materialContext oldView
      (List.prefix_append source [a]) (initial.trans (List.prefix_append target [newA]))
      (List.prefix_append visible [state.length]) (List.prefix_append (List.range source.length) [target.length])
      (List.prefix_append materials [ownerMaterial])
    have slotPair := fixed_prefix_root_emit sourceCoherent sourceValid sourceUnit initial known oldView
      visiblePrefix newView.length scope.extended (statePrefix.trans newScope.extended)
      a newA ownerMaterial (fun j => u j + 2) (fun j => v j + 2) (c + 2) (c + 2) below below belowPair
    have forestTrace := encode_relocation_control d h (source ++ [a]) (target ++ [newA])
      (List.range source.length ++ [target.length]) (visible ++ [state.length]) (nextVisible ++ [next.length])
      (owners ++ [source.length]) (materials ++ [ownerMaterial]) withSlot newSlot positive
      sourceCoherent' sourceValid' targetCoherent' targetValid' targetUnit view slotView newSlotView
      targetWidth slotKnown slotPair legal.2.1
    obtain ⟨finalVisible, extended, forestView⟩ := encode_numerical_view d h (source ++ [a])
      (visible ++ [state.length]) withSlot positive sourceCoherent' sourceValid' slotView legal.2.1.separated
    have nextScope := scope.after_forest positive sourceCoherent sourceValid oldView.length (c + 2) below
      (Source.labels h) (encode_extends d _ _ _) extended legal.1 forestView
    have newLegal := Source.relocateForests_finiteLegal d (.cons h hs) (source ++ [a]) (target ++ [newA])
      (List.range source.length ++ [target.length]) sourceCoherent' sourceValid' targetCoherent' targetValid'
      targetUnit view positive source.length (by simp)
      (by simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_sub_cancel]; exact .refl _)
      (by simpa only [a, Parents.reading_append_label] using legal)
    have endpoint : Parents.point (List.range source.length ++ [target.length]) source.length = target.length := by
      simpa only [List.length_range] using Parents.point_append_last (List.range source.length) target.length
    rw [endpoint, Parents.reading_append_label] at newLegal
    obtain ⟨finalNewVisible, newExtended, newForestView⟩ := encode_numerical_view d newH (target ++ [newA])
      (nextVisible ++ [next.length]) newSlot positive targetCoherent' targetValid' newSlotView newLegal.2.1.separated
    have nextNewScope := newScope.after_forest positive targetCoherent targetValid newView.length (c + 2) below
      (Source.labels newH) (encode_extends d _ _ _) newExtended newLegal.1 newForestView
    have tailTrace := prefix_rebase_forests_control d hs source target coordinates newCoordinates visible nextVisible
      owners materials ownerMaterial original newOriginal withForest newForest u v gate newGate c below positive
      sourceCoherent sourceValid sourceUnit initial targetCoherent targetValid targetUnit view oldView newView targetWidth
      known visiblePrefix statePrefix nextScope nextNewScope inherited width ownerLegal legal.2.2
    exact ((SharedTrace.emit state next (fun j => u j + 2) (fun j => v j + 2) (c + 2) 0 below below).trans forestTrace).trans tailTrace

/-- Complete actual execution at a shared-prefix rebase entry. The
after-root view is sufficient; no impossible pre-root frontier and no
unproved initial frame pairing are required. -/
theorem prefix_rebase_encode_control (d : Nat) (coordinates newCoordinates : List Nat)
    (hs : Forests (List Nat)) (tail : NumericalExpr) (source target : ParentContext)
    (visible nextVisible owners : List Nat) (materials : List (Forests (List Nat)))
    (state next : State d) (positive : 0 < d)
    (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
    (sourceUnit : Parents.UnitSteps d source) (initial : source <+: target)
    (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
    (targetUnit : Parents.UnitSteps d (target ++ [Parents.label d target newCoordinates]))
    (view : Parents.NumericalView d (source ++ [Parents.label d source coordinates])
      (target ++ [Parents.label d target newCoordinates]) (List.range source.length ++ [target.length]))
    (oldView : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (newView : Parents.NumericalView d target (BMS.parentTable (d + 2) (matrix next)) nextVisible)
    (targetWidth : ∀ i, i < (target ++ [Parents.label d target newCoordinates]).length →
      ((target ++ [Parents.label d target newCoordinates])[i]?.getD default).coordinates.length = d)
    (known : VisibleMaterials d source visible owners materials state)
    (visiblePrefix : visible <+: nextVisible) (statePrefix : state <+: next)
    (frameSame : frameAt next (representative nextVisible (Parents.label d target newCoordinates) (d - 1)) =
      frameAt state (representative visible (Parents.label d source coordinates) (d - 1)))
    (keySame : queryKey d target newCoordinates
      (Source.relocateForests d (source ++ [Parents.label d source coordinates])
        (target ++ [Parents.label d target newCoordinates]) (List.range source.length ++ [target.length]) hs) =
      queryKey d source coordinates hs)
    (legal : Source.FiniteLegal d source (.cons coordinates hs tail)) :
    let a := Parents.label d source coordinates
    let newA := Parents.label d target newCoordinates
    let newHs := Source.relocateForests d (source ++ [a]) (target ++ [newA]) (List.range source.length ++ [target.length]) hs
    let newTail := Source.relocate d (source ++ [a]) (target ++ [newA]) (List.range source.length ++ [target.length]) tail
    SharedTrace state next (encode d (Parents.annotate d source (.cons coordinates hs tail)) visible state)
      (encode d (Parents.annotate d target (.cons newCoordinates newHs newTail)) nextVisible next) := by
  let a := Parents.label d source coordinates
  let newA := Parents.label d target newCoordinates
  let newHs := Source.relocateForests d (source ++ [a]) (target ++ [newA]) (List.range source.length ++ [target.length]) hs
  let headed := headState d a (Parents.annotateForests d (source ++ [a]) hs) visible state
  let newHeaded := headState d newA (Parents.annotateForests d (target ++ [newA]) newHs) nextVisible next
  let key := queryKey d source coordinates hs
  let frame := frameAt state (representative visible a (d - 1))
  let below := smaller frame key
  let c := (base below).height
  let u := vector state visible a
  let v := vector next nextVisible newA
  have sourceCoherent' := Parents.coherent_append_label sourceCoherent coordinates
  have sourceValid' := Parents.context_valid_append_label d source sourceValid coordinates
  have targetCoherent' := Parents.coherent_append_label targetCoherent newCoordinates
  have targetValid' := Parents.context_valid_append_label d target targetValid newCoordinates
  have newLegal := Source.relocateForests_finiteLegal d hs (source ++ [a]) (target ++ [newA])
    (List.range source.length ++ [target.length]) sourceCoherent' sourceValid' targetCoherent' targetValid'
    targetUnit view positive source.length (by simp)
    (by simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_sub_cancel]; exact .refl _)
    (by simpa only [a, Parents.reading_append_label] using legal.2.2.2.1)
  have endpoint : Parents.point (List.range source.length ++ [target.length]) source.length = target.length := by
    simpa only [List.length_range] using Parents.point_append_last (List.range source.length) target.length
  rw [endpoint, Parents.reading_append_label] at newLegal
  have afterHead := prefix_rebase_head_coupled sourceCoherent sourceValid sourceUnit initial known oldView
    visiblePrefix newView.length statePrefix coordinates newCoordinates hs frameSame keySame
  have tailTrace := encode_relocation_control d tail (source ++ [a]) (target ++ [newA])
    (List.range source.length ++ [target.length]) (visible ++ [headed.length - 1]) (nextVisible ++ [newHeaded.length - 1])
    owners (materials ++ [hs]) headed newHeaded positive sourceCoherent' sourceValid' targetCoherent' targetValid'
    targetUnit view
    (headState_view state positive sourceCoherent sourceValid oldView coordinates hs legal.2.2.2.1.separated)
    (headState_view next positive targetCoherent targetValid newView newCoordinates newHs newLegal.separated)
    targetWidth (headState_materials known oldView coordinates hs legal.1 legal.2.2.2.1) afterHead legal.2.2.2.2
  have headTrace : SharedTrace state next headed newHeaded := by
    cases found : equal frame key with
    | some bound =>
      have result := SharedTrace.emit state next u v bound.height 0
        (below ++ [{bound with latest := some state.length}])
        (below ++ [{bound with latest := some next.length}])
      dsimp only [frame, key, queryKey, a] at found
      simp only [queryKey] at keySame
      dsimp only [headed, newHeaded, newHs, a, newA]
      simp only [headState, encode, oldView.length, newView.length, keySame, frameSame, found]
      exact result
    | none =>
      let withDefinition := emit state u (c + 1) 1 []
      let newDefinition := emit next v (c + 1) 1 []
      let withGuard := emit withDefinition (fun j => u j + 1) (c + 2) 2 []
      let newGuard := emit newDefinition (fun j => v j + 1) (c + 2) 2 []
      let withForests := encodeForests d (Parents.annotateForests d (source ++ [a]) hs) visible u c below withGuard
      let newForests := encodeForests d (Parents.annotateForests d (target ++ [newA]) newHs) nextVisible v c below newGuard
      have forestTrace := prefix_rebase_forests_control d hs source target coordinates newCoordinates visible nextVisible
        owners materials hs state next withGuard newGuard u v (state.length + 1) (next.length + 1) c below positive
        sourceCoherent sourceValid sourceUnit initial targetCoherent targetValid targetUnit view oldView newView targetWidth
        known visiblePrefix statePrefix (initial_numerical_gate state sourceCoherent sourceValid oldView coordinates c)
        (initial_numerical_gate next targetCoherent targetValid newView newCoordinates c)
        (smaller_inheritedMaterials (queried_frame_inheritedMaterials known oldView coordinates) key)
        legal.1 legal.2.2.2.1 legal.2.2.2.1
      have result := (((SharedTrace.emit state next u v (c + 1) 1 [] []).trans
        (SharedTrace.emit withDefinition newDefinition (fun j => u j + 1) (fun j => v j + 1) (c + 2) 2 [] [])).trans
        forestTrace).trans (SharedTrace.emit withForests newForests (fun j => u j + 1) (fun j => v j + 1) (c + 2) 0
          (below ++ [⟨key, c + 2, some withForests.length, some state.length⟩])
          (below ++ [⟨key, c + 2, some newForests.length, some next.length⟩]))
      dsimp only [frame, key, queryKey, a] at found
      simp only [queryKey] at keySame
      dsimp only [headed, newHeaded, newHs, a, newA]
      simp only [headState, encode, oldView.length, newView.length, keySame, frameSame, found]
      exact result
  simpa only [Parents.annotate, encode_split_head] using headTrace.trans tailTrace

end BTnSSBMS.Encoder
