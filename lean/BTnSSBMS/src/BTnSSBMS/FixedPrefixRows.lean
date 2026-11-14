import BTnSSBMS.EncoderRowTransport

/-! Initialize complete numerical transport at the root of a partial
rebase. An earlier prefix is fixed; the newly installed root changes by
one specified nonnegative amount in the chosen row. -/
namespace BTnSSBMS.Encoder

theorem prefix_rebase_forests_row (d : Nat) (hs : Forests (List Nat)) (source target : ParentContext)
    (coordinates newCoordinates visible nextVisible owners : List Nat)
    (materials : List (Forests (List Nat))) (ownerMaterial : Forests (List Nat))
    (original newOriginal state next : State d) (u v : Nat → Nat)
    (newGate c : Nat) (below : List Binding) (positive : 0 < d)
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
    (scope : NumericalGate d source coordinates visible original state u (original.length + 1))
    (newScope : NumericalGate d target newCoordinates nextVisible newOriginal next v newGate)
    (inherited : InheritedMaterials d source coordinates visible owners materials below)
    (width : coordinates.length = d)
    (ownerLegal : Source.FiniteLegalForests d (source ++ [Parents.label d source coordinates])
      (coordinates[0]?.getD 0) ownerMaterial)
    (legal : Source.FiniteLegalForests d (source ++ [Parents.label d source coordinates])
      (coordinates[0]?.getD 0) hs)
    (j amount : Nat) (room : j < d) (headValue : v j = u j + amount)
    (guardPrefix : emit (emit original u (c + 1) 1 []) (fun k => u k + 1) (c + 2) 2 [] <+: state) :
    RowRebaseTrace j original.length amount state next
      (encodeForests d (Parents.annotateForests d (source ++ [Parents.label d source coordinates]) hs) visible u c below state)
      (encodeForests d (Parents.annotateForests d (target ++ [Parents.label d target newCoordinates])
        (Source.relocateForests d (source ++ [Parents.label d source coordinates])
          (target ++ [Parents.label d target newCoordinates]) (List.range source.length ++ [target.length]) hs))
        nextVisible v c below next) := by
  cases hs with
  | nil => exact RowRebaseTrace.refl j original.length amount state next
  | cons h hs =>
    let a := Parents.label d source coordinates
    let newA := Parents.label d target newCoordinates
    let newH := Source.relocate d (source ++ [a]) (target ++ [newA]) (List.range source.length ++ [target.length]) h
    let withSlot := emit state (fun k => u k + 2) (c + 2) 0 below
    let newSlot := emit next (fun k => v k + 2) (c + 2) 0 below
    let withForest := encode d (Parents.annotate d (source ++ [a]) h) (visible ++ [state.length]) withSlot
    let newForest := encode d (Parents.annotate d (target ++ [newA]) newH) (nextVisible ++ [next.length]) newSlot
    have sourceCoherent' := Parents.coherent_append_label sourceCoherent coordinates
    have sourceValid' := Parents.context_valid_append_label d source sourceValid coordinates
    have targetCoherent' := Parents.coherent_append_label targetCoherent newCoordinates
    have targetValid' := Parents.context_valid_append_label d target targetValid newCoordinates
    have slotView := scope.slot_view sourceValid oldView (c + 2) below
    have newSlotView := newScope.slot_view targetValid newView (c + 2) below
    have slotKnown := (known.extends scope.extended).inherit_slot inherited ownerMaterial width ownerLegal (fun k => u k + 2) (c + 2)
    have belowPair := inherited.keys.fixed_prefix sourceCoherent sourceValid sourceUnit known.materialContext oldView
      (List.prefix_append source [a]) (initial.trans (List.prefix_append target [newA]))
      (List.prefix_append visible [state.length]) (List.prefix_append (List.range source.length) [target.length])
      (List.prefix_append materials [ownerMaterial])
    have slotPair := fixed_prefix_root_emit sourceCoherent sourceValid sourceUnit initial known oldView
      visiblePrefix newView.length scope.extended (statePrefix.trans newScope.extended)
      a newA ownerMaterial (fun k => u k + 2) (fun k => v k + 2) (c + 2) (c + 2) below below belowPair
    have rootBefore : original.length < state.length := by
      have longer := guardPrefix.length_le
      simp only [emit_length] at longer
      omega
    have slotTrace := RowRebaseTrace.emit state next (fun k => u k + 2) (fun k => v k + 2)
      (c + 2) 0 (c + 2) 0 below below j original.length amount room (by
        rw [scope.rowBump_slot (c + 2) below j original.length amount room rootBefore,
          rowBump_prefix guardPrefix j original.length amount (original.length + 1)
            (by simp only [emit_length]; omega),
          rowBump_guard original u c j original.length amount room (Nat.le_refl _), rowBump_self]
        omega)
    have values := fixed_prefix_row_values oldView.length visiblePrefix statePrefix
      (fun p inside => by simpa only [table_length] using oldView.bounded p inside) j amount
    have extendedValues := values.extends (result := withSlot) (newResult := newSlot)
      (fun p inside => by simpa only [table_length] using oldView.bounded p inside)
      (fun p inside => by
        have point : Parents.point (List.range source.length) p = p := by
          simp only [Parents.point, List.getElem?_range inside, Option.getD_some]
        rw [point]
        have targetBound : p < target.length := Nat.lt_of_lt_of_le inside initial.length_le
        simpa only [table_length] using newView.bounded p targetBound)
      (scope.extended.trans (emit_extends ..)) (newScope.extended.trans (emit_extends ..))
    have slotValues := extendedValues.append (by simp only [List.length_range]) oldView.length
      (fun p inside => by
        simp only [Parents.point, List.getElem?_range inside, Option.getD_some]
        rw [newView.length]
        exact Nat.lt_of_lt_of_le inside initial.length_le)
      state.length next.length (by
        simpa only [emit_length, Nat.add_sub_cancel] using slotTrace.last (by rw [emit_length]; omega))
    rw [newView.length] at slotValues
    have forestTrace := encode_relocation_row d h (source ++ [a]) (target ++ [newA])
      (List.range source.length ++ [target.length]) (visible ++ [state.length]) (nextVisible ++ [next.length])
      (owners ++ [source.length]) (materials ++ [ownerMaterial]) withSlot newSlot positive
      sourceCoherent' sourceValid' targetCoherent' targetValid' targetUnit view slotView newSlotView
      targetWidth slotKnown slotPair legal.2.1 j original.length amount room
      (by dsimp only [withSlot]; rw [emit_length]; omega)
      (by simpa only [List.length_append, List.length_cons, List.length_nil] using slotValues)
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
    have tailTrace := prefix_rebase_forests_row d hs source target coordinates newCoordinates visible nextVisible
      owners materials ownerMaterial original newOriginal withForest newForest u v newGate c below positive
      sourceCoherent sourceValid sourceUnit initial targetCoherent targetValid targetUnit view oldView newView targetWidth
      known visiblePrefix statePrefix nextScope nextNewScope inherited width ownerLegal legal.2.2 j amount room headValue
      (guardPrefix.trans ((emit_extends ..).trans (encode_extends ..)))
    exact (slotTrace.trans forestTrace).trans tailTrace

theorem prefix_rebase_encode_row (d : Nat) (coordinates newCoordinates : List Nat)
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
    (legal : Source.FiniteLegal d source (.cons coordinates hs tail))
    (j amount : Nat) (room : j < d)
    (headValue : vector next nextVisible (Parents.label d target newCoordinates) j =
      vector state visible (Parents.label d source coordinates) j + amount) :
    let a := Parents.label d source coordinates
    let newA := Parents.label d target newCoordinates
    let newHs := Source.relocateForests d (source ++ [a]) (target ++ [newA]) (List.range source.length ++ [target.length]) hs
    let newTail := Source.relocate d (source ++ [a]) (target ++ [newA]) (List.range source.length ++ [target.length]) tail
    RowRebaseTrace j state.length amount state next
      (encode d (Parents.annotate d source (.cons coordinates hs tail)) visible state)
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
  change v j = u j + amount at headValue
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
  have headTrace : RowRebaseTrace j state.length amount state next headed newHeaded := by
    cases found : equal frame key with
    | some bound =>
      have result := RowRebaseTrace.emit state next u v bound.height 0 bound.height 0
        (below ++ [{bound with latest := some state.length}])
        (below ++ [{bound with latest := some next.length}]) j state.length amount room
        (by rw [rowBump_self]; exact headValue)
      dsimp only [frame, key, queryKey, a] at found
      simp only [queryKey] at keySame
      dsimp only [headed, newHeaded, newHs, a, newA]
      simp only [headState, encode, oldView.length, newView.length, keySame, frameSame, found]
      exact result
    | none =>
      let first := emit state u (c + 1) 1 []
      let newFirst := emit next v (c + 1) 1 []
      let guarded := emit first (fun k => u k + 1) (c + 2) 2 []
      let newGuarded := emit newFirst (fun k => v k + 1) (c + 2) 2 []
      let forests := encodeForests d (Parents.annotateForests d (source ++ [a]) hs) visible u c below guarded
      let newForests := encodeForests d (Parents.annotateForests d (target ++ [newA]) newHs) nextVisible v c below newGuarded
      have forestTrace := prefix_rebase_forests_row d hs source target coordinates newCoordinates visible nextVisible
        owners materials hs state next guarded newGuarded u v (next.length + 1) c below positive
        sourceCoherent sourceValid sourceUnit initial targetCoherent targetValid targetUnit view oldView newView targetWidth
        known visiblePrefix statePrefix (initial_numerical_gate state sourceCoherent sourceValid oldView coordinates c)
        (initial_numerical_gate next targetCoherent targetValid newView newCoordinates c)
        (smaller_inheritedMaterials (queried_frame_inheritedMaterials known oldView coordinates) key)
        legal.1 legal.2.2.2.1 legal.2.2.2.1 j amount room headValue (List.prefix_refl _)
      have introTrace := (RowRebaseTrace.emit state next u v (c + 1) 1 (c + 1) 1 [] []
        j state.length amount room (by rw [rowBump_self]; exact headValue)).trans
        (RowRebaseTrace.emit first newFirst (fun k => u k + 1) (fun k => v k + 1)
          (c + 2) 2 (c + 2) 2 [] [] j state.length amount room (by
            dsimp only [first]
            rw [emit_length, rowBump_guard state u c j state.length amount room (Nat.le_refl _), rowBump_self]
            omega))
      have scope := encodeForests_numerical_gate d hs source coordinates visible state guarded u (state.length + 1)
        c below positive sourceCoherent sourceValid oldView
        (initial_numerical_gate state sourceCoherent sourceValid oldView coordinates c) legal.2.2.2.1.separated
      let finalFrame := below ++ [⟨key, c + 2, some forests.length, some state.length⟩]
      let newFinalFrame := below ++ [⟨key, c + 2, some newForests.length, some next.length⟩]
      have closeValue : v j + 1 = u j + 1 +
          rowBump (emit forests (fun k => u k + 1) (c + 2) 0 finalFrame) j state.length amount forests.length := by
        have edge := scope.closing_parents (encodeForests_extends ..) positive (c + 2) 0 finalFrame j room
        change Parents.parent (BMS.parentTable (d + 2) (matrix
          (emit forests (fun k => u k + 1) (c + 2) 0 finalFrame))) j forests.length = some state.length at edge
        have longer : guarded.length ≤ forests.length := (encodeForests_extends ..).length_le
        have distinct : state.length ≠ forests.length := by
          dsimp only [guarded, first] at longer
          simp only [emit_length] at longer
          omega
        rw [rowBump_parent distinct edge, rowBump_self]
        omega
      have result := (introTrace.trans forestTrace).trans
        (RowRebaseTrace.emit forests newForests (fun k => u k + 1) (fun k => v k + 1)
          (c + 2) 0 (c + 2) 0 finalFrame newFinalFrame j state.length amount room closeValue)
      dsimp only [frame, key, queryKey, a] at found
      simp only [queryKey] at keySame
      dsimp only [headed, newHeaded, newHs, a, newA]
      simp only [headState, encode, oldView.length, newView.length, keySame, frameSame, found]
      exact result
  have headNonempty : state.length < headed.length := by
    have before := headState_first_before_last d a (Parents.annotateForests d (source ++ [a]) hs) visible state
    have nonempty := headState_nonempty d a (Parents.annotateForests d (source ++ [a]) hs) visible state
    change state.length ≤ headed.length - 1 at before
    change 0 < headed.length at nonempty
    omega
  have values := fixed_prefix_row_values oldView.length visiblePrefix statePrefix
    (fun p inside => by simpa only [table_length] using oldView.bounded p inside) j amount
  have extendedValues := values.extends (result := headed) (newResult := newHeaded)
    (fun p inside => by simpa only [table_length] using oldView.bounded p inside)
    (fun p inside => by
      have point : Parents.point (List.range source.length) p = p := by
        simp only [Parents.point, List.getElem?_range inside, Option.getD_some]
      rw [point]
      simpa only [table_length] using newView.bounded p (Nat.lt_of_lt_of_le inside initial.length_le))
    headTrace.oldPrefix headTrace.newPrefix
  have finalValues := extendedValues.append (by simp only [List.length_range]) oldView.length
    (fun p inside => by
      simp only [Parents.point, List.getElem?_range inside, Option.getD_some]
      rw [newView.length]
      exact Nat.lt_of_lt_of_le inside initial.length_le)
    (headed.length - 1) (newHeaded.length - 1) (headTrace.last headNonempty)
  rw [newView.length] at finalValues
  have afterHead := prefix_rebase_head_coupled sourceCoherent sourceValid sourceUnit initial known oldView
    visiblePrefix newView.length statePrefix coordinates newCoordinates hs frameSame keySame
  have tailTrace := encode_relocation_row d tail (source ++ [a]) (target ++ [newA])
    (List.range source.length ++ [target.length]) (visible ++ [headed.length - 1]) (nextVisible ++ [newHeaded.length - 1])
    owners (materials ++ [hs]) headed newHeaded positive sourceCoherent' sourceValid' targetCoherent' targetValid'
    targetUnit view
    (headState_view state positive sourceCoherent sourceValid oldView coordinates hs legal.2.2.2.1.separated)
    (headState_view next positive targetCoherent targetValid newView newCoordinates newHs newLegal.separated)
    targetWidth (headState_materials known oldView coordinates hs legal.1 legal.2.2.2.1) afterHead legal.2.2.2.2
    j state.length amount room headNonempty
    (by simpa only [List.length_append, List.length_cons, List.length_nil] using finalValues)
  simpa only [Parents.annotate, encode_split_head] using headTrace.trans tailTrace

end BTnSSBMS.Encoder
