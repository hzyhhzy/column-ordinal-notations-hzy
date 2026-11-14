import BTnSSBMS.RootedDecision
import BTnSSBMS.FreshShift
import BTnSSBMS.EncoderRootedTransport
import BTnSSBMS.RootedSlots

/-!
Complete output comparison under a root-gated insertion. The recursion
allows fresh/reuse disagreement and unequal output lengths after the
first strict difference. Forest siblings restore the owner's entering
frame; numerical values are extended only while the output is equal.
-/
namespace BTnSSBMS.Encoder

structure RunFacts (state : State d) : Prop where
  ordered : FramesOrdered state
  dense : FramesDense state
  realized : FramesRealized state
  ancestral : FramesAncestral state

structure SavedFacts (state : State d) (frame : List Binding) : Prop where
  ordered : FrameOrdered frame
  dense : FrameDense frame
  realized : FrameRealized state frame
  zero : HasZero frame

theorem SavedFacts.extends {state next : State d} {frame : List Binding}
    (facts : SavedFacts state frame) (extended : state <+: next) : SavedFacts next frame :=
  ⟨facts.ordered, facts.dense, frameRealized_extends extended facts.realized, facts.zero⟩

theorem RunFacts.emit_facts {state : State d} (facts : RunFacts state)
    (u : Nat → Nat) (height tag : Nat) (frame : List Binding)
    (ordered : FrameOrdered frame) (dense : FrameDense frame)
    (realized : FrameRealized (emit state u height tag frame) frame)
    (ancestral : FrameAncestral (emit state u height tag frame) state.length frame) :
    RunFacts (emit state u height tag frame) :=
  ⟨framesOrdered_emit facts.ordered u height tag frame ordered,
   framesDense_emit facts.dense u height tag frame dense,
   framesRealized_emit facts.realized u height tag frame realized,
   framesAncestral_emit facts.ancestral u height tag frame ancestral⟩

theorem RunFacts.empty_emit {state : State d} (facts : RunFacts state)
    (u : Nat → Nat) (height tag : Nat) : RunFacts (emit state u height tag []) :=
  facts.emit_facts u height tag [] (by simp [FrameOrdered]) empty_frame_dense
    (empty_frame_realized _) (empty_frame_ancestral _ _)

theorem RunFacts.encode {state : State d} (facts : RunFacts state)
    (e : NumericalExpr) (source : ParentContext) (visible : List Nat)
    (positive : 0 < d) (coherent : Parents.Coherent d source)
    (valid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (good : VisibleGood state visible) (legal : Source.FiniteLegal d source e) :
    RunFacts (encode d (Parents.annotate d source e) visible state) := by
  have safe := encode_noFallback d (Parents.annotate d source e) visible state good
  exact ⟨encode_framesOrdered d _ visible state facts.ordered,
    encode_framesDense d _ visible state facts.ordered facts.dense safe,
    encode_framesRealized d _ visible state facts.realized,
    encode_framesAncestral d e source visible state positive coherent valid view
      legal.separated (legal.parented positive) facts.ordered facts.realized facts.ancestral safe⟩

theorem RunFacts.fresh_below {state : State d} (facts : RunFacts state)
    {visible : List Nat} (good : VisibleGood state visible) (a : ParentLabel) (key : Key)
    (fresh : equal (frameAt state (representative visible a (d - 1))) key = none) :
    SavedFacts state (smaller (frameAt state (representative visible a (d - 1))) key) := by
  have ordered := queried_frame_ordered facts.ordered (representative visible a (d - 1))
  exact ⟨smaller_ordered ordered key,
    frameDense_prefix (queried_frame_dense facts.dense _) (smaller_prefix ordered key),
    smaller_realized (queried_frame_realized facts.realized _) key,
    fresh_smaller_has_zero (queried_frame_has_zero state visible good a (d - 1)) key fresh⟩

theorem RunFacts.fresh_gate {state : State d} (facts : RunFacts state)
    {source : ParentContext} {visible : List Nat} (coordinates : List Nat) (hs : Forests (List Nat))
    (positive : 0 < d) (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (good : VisibleGood state visible)
    (parented : hs ≠ .nil → ∃ p, (Parents.label d source coordinates).parents[d - 1]?.join = some p)
    (fresh : equal (frameAt state (representative visible (Parents.label d source coordinates) (d - 1)))
      (queryKey d source coordinates hs) = none) :
    let key := queryKey d source coordinates hs
    let u := vector state visible (Parents.label d source coordinates)
    let below := smaller (frameAt state (representative visible (Parents.label d source coordinates) (d - 1))) key
    let c := (base below).height
    KeyGate d source coordinates visible state
      (emit (emit state u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 []) u c below := by
  dsimp only
  have fresh' : equal (frameAt state (representative visible (Parents.label d source coordinates) (d - 1)))
      (Keys.ofColumn d visible.length (Parents.label d source coordinates)
        (Parents.annotateForests d (source ++ [Parents.label d source coordinates]) hs)) = none := by
    simpa only [view.length, queryKey] using fresh
  obtain ⟨position, selected⟩ := fresh_has_representative state view coordinates hs parented fresh'
  have below := facts.fresh_below good (Parents.label d source coordinates) (queryKey d source coordinates hs) fresh
  obtain ⟨_, _, _, _, paths⟩ := fresh_head_result state coherent valid view facts.ordered facts.realized facts.ancestral
    coordinates (queryKey d source coordinates hs) positive position selected
    (by simpa only [← selected] using hasZero_nonempty below.zero)
  refine ⟨initial_numerical_gate state coherent valid view coordinates _, List.prefix_refl _, ?_⟩
  exact (show FrameAncestral
    (emit state (vector state visible (Parents.label d source coordinates))
      ((base (smaller (frameAt state (representative visible (Parents.label d source coordinates) (d - 1)))
        (queryKey d source coordinates hs))).height + 1) 1 []) state.length
    (smaller (frameAt state (representative visible (Parents.label d source coordinates) (d - 1)))
      (queryKey d source coordinates hs)) from by simpa only [← selected] using paths).extends (emit_extends ..)

private theorem comparison_width_append {d : Nat} {source : ParentContext} {coordinates : List Nat}
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
  theorem encode_rooted_comparison (root d : Nat) (e : NumericalExpr) (source target : ParentContext)
      (moved visible nextVisible owners : List Nat) (materials : List (Forests (List Nat)))
      (pool : List Key) (state next : State d) (positive : 0 < d)
      (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
      (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
      (targetUnit : Parents.UnitSteps d target)
      (view : Parents.NumericalView d source target moved)
      (oldView : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
      (newView : Parents.NumericalView d target (BMS.parentTable (d + 2) (matrix next)) nextVisible)
      (targetWidth : ∀ i, i < target.length → (target[i]?.getD default).coordinates.length = d)
      (known : VisibleMaterials d source visible owners materials state)
      (related : RootedFrames root d source target moved visible nextVisible materials pool state next)
      (legal : Source.FiniteLegal d source e) (facts : RunFacts state) (newFacts : RunFacts next)
      (good : VisibleGood state visible) (newGood : VisibleGood next nextVisible)
      (delta : Nat → Nat) (keyAmount : delta d = 2 * pool.length) (rootBefore : root < state.length)
      (values : ∀ j, j < d → RowRebaseValues j root (delta j) source.length moved visible nextVisible state next) :
      ShiftComparison root delta state next (encode d (Parents.annotate d source e) visible state)
        (encode d (Parents.annotate d target (Source.relocate d source target moved e)) nextVisible next) := by
    cases e with
    | nil => exact ShiftComparison.refl root delta state next
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
      let newC := (base newBelow).height
      let u := vector state visible a
      let v := vector next nextVisible newA
      have oldKey : Keys.ofColumn d visible.length a annotated = key := by rw [oldView.length]; rfl
      have newKeyEq : Keys.ofColumn d nextVisible.length newA newAnnotated = newKey := by rw [newView.length]; rfl
      have query : MaterialQuery d source coordinates visible owners materials state hs :=
        ⟨queried_frame_inheritedMaterials known oldView coordinates, sourceCoherent, sourceValid,
          oldView, legal.1, legal.2.1, legal.2.2.2.1⟩
      have newLegal := Source.relocate_finiteLegal d (.cons coordinates hs tail) source target moved
        sourceCoherent sourceValid targetCoherent targetValid targetUnit view positive legal
      have headLegal : Source.FiniteLegal d source (.cons coordinates hs .nil) :=
        ⟨legal.1, legal.2.1, legal.2.2.1, legal.2.2.2.1, trivial⟩
      have newHeadLegal : Source.FiniteLegal d target (.cons newCoordinates newHs .nil) :=
        ⟨newLegal.1, newLegal.2.1, newLegal.2.2.1, newLegal.2.2.2.1, trivial⟩
      have decision := related.query_column_alternative query positive rootBefore targetCoherent targetValid
        targetUnit view newView targetWidth facts.ordered facts.dense good facts.realized facts.ancestral
        newFacts.ordered newFacts.dense newGood delta keyAmount values
      change listCompare Ord.compare (row d v (firstHeight newFrame newKey) (freshBit newFrame newKey))
          (shiftedColumn (queryHead d a key visible state) root delta state.length) = .lt ∨
        (row d v (firstHeight newFrame newKey) (freshBit newFrame newKey) =
          shiftedColumn (queryHead d a key visible state) root delta state.length ∧
          (equal newFrame newKey = none ↔ equal frame key = none)) at decision
      have headCompared : ShiftComparison root delta state next headed newHeaded := by
        rcases decision with strict | ⟨same, branch⟩
        · have actual := queryHead_strict_continuations state next a newA key newKey visible nextVisible root delta
            (by simpa only [oldKey] using queryHead_prefix_encode d a annotated .nil visible state)
            (by simpa only [newKeyEq] using queryHead_prefix_encode d newA newAnnotated .nil nextVisible next) strict
          refine ⟨encode_extends .., encode_extends .., Or.inl ?_⟩
          rw [shiftedOutput_eq_copy _ _ _ _ _ (Nat.le_refl _)]
          exact actual
        · by_cases fresh : equal frame key = none
          · have newFresh : equal newFrame newKey = none := branch.mpr fresh
            let first := emit state u (c + 1) 1 []
            let newFirst := emit next v (newC + 1) 1 []
            let guarded := emit first (fun j => u j + 1) (c + 2) 2 []
            let newGuarded := emit newFirst (fun j => v j + 1) (newC + 2) 2 []
            let forests := encodeForests d annotated visible u c below guarded
            let newForests := encodeForests d newAnnotated nextVisible v newC newBelow newGuarded
            have freshLookup : equal (frameAt state (representative visible a (d - 1))) key = none := fresh
            have firstSame : row d v (newC + 1) 1 = shiftedColumn first root delta state.length := by
              simpa only [queryHead, firstHeight, freshBit, fresh, newFresh, freshLookup, Option.isSome_none,
                Bool.false_eq_true, if_false] using same
            have shift := FreshShift.of_first_column firstSame
            have oldGate := facts.fresh_gate coordinates hs positive sourceCoherent sourceValid oldView good
              (headLegal.parented positive).1 fresh
            have newGate := newFacts.fresh_gate newCoordinates newHs positive targetCoherent targetValid newView newGood
              (newHeadLegal.parented positive).1 newFresh
            obtain ⟨splice⟩ := related.queried oldView newView view sourceCoherent sourceValid
              targetCoherent targetValid positive coordinates
            have belowRelated := splice.filtered key newKey
              (query.relocation_comparisons targetCoherent targetValid targetUnit view targetWidth positive)
            have initialCompared := (ShiftComparison.emit_equal state next u v (c + 1) 1 (newC + 1) 1
              [] [] root delta firstSame).trans
              (ShiftComparison.emit_equal first newFirst (fun j => u j + 1) (fun j => v j + 1)
                (c + 2) 2 (newC + 2) 2 [] [] root delta (by
                  simpa only [first, emit_length] using shift.guard positive (Nat.le_of_lt rootBefore)))
            have forestCompared := encodeForests_rooted_comparison root d hs source target coordinates moved visible
              nextVisible owners materials hs pool state next guarded newGuarded u v c newC below newBelow
              positive sourceCoherent sourceValid targetCoherent targetValid targetUnit view oldView newView targetWidth
              known related oldGate newGate (smaller_inheritedMaterials query.inherited key) belowRelated
              (facts.fresh_below good a key fresh) (newFacts.fresh_below newGood newA newKey newFresh)
              ((facts.empty_emit u (c + 1) 1).empty_emit (fun j => u j + 1) (c + 2) 2)
              ((newFacts.empty_emit v (newC + 1) 1).empty_emit (fun j => v j + 1) (newC + 2) 2)
              good newGood legal.1 legal.2.1 legal.2.2.2.1 legal.2.2.2.1 delta keyAmount rootBefore values shift
            have finalGate := oldGate.encodeForests hs positive sourceCoherent sourceValid oldView legal.2.2.2.1.separated
            let finalFrame := below ++ [⟨key, c + 2, some forests.length, some state.length⟩]
            let newFinalFrame := newBelow ++ [⟨newKey, newC + 2, some newForests.length, some next.length⟩]
            have closingCompared := ShiftComparison.emit_equal forests newForests (fun j => u j + 1) (fun j => v j + 1)
              (c + 2) 0 (newC + 2) 0 finalFrame newFinalFrame root delta
              (shift.closing finalGate positive (Nat.le_of_lt rootBefore) finalFrame)
            have result := (initialCompared.trans forestCompared).trans closingCompared
            dsimp only [frame, key, newFrame, newKey, queryKey, a, newA, newCoordinates, newHs] at fresh newFresh
            dsimp only [headed, newHeaded, annotated, newAnnotated, a, newA, newCoordinates, newHs]
            simp only [headState, encode, oldView.length, newView.length, fresh, newFresh]
            exact result
          · exact headState_comparison_of_query_decision state next a newA annotated newAnnotated visible nextVisible
              root delta (Or.inl (by rwa [oldKey])) (by simpa only [oldKey, newKeyEq] using Or.inr ⟨same, branch⟩)
      have oldTailPrefix : headed <+: encode d (Parents.annotate d source (.cons coordinates hs tail)) visible state := by
        rw [Parents.annotate, encode_split_head]
        exact encode_extends ..
      have newTailPrefix : newHeaded <+: encode d (Parents.annotate d target
          (Source.relocate d source target moved (.cons coordinates hs tail))) nextVisible next := by
        rw [Source.relocate, Parents.annotate, encode_split_head]
        exact encode_extends ..
      rcases headCompared.comparison with strict | equalOutput
      · exact ⟨headCompared.oldPrefix.trans oldTailPrefix, headCompared.newPrefix.trans newTailPrefix,
          Or.inl (shifted_strict_extends headCompared.oldPrefix headCompared.newPrefix oldTailPrefix newTailPrefix strict)⟩
      · have headNonempty : state.length < headed.length := by
          have before := headState_first_before_last d a annotated visible state
          have nonempty := headState_nonempty d a annotated visible state
          change state.length ≤ headed.length - 1 at before
          change 0 < headed.length at nonempty
          omega
        have finalValues (j : Nat) (room : j < d) :
            RowRebaseValues j root (delta j) (source.length + 1) (moved ++ [target.length])
              (visible ++ [headed.length - 1]) (nextVisible ++ [newHeaded.length - 1]) headed newHeaded := by
          have trace := equal_shiftedOutput_row_trace headCompared.oldPrefix headCompared.newPrefix equalOutput j (by omega)
          have oldValues := (values j room).extends
            (fun p inside => by simpa only [table_length] using oldView.bounded p inside)
            (fun p inside => by simpa only [table_length] using newView.bounded _ (view.bounded p inside))
            headCompared.oldPrefix headCompared.newPrefix
          have result := oldValues.append view.length oldView.length
            (fun p inside => by rw [newView.length]; exact view.bounded p inside)
            (headed.length - 1) (newHeaded.length - 1) (trace.last headNonempty)
          simpa only [newView.length] using result
        have nextFacts := facts.encode (.cons coordinates hs .nil) source visible positive sourceCoherent sourceValid
          oldView good headLegal
        have nextNewFacts := newFacts.encode (.cons newCoordinates newHs .nil) target nextVisible positive targetCoherent
          targetValid newView newGood newHeadLegal
        have tailCompared := encode_rooted_comparison root d tail (source ++ [a]) (target ++ [newA])
          (moved ++ [target.length]) (visible ++ [headed.length - 1]) (nextVisible ++ [newHeaded.length - 1])
          owners (materials ++ [hs]) pool headed newHeaded positive
          (Parents.coherent_append_label sourceCoherent coordinates)
          (Parents.context_valid_append_label d source sourceValid coordinates)
          (Parents.coherent_append_label targetCoherent newCoordinates)
          (Parents.context_valid_append_label d target targetValid newCoordinates)
          (Source.relocationHead_unitSteps sourceCoherent sourceValid targetCoherent targetValid targetUnit view coordinates)
          (Source.relocation_view_append sourceCoherent sourceValid targetCoherent targetValid view coordinates)
          (headState_view state positive sourceCoherent sourceValid oldView coordinates hs legal.2.2.2.1.separated)
          (headState_view next positive targetCoherent targetValid newView newCoordinates newHs newLegal.2.2.2.1.separated)
          (comparison_width_append targetWidth (Source.relocationHead_width d source target moved coordinates))
          (headState_materials known oldView coordinates hs legal.1 legal.2.2.2.1)
          (related.head known query newView targetCoherent targetValid targetUnit view targetWidth positive)
          legal.2.2.2.2 nextFacts nextNewFacts
          (headState_good d a annotated visible state good) (headState_good d newA newAnnotated nextVisible next newGood)
          delta keyAmount (by omega)
          (by simpa only [List.length_append, List.length_cons, List.length_nil] using finalValues)
        simpa only [Parents.annotate, Source.relocate, encode_split_head] using headCompared.trans tailCompared

  theorem encodeForests_rooted_comparison (root d : Nat) (hs : Forests (List Nat)) (source target : ParentContext)
      (coordinates moved visible nextVisible owners : List Nat) (materials : List (Forests (List Nat)))
      (ownerMaterial : Forests (List Nat)) (pool : List Key) (original newOriginal state next : State d)
      (u v : Nat → Nat) (c newC : Nat) (below newBelow : List Binding)
      (positive : 0 < d) (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
      (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
      (targetUnit : Parents.UnitSteps d target) (view : Parents.NumericalView d source target moved)
      (oldView : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix original)) visible)
      (newView : Parents.NumericalView d target (BMS.parentTable (d + 2) (matrix newOriginal)) nextVisible)
      (targetWidth : ∀ i, i < target.length → (target[i]?.getD default).coordinates.length = d)
      (known : VisibleMaterials d source visible owners materials original)
      (related : RootedFrames root d source target moved visible nextVisible materials pool original newOriginal)
      (scope : KeyGate d source coordinates visible original state u c below)
      (newScope : KeyGate d target (Source.relocationHead d source target moved coordinates)
        nextVisible newOriginal next v newC newBelow)
      (inherited : InheritedMaterials d source coordinates visible owners materials below)
      (belowRelated : RootedInsertion root (fun b => (rekeyBinding d source target visible moved materials b).key)
        below newBelow pool)
      (belowFacts : SavedFacts original below) (newBelowFacts : SavedFacts newOriginal newBelow)
      (facts : RunFacts state) (newFacts : RunFacts next)
      (good : VisibleGood original visible) (newGood : VisibleGood newOriginal nextVisible)
      (width : coordinates.length = d)
      (unit : Parents.UnitSteps d (source ++ [Parents.label d source coordinates]))
      (ownerLegal : Source.FiniteLegalForests d (source ++ [Parents.label d source coordinates]) (coordinates[0]?.getD 0) ownerMaterial)
      (legal : Source.FiniteLegalForests d (source ++ [Parents.label d source coordinates]) (coordinates[0]?.getD 0) hs)
      (delta : Nat → Nat) (keyAmount : delta d = 2 * pool.length) (rootBefore : root < original.length)
      (values : ∀ j, j < d → RowRebaseValues j root (delta j) source.length moved visible nextVisible original newOriginal)
      (shift : FreshShift original u v c newC root delta) :
      let a := Parents.label d source coordinates
      let newCoordinates := Source.relocationHead d source target moved coordinates
      let newA := Parents.label d target newCoordinates
      ShiftComparison root delta state next
        (encodeForests d (Parents.annotateForests d (source ++ [a]) hs) visible u c below state)
        (encodeForests d (Parents.annotateForests d (target ++ [newA])
          (Source.relocateForests d (source ++ [a]) (target ++ [newA]) (moved ++ [target.length]) hs)) nextVisible v newC newBelow next) := by
    cases hs with
    | nil => exact ShiftComparison.refl root delta state next
    | cons h hs =>
      let a := Parents.label d source coordinates
      let newCoordinates := Source.relocationHead d source target moved coordinates
      let newA := Parents.label d target newCoordinates
      let newH := Source.relocate d (source ++ [a]) (target ++ [newA]) (moved ++ [target.length]) h
      let withSlot := emit state (fun j => u j + 2) (c + 2) 0 below
      let newSlot := emit next (fun j => v j + 2) (newC + 2) 0 newBelow
      let withForest := encode d (Parents.annotate d (source ++ [a]) h) (visible ++ [state.length]) withSlot
      let newForest := encode d (Parents.annotate d (target ++ [newA]) newH) (nextVisible ++ [next.length]) newSlot
      have sourceCoherent' := Parents.coherent_append_label sourceCoherent coordinates
      have sourceValid' := Parents.context_valid_append_label d source sourceValid coordinates
      have targetCoherent' := Parents.coherent_append_label targetCoherent newCoordinates
      have targetValid' := Parents.context_valid_append_label d target targetValid newCoordinates
      have view' := Source.relocation_view_append sourceCoherent sourceValid targetCoherent targetValid view coordinates
      have targetUnit' := Source.relocationHead_unitSteps sourceCoherent sourceValid targetCoherent targetValid targetUnit view coordinates
      have width' := comparison_width_append targetWidth (Source.relocationHead_width d source target moved coordinates)
      have slotView := scope.numerical.slot_view sourceValid oldView (c + 2) below
      have newSlotView := newScope.numerical.slot_view targetValid newView (newC + 2) newBelow
      have slotKnown := (known.extends scope.numerical.extended).inherit_slot inherited ownerMaterial width ownerLegal
        (fun j => u j + 2) (c + 2)
      have slotRelated := (related.extends scope.numerical.extended newScope.numerical.extended).append_emit
        (known.extends scope.numerical.extended) oldView view newView.length a newA ownerMaterial
        (fun j => u j + 2) (fun j => v j + 2) (c + 2) (newC + 2) below newBelow
        (belowRelated.congr (fun b member => congrArg Binding.key
          (rekeyBinding_prefix oldView view known.materialContext.length
            (List.prefix_append source [a]) (List.prefix_append target [newA])
            (List.prefix_append visible [state.length]) (List.prefix_append moved [target.length])
            (List.prefix_append materials [ownerMaterial]) b (inherited.keys b member))))
      have slotSame := shift.slot scope positive (Nat.le_of_lt rootBefore)
      have slotCompared := ShiftComparison.emit_equal state next (fun j => u j + 2) (fun j => v j + 2)
        (c + 2) 0 (newC + 2) 0 below newBelow root delta slotSame
      have slotValues (j : Nat) (room : j < d) :
          RowRebaseValues j root (delta j) (source.length + 1) (moved ++ [target.length])
            (visible ++ [state.length]) (nextVisible ++ [next.length]) withSlot newSlot := by
        have oldValues := (values j room).extends (result := withSlot) (newResult := newSlot)
          (fun p inside => by simpa only [table_length] using oldView.bounded p inside)
          (fun p inside => by simpa only [table_length] using newView.bounded _ (view.bounded p inside))
          (scope.numerical.extended.trans (emit_extends ..)) (newScope.numerical.extended.trans (emit_extends ..))
        have value := congrArg (fun col : List Nat => col[j]?.getD 0) slotSame
        rw [shiftedColumn_emit, row_numerical_reading d _ _ _ j room, row_numerical_reading d _ _ _ j room] at value
        have result := oldValues.append view.length oldView.length
          (fun p inside => by rw [newView.length]; exact view.bounded p inside) state.length next.length (by
            change Parents.reading (BMS.parentTable (d + 2) (matrix newSlot)) j next.length =
              Parents.reading (BMS.parentTable (d + 2) (matrix withSlot)) j state.length +
                rowBump withSlot j root (delta j) state.length
            rw [emitted_numerical_value next _ _ _ _ j room, emitted_numerical_value state _ _ _ _ j room]
            exact value)
        simpa only [newView.length] using result
      have slotFacts := facts.emit_facts (fun j => u j + 2) (c + 2) 0 below belowFacts.ordered belowFacts.dense
        (frameRealized_extends (scope.numerical.extended.trans (emit_extends ..)) belowFacts.realized)
        (scope.slot_ancestral positive)
      have newSlotFacts := newFacts.emit_facts (fun j => v j + 2) (newC + 2) 0 newBelow newBelowFacts.ordered newBelowFacts.dense
        (frameRealized_extends (newScope.numerical.extended.trans (emit_extends ..)) newBelowFacts.realized)
        (newScope.slot_ancestral positive)
      have slotGood := visibleGood_emit state visible (visibleGood_extends scope.numerical.extended good)
        (fun j => u j + 2) (c + 2) 0 below belowFacts.zero
      have newSlotGood := visibleGood_emit next nextVisible (visibleGood_extends newScope.numerical.extended newGood)
        (fun j => v j + 2) (newC + 2) 0 newBelow newBelowFacts.zero
      have forestCompared := encode_rooted_comparison root d h (source ++ [a]) (target ++ [newA])
        (moved ++ [target.length]) (visible ++ [state.length]) (nextVisible ++ [next.length]) (owners ++ [source.length])
        (materials ++ [ownerMaterial]) pool withSlot newSlot positive sourceCoherent' sourceValid' targetCoherent' targetValid'
        targetUnit' view' slotView newSlotView width' slotKnown slotRelated legal.2.1 slotFacts newSlotFacts slotGood newSlotGood
        delta keyAmount (by have := scope.numerical.extended.length_le; dsimp only [withSlot]; rw [emit_length]; omega)
        (by simpa only [List.length_append, List.length_cons, List.length_nil] using slotValues)
      obtain ⟨finalVisible, extended, forestView⟩ := encode_numerical_view d h (source ++ [a])
        (visible ++ [state.length]) withSlot positive sourceCoherent' sourceValid' slotView legal.2.1.separated
      have nextScope := scope.after_forest positive sourceCoherent sourceValid oldView.length (Source.labels h)
        (encode_extends ..) extended legal.1 forestView
      have newLegal := Source.relocateForests_finiteLegal d (.cons h hs) (source ++ [a]) (target ++ [newA]) (moved ++ [target.length])
        sourceCoherent' sourceValid' targetCoherent' targetValid' targetUnit' view' positive source.length
        (by simp) (by simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_sub_cancel]; exact .refl _)
        (by simpa only [a, Parents.reading_append_label] using legal)
      simp only [← view.length, Parents.point_append_last, newA, Parents.reading_append_label] at newLegal
      obtain ⟨finalNewVisible, newExtended, newForestView⟩ := encode_numerical_view d newH (target ++ [newA])
        (nextVisible ++ [next.length]) newSlot positive targetCoherent' targetValid' newSlotView newLegal.2.1.separated
      have nextNewScope := newScope.after_forest positive targetCoherent targetValid newView.length (Source.labels newH)
        (encode_extends ..) newExtended newLegal.1 newForestView
      have tailCompared := encodeForests_rooted_comparison root d hs source target coordinates moved visible nextVisible owners
        materials ownerMaterial pool original newOriginal withForest newForest u v c newC below newBelow positive
        sourceCoherent sourceValid targetCoherent targetValid targetUnit view oldView newView targetWidth known related
        nextScope nextNewScope inherited belowRelated belowFacts newBelowFacts
        (slotFacts.encode h (source ++ [a]) (visible ++ [state.length]) positive sourceCoherent' sourceValid' slotView slotGood legal.2.1)
        (newSlotFacts.encode newH (target ++ [newA]) (nextVisible ++ [next.length]) positive targetCoherent' targetValid'
          newSlotView newSlotGood newLegal.2.1)
        good newGood width unit ownerLegal legal.2.2 delta keyAmount rootBefore values shift
      exact (slotCompared.trans forestCompared).trans tailCompared
end

end BTnSSBMS.Encoder
