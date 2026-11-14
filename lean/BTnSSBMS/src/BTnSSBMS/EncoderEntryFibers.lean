import BTnSSBMS.VisibleEntryFibers

/-!
Every visible source position in the entire actual execution has its
original snapshot and a numerical fiber containing no other source
head. All history entries are sound by the independently proved trace
soundness theorem; no recursive inverse-ancestry assumption is used.
-/
namespace BTnSSBMS.Encoder

mutual
  theorem entries_fibers (d : Nat) (e : NumericalExpr) (source : ParentContext)
      (visible owners : List Nat) (materials : List (Forests (List Nat))) (state : State d)
      (history : List (Entry d)) (positive : 0 < d)
      (soundHistory : ∀ entry ∈ history, entry.Sound)
      (known : VisibleEntryFibers d source visible owners materials state history)
      (included : ∀ entry ∈ entries d e source visible owners materials state, entry ∈ history) :
      ∀ entry ∈ entries d e source visible owners materials state,
        VisibleEntryFibers d entry.source entry.visible entry.owners entry.materials entry.state history := by
    cases e with
    | nil => intro entry member; simp only [entries, List.not_mem_nil] at member
    | cons coordinates hs tail =>
      let current : Entry d := ⟨source, coordinates, hs, tail, visible, owners, materials, state⟩
      let a := Parents.label d source coordinates
      let annotated := Parents.annotateForests d (source ++ [a]) hs
      let key := Keys.ofColumn d visible.length a annotated
      let frame := frameAt state (representative visible a (d - 1))
      let below := smaller frame key
      let c := (base below).height
      let u := vector state visible a
      let headed := headState d a annotated visible state
      let guarded := emit (emit state u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 []
      have currentMember : current ∈ history := included current (List.mem_cons_self)
      have currentSound := soundHistory current currentMember
      have headPrefix : state <+: headed := encode_extends ..
      have headFiber : NumericalFiber headed state.length (headed.length - 1) :=
        headState_fiber state positive currentSound.coherent currentSound.valid currentSound.view
          coordinates hs currentSound.legal.2.2.2.1.separated
      have headedKnown : VisibleEntryFibers d (source ++ [a]) (visible ++ [headed.length - 1]) owners
          (materials ++ [hs]) headed history :=
        (known.extends headPrefix).append_entry current currentMember rfl rfl rfl
          (List.prefix_refl _) (List.prefix_refl _) headPrefix (headed.length - 1)
          (headState_first_before_last d a annotated visible state) headFiber
          (headState_last_readout d a annotated visible state)
      have tailIncluded : ∀ entry ∈ entries d tail (source ++ [a]) (visible ++ [headed.length - 1])
          owners (materials ++ [hs]) headed, entry ∈ history := by
        intro entry member
        apply included entry
        simp only [entries, List.mem_cons, List.mem_append]
        exact .inr (.inr member)
      have tailFibers := entries_fibers d tail (source ++ [a]) (visible ++ [headed.length - 1])
        owners (materials ++ [hs]) headed history positive soundHistory headedKnown tailIncluded
      have innerFibers : ∀ entry ∈ (match equal frame key with
          | some _ => []
          | none => forestEntries d hs source coordinates visible owners materials hs u c below guarded),
          VisibleEntryFibers d entry.source entry.visible entry.owners entry.materials entry.state history := by
        cases found : equal frame key with
        | some bound => intro entry member; simp only [List.not_mem_nil] at member
        | none =>
          have guardPrefix : state <+: guarded := (emit_extends ..).trans (emit_extends ..)
          apply forestEntries_fibers d hs current u c below guarded history positive soundHistory
            (known.extends guardPrefix) currentMember
            (initial_numerical_gate state currentSound.coherent currentSound.valid currentSound.view coordinates c)
            (List.prefix_refl _) currentSound.legal.2.2.2.1
          intro entry member
          apply included entry
          dsimp only [frame, key, a, annotated] at found
          simp only [entries, found, List.mem_cons, List.mem_append]
          exact .inr (.inl member)
      intro entry member
      simp only [entries, List.mem_cons, List.mem_append] at member
      rcases member with rfl | inner | later
      · exact known
      · exact innerFibers entry inner
      · exact tailFibers entry later

  theorem forestEntries_fibers (d : Nat) (hs : Forests (List Nat)) (owner : Entry d)
      (u : Nat → Nat) (c : Nat) (below : List Binding) (state : State d) (history : List (Entry d))
      (positive : 0 < d) (soundHistory : ∀ entry ∈ history, entry.Sound)
      (known : VisibleEntryFibers d owner.source owner.visible owner.owners owner.materials state history)
      (ownerMember : owner ∈ history)
      (scope : NumericalGate d owner.source owner.coordinates owner.visible owner.state state u (owner.state.length + 1))
      (guardedPrefix : emit (emit owner.state u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 [] <+: state)
      (legal : Source.FiniteLegalForests d (owner.source ++ [Parents.label d owner.source owner.coordinates])
        (owner.coordinates[0]?.getD 0) hs)
      (included : ∀ entry ∈ forestEntries d hs owner.source owner.coordinates owner.visible owner.owners
        owner.materials owner.attachments u c below state, entry ∈ history) :
      ∀ entry ∈ forestEntries d hs owner.source owner.coordinates owner.visible owner.owners
          owner.materials owner.attachments u c below state,
        VisibleEntryFibers d entry.source entry.visible entry.owners entry.materials entry.state history := by
    cases hs with
    | nil => intro entry member; simp only [forestEntries, List.not_mem_nil] at member
    | cons h hs =>
      let a := Parents.label d owner.source owner.coordinates
      let withSlot := emit state (fun j => u j + 2) (c + 2) 0 below
      let withForest := encode d (Parents.annotate d (owner.source ++ [a]) h)
        (owner.visible ++ [state.length]) withSlot
      have ownerSound := soundHistory owner ownerMember
      have guardOutput : Readout state (owner.state.length + 1) (c + 2) 2 :=
        readout_extends guardedPrefix
          (by simpa only [emit_length] using
            (readout_emit (emit owner.state u (c + 1) 1 [])
              (fun j => u j + 1) (c + 2) 2 []))
      have slotFiber : NumericalFiber withSlot owner.state.length state.length :=
        scope.slot_fiber ((initial_guard_fiber owner.state u c).extends guardedPrefix) guardOutput (c + 2) below
      have slotKnown : VisibleEntryFibers d (owner.source ++ [a]) (owner.visible ++ [state.length])
          (owner.owners ++ [owner.source.length]) (owner.materials ++ [owner.attachments]) withSlot history :=
        (known.extends (emit_extends ..)).append_entry owner ownerMember rfl rfl rfl
          (List.prefix_append _ _) (List.prefix_append _ _) (scope.extended.trans (emit_extends ..))
          state.length scope.extended.length_le slotFiber ⟨c + 2, readout_emit ..⟩
      have innerIncluded : ∀ entry ∈ entries d h (owner.source ++ [a]) (owner.visible ++ [state.length])
          (owner.owners ++ [owner.source.length]) (owner.materials ++ [owner.attachments]) withSlot,
          entry ∈ history := by
        intro entry member
        exact included entry (List.mem_append_left _ member)
      have innerFibers := entries_fibers d h (owner.source ++ [a]) (owner.visible ++ [state.length])
        (owner.owners ++ [owner.source.length]) (owner.materials ++ [owner.attachments]) withSlot history
        positive soundHistory slotKnown innerIncluded
      have nextCoherent := Parents.coherent_append_label ownerSound.coherent owner.coordinates
      have nextValid := Parents.context_valid_append_label d owner.source ownerSound.valid owner.coordinates
      have slotView := scope.slot_view ownerSound.valid ownerSound.view (c + 2) below
      obtain ⟨finalVisible, extended, forestView⟩ := encode_numerical_view d h (owner.source ++ [a])
        (owner.visible ++ [state.length]) withSlot positive nextCoherent nextValid slotView legal.2.1.separated
      have nextScope := scope.after_forest positive ownerSound.coherent ownerSound.valid ownerSound.view.length
        (c + 2) below (Source.labels h) (encode_extends d _ _ _) extended legal.1 forestView
      have forestPrefix : state <+: withForest := (emit_extends ..).trans (encode_extends ..)
      have tailIncluded : ∀ entry ∈ forestEntries d hs owner.source owner.coordinates owner.visible owner.owners
          owner.materials owner.attachments u c below withForest, entry ∈ history := by
        intro entry member
        exact included entry (List.mem_append_right _ member)
      have tailFibers := forestEntries_fibers d hs owner u c below withForest history positive soundHistory
        (known.extends forestPrefix) ownerMember nextScope (guardedPrefix.trans forestPrefix) legal.2.2 tailIncluded
      intro entry member
      simp only [forestEntries, List.mem_append] at member
      rcases member with inner | later
      · exact innerFibers entry inner
      · exact tailFibers entry later
end

theorem source_entries_fibers (d : Nat) (e : NumericalExpr) (positive : 0 < d)
    (legal : Source.FiniteLegal d [] e) :
    ∀ entry ∈ entries d e [] [] [] [] [],
      VisibleEntryFibers d entry.source entry.visible entry.owners entry.materials entry.state
        (entries d e [] [] [] [] []) :=
  entries_fibers d e [] [] [] [] [] (entries d e [] [] [] [] []) positive
    (source_entries_sound d e positive legal) (empty_visibleEntryFibers d [] _) (fun _ member => member)

theorem standard_entries_fibers {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) :
    ∀ entry ∈ entries d e [] [] [] [] [],
      VisibleEntryFibers d entry.source entry.visible entry.owners entry.materials entry.state
        (entries d e [] [] [] [] []) :=
  source_entries_fibers d e positive (Source.standard_finiteLegal positive standard)

end BTnSSBMS.Encoder
