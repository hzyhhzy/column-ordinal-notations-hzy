import BTnSSBMS.EncoderEntries

/-!
Every recorded actual entry carries the full finite legality of its
remaining lexical input, the real numerical view, and all saved original
materials. This quantifies over the entire trace, not bounded samples.
-/
namespace BTnSSBMS.Encoder

mutual
  theorem entries_sound (d : Nat) (e : NumericalExpr) (source : ParentContext)
      (visible owners : List Nat) (materials : List (Forests (List Nat))) (state : State d)
      (positive : 0 < d) (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
      (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
      (known : VisibleMaterials d source visible owners materials state)
      (legal : Source.FiniteLegal d source e) :
      ∀ entry ∈ entries d e source visible owners materials state, entry.Sound := by
    cases e with
    | nil => intro entry member; simp only [entries, List.not_mem_nil] at member
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
      have innerSound : ∀ entry ∈ (match equal frame key with
          | some _ => []
          | none => forestEntries d hs source coordinates visible owners materials hs u c below guarded),
          entry.Sound := by
        cases found : equal frame key with
        | some bound => intro entry member; simp only [List.not_mem_nil] at member
        | none =>
          exact forestEntries_sound d hs source coordinates visible owners materials hs state guarded u
            (state.length + 1) c below positive coherent valid view known
            (initial_numerical_gate state coherent valid view coordinates c)
            (smaller_inheritedMaterials (queried_frame_inheritedMaterials known view coordinates) key)
            legal.1 legal.2.2.2.1 legal.2.2.2.1
      have tailSound := entries_sound d tail (source ++ [a]) (visible ++ [headed.length - 1]) owners
        (materials ++ [hs]) headed positive (Parents.coherent_append_label coherent coordinates)
        (Parents.context_valid_append_label d source valid coordinates)
        (headState_view state positive coherent valid view coordinates hs legal.2.2.2.1.separated)
        (headState_materials known view coordinates hs legal.1 legal.2.2.2.1) legal.2.2.2.2
      intro entry member
      simp only [entries, List.mem_cons, List.mem_append] at member
      rcases member with rfl | inner | later
      · exact ⟨coherent, valid, view, known, legal⟩
      · exact innerSound entry inner
      · exact tailSound entry later

  theorem forestEntries_sound (d : Nat) (hs : Forests (List Nat)) (source : ParentContext)
      (coordinates visible owners : List Nat) (materials : List (Forests (List Nat)))
      (ownerMaterial : Forests (List Nat)) (original state : State d) (u : Nat → Nat)
      (gate c : Nat) (below : List Binding) (positive : 0 < d)
      (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
      (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix original)) visible)
      (known : VisibleMaterials d source visible owners materials original)
      (scope : NumericalGate d source coordinates visible original state u gate)
      (inherited : InheritedMaterials d source coordinates visible owners materials below)
      (width : coordinates.length = d)
      (ownerLegal : Source.FiniteLegalForests d (source ++ [Parents.label d source coordinates])
        (coordinates[0]?.getD 0) ownerMaterial)
      (legal : Source.FiniteLegalForests d (source ++ [Parents.label d source coordinates])
        (coordinates[0]?.getD 0) hs) :
      ∀ entry ∈ forestEntries d hs source coordinates visible owners materials ownerMaterial u c below state,
        entry.Sound := by
    cases hs with
    | nil => intro entry member; simp only [forestEntries, List.not_mem_nil] at member
    | cons h hs =>
      let a := Parents.label d source coordinates
      let withSlot := emit state (fun j => u j + 2) (c + 2) 0 below
      let withForest := encode d (Parents.annotate d (source ++ [a]) h) (visible ++ [state.length]) withSlot
      have nextCoherent := Parents.coherent_append_label coherent coordinates
      have nextValid := Parents.context_valid_append_label d source valid coordinates
      have slotView := scope.slot_view valid view (c + 2) below
      have slotMaterials := (known.extends scope.extended).inherit_slot inherited ownerMaterial width ownerLegal
        (fun j => u j + 2) (c + 2)
      have innerSound := entries_sound d h (source ++ [a]) (visible ++ [state.length])
        (owners ++ [source.length]) (materials ++ [ownerMaterial]) withSlot positive nextCoherent nextValid
        slotView slotMaterials legal.2.1
      obtain ⟨finalVisible, extended, forestView⟩ := encode_numerical_view d h (source ++ [a])
        (visible ++ [state.length]) withSlot positive nextCoherent nextValid slotView legal.2.1.separated
      have nextScope := scope.after_forest positive coherent valid view.length (c + 2) below
        (Source.labels h) (encode_extends d _ _ _) extended legal.1 forestView
      have tailSound := forestEntries_sound d hs source coordinates visible owners materials ownerMaterial
        original withForest u gate c below positive coherent valid view known nextScope inherited width ownerLegal legal.2.2
      intro entry member
      simp only [forestEntries, List.mem_append] at member
      rcases member with inner | later
      · exact innerSound entry inner
      · exact tailSound entry later
end

theorem source_entries_sound (d : Nat) (e : NumericalExpr) (positive : 0 < d)
    (legal : Source.FiniteLegal d [] e) :
    ∀ entry ∈ entries d e [] [] [] [] [], entry.Sound :=
  entries_sound d e [] [] [] [] [] positive (Parents.empty_coherent d) Parents.empty_context_valid
    (Parents.empty_numerical_view d) (empty_visibleMaterials d) legal

theorem standard_entries_sound {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) :
    ∀ entry ∈ entries d e [] [] [] [] [], entry.Sound :=
  source_entries_sound d e positive (Source.standard_finiteLegal positive standard)

/-- Every first-output position identified by the exhaustive numerical
classification has a real source-entry snapshot with full finite data. -/
theorem standard_head_entry {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {p : Nat}
    (member : p ∈ headPositions d (Parents.annotate d [] e) [] []) :
    ∃ entry, entry ∈ entries d e [] [] [] [] [] ∧ entry.state.length = p ∧ entry.Sound := by
  rw [← entries_positions d e [] [] [] [] []] at member
  obtain ⟨entry, found, position⟩ := List.mem_map.mp member
  exact ⟨entry, found, position, standard_entries_sound positive standard entry found⟩

end BTnSSBMS.Encoder
