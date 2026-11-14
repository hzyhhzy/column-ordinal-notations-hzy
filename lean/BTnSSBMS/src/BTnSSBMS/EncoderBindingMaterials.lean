import BTnSSBMS.BindingMaterials

/-!
Attachment provenance at every query of the actual recursive encoder.
The proof-side material context contains original numerical forests, not
keys chosen to satisfy a later comparison. Each open owner contributes
its whole list, and sibling forests restart from that same owner entry.
-/
namespace BTnSSBMS.Source

def outerMaterials : NumericalExpr → List (Forests (List Nat))
  | .nil => []
  | .cons _ hs tail => hs :: outerMaterials tail

end BTnSSBMS.Source

namespace BTnSSBMS.Encoder

/-- The actual numerical entry and current attachment accompany the
saved-payload certificate at every read. Later transport lemmas therefore
need not assume these conditions separately for unobserved inner reads. -/
structure MaterialQuery (d : Nat) (source : ParentContext) (coordinates visible owners : List Nat)
    (materials : List (Forests (List Nat))) (state : State d) (hs : Forests (List Nat)) : Prop where
  inherited : InheritedMaterials d source coordinates visible owners materials
    (frameAt state (representative visible (Parents.label d source coordinates) (d - 1)))
  coherent : Parents.Coherent d source
  valid : Parents.ContextValid source
  view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible
  width : coordinates.length = d
  unit : Parents.UnitSteps d (source ++ [Parents.label d source coordinates])
  legal : Source.FiniteLegalForests d (source ++ [Parents.label d source coordinates])
    (coordinates[0]?.getD 0) hs

mutual
  def ReadsMaterials (d : Nat) (e : NumericalExpr) (source : ParentContext)
      (visible owners : List Nat) (materials : List (Forests (List Nat))) (state : State d) : Prop :=
    match e with
    | .nil => True
    | .cons coordinates hs tail =>
      let a := Parents.label d source coordinates
      let annotated := Parents.annotateForests d (source ++ [a]) hs
      let key := Keys.ofColumn d visible.length a annotated
      let frame := frameAt state (representative visible a (d - 1))
      let below := smaller frame key
      let c := (base below).height
      let u := vector state visible a
      let headed := headState d a annotated visible state
      MaterialQuery d source coordinates visible owners materials state hs ∧
        (match equal frame key with
        | some _ => True
        | none => ReadsMaterialsForests d hs source coordinates visible owners materials hs u c below
            (emit (emit state u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 [])) ∧
        ReadsMaterials d tail (source ++ [a]) (visible ++ [headed.length - 1]) owners
          (materials ++ [hs]) headed

  def ReadsMaterialsForests (d : Nat) (hs : Forests (List Nat)) (source : ParentContext)
      (coordinates visible owners : List Nat) (materials : List (Forests (List Nat)))
      (ownerMaterial : Forests (List Nat)) (u : Nat → Nat) (c : Nat)
      (below : List Binding) (state : State d) : Prop :=
    match hs with
    | .nil => True
    | .cons h hs =>
      let a := Parents.label d source coordinates
      let withSlot := emit state (fun j => u j + 2) (c + 2) 0 below
      let withForest := encode d (Parents.annotate d (source ++ [a]) h)
        (visible ++ [state.length]) withSlot
      ReadsMaterials d h (source ++ [a]) (visible ++ [state.length])
          (owners ++ [source.length]) (materials ++ [ownerMaterial]) withSlot ∧
        ReadsMaterialsForests d hs source coordinates visible owners materials ownerMaterial u c below withForest
end

mutual
  theorem encode_readsMaterials (d : Nat) (e : NumericalExpr) (source : ParentContext)
      (visible owners : List Nat) (materials : List (Forests (List Nat)))
      (state : State d) (positive : 0 < d)
      (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
      (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
      (known : VisibleMaterials d source visible owners materials state)
      (legal : Source.FiniteLegal d source e) :
      ReadsMaterials d e source visible owners materials state := by
    cases e with
    | nil => trivial
    | cons coordinates hs tail =>
      let a := Parents.label d source coordinates
      let annotated := Parents.annotateForests d (source ++ [a]) hs
      let key := Keys.ofColumn d visible.length a annotated
      let frame := frameAt state (representative visible a (d - 1))
      let below := smaller frame key
      let c := (base below).height
      let u := vector state visible a
      let guarded := emit (emit state u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 []
      have inherited : InheritedMaterials d source coordinates visible owners materials frame :=
        queried_frame_inheritedMaterials known view coordinates
      change MaterialQuery d source coordinates visible owners materials state hs ∧
        (match equal frame key with
        | some _ => True
        | none => ReadsMaterialsForests d hs source coordinates visible owners materials hs u c below guarded) ∧ _
      refine ⟨⟨inherited, coherent, valid, view, legal.1, legal.2.1, legal.2.2.2.1⟩, ?_, ?_⟩
      · cases found : equal frame key with
        | some bound => trivial
        | none =>
          exact encodeForests_readsMaterials d hs source coordinates visible owners materials hs
            state guarded u (state.length + 1) c below positive coherent valid view known
            (initial_numerical_gate state coherent valid view coordinates c)
            (smaller_inheritedMaterials inherited key) legal.1 legal.2.2.2.1 legal.2.2.2.1
      · exact encode_readsMaterials d tail (source ++ [a])
          (visible ++ [(headState d a annotated visible state).length - 1]) owners (materials ++ [hs])
          (headState d a annotated visible state) positive
          (Parents.coherent_append_label coherent coordinates)
          (Parents.context_valid_append_label d source valid coordinates)
          (headState_view state positive coherent valid view coordinates hs legal.2.2.2.1.separated)
          (headState_materials known view coordinates hs legal.1 legal.2.2.2.1) legal.2.2.2.2

  theorem encodeForests_readsMaterials (d : Nat) (hs : Forests (List Nat))
      (source : ParentContext) (coordinates visible owners : List Nat)
      (materials : List (Forests (List Nat))) (ownerMaterial : Forests (List Nat))
      (original state : State d) (u : Nat → Nat) (gate c : Nat) (below : List Binding)
      (positive : 0 < d) (coherent : Parents.Coherent d source)
      (valid : Parents.ContextValid source)
      (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix original)) visible)
      (known : VisibleMaterials d source visible owners materials original)
      (scope : NumericalGate d source coordinates visible original state u gate)
      (inherited : InheritedMaterials d source coordinates visible owners materials below)
      (width : coordinates.length = d)
      (ownerLegal : Source.FiniteLegalForests d (source ++ [Parents.label d source coordinates])
        (coordinates[0]?.getD 0) ownerMaterial)
      (legal : Source.FiniteLegalForests d (source ++ [Parents.label d source coordinates])
        (coordinates[0]?.getD 0) hs) :
      ReadsMaterialsForests d hs source coordinates visible owners materials ownerMaterial u c below state := by
    cases hs with
    | nil => trivial
    | cons h hs =>
      let a := Parents.label d source coordinates
      let withSlot := emit state (fun j => u j + 2) (c + 2) 0 below
      have nextCoherent := Parents.coherent_append_label coherent coordinates
      have nextValid := Parents.context_valid_append_label d source valid coordinates
      have slotView := scope.slot_view valid view (c + 2) below
      have slotMaterials := (known.extends scope.extended).inherit_slot inherited ownerMaterial width ownerLegal
        (fun j => u j + 2) (c + 2)
      refine ⟨?_, ?_⟩
      · exact encode_readsMaterials d h (source ++ [a]) (visible ++ [state.length])
          (owners ++ [source.length]) (materials ++ [ownerMaterial]) withSlot positive
          nextCoherent nextValid slotView slotMaterials legal.2.1
      · obtain ⟨finalVisible, extended, forestView⟩ := encode_numerical_view d h (source ++ [a])
          (visible ++ [state.length]) withSlot positive nextCoherent nextValid slotView legal.2.1.separated
        have nextScope := scope.after_forest positive coherent valid view.length
          (c + 2) below (Source.labels h) (encode_extends d _ _ _) extended legal.1 forestView
        exact encodeForests_readsMaterials d hs source coordinates visible owners materials ownerMaterial original
          (encode d (Parents.annotate d (source ++ [a]) h) (visible ++ [state.length]) withSlot)
          u gate c below positive coherent valid view known nextScope inherited width ownerLegal legal.2.2
end

/-- The final outer material context is exactly the list of input outer
attachments. It is not reconstructed from output keys. -/
theorem encode_material_view (d : Nat) (e : NumericalExpr) (source : ParentContext)
    (visible owners : List Nat) (materials : List (Forests (List Nat)))
    (state : State d) (positive : 0 < d)
    (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (known : VisibleMaterials d source visible owners materials state)
    (legal : Source.FiniteLegal d source e) :
    ∃ finalVisible, visible <+: finalVisible ∧
      Parents.NumericalView d (BMS.parentTableAux d source (Source.labels e))
        (BMS.parentTable (d + 2) (matrix (encode d (Parents.annotate d source e) visible state))) finalVisible ∧
      VisibleMaterials d (BMS.parentTableAux d source (Source.labels e)) finalVisible owners
        (materials ++ Source.outerMaterials e) (encode d (Parents.annotate d source e) visible state) := by
  cases e with
  | nil => exact ⟨visible, List.prefix_refl _, view, by
      simpa only [Source.outerMaterials, Source.labels, BMS.parentTableAux, Parents.annotate,
        encode, List.append_nil] using known⟩
  | cons coordinates hs tail =>
    let a := Parents.label d source coordinates
    let annotated := Parents.annotateForests d (source ++ [a]) hs
    let headed := headState d a annotated visible state
    obtain ⟨finalVisible, extended, finalView, finalMaterials⟩ := encode_material_view d tail
      (source ++ [a]) (visible ++ [headed.length - 1]) owners (materials ++ [hs]) headed positive
      (Parents.coherent_append_label coherent coordinates)
      (Parents.context_valid_append_label d source valid coordinates)
      (headState_view state positive coherent valid view coordinates hs legal.2.2.2.1.separated)
      (headState_materials known view coordinates hs legal.1 legal.2.2.2.1) legal.2.2.2.2
    refine ⟨finalVisible, (List.prefix_append _ _).trans extended, ?_, ?_⟩
    · simpa only [Source.labels, BMS.parentTableAux, Parents.annotate, encode_split_head] using finalView
    · simpa only [Source.labels, Source.outerMaterials, BMS.parentTableAux, Parents.annotate,
        encode_split_head, List.append_assoc, List.singleton_append] using finalMaterials

theorem source_readsMaterials (d : Nat) (e : NumericalExpr) (positive : 0 < d)
    (legal : Source.FiniteLegal d [] e) : ReadsMaterials d e [] [] [] [] [] :=
  encode_readsMaterials d e [] [] [] [] [] positive (Parents.empty_coherent d)
    Parents.empty_context_valid (Parents.empty_numerical_view d) (empty_visibleMaterials d) legal

theorem source_binding_materials (d : Nat) (e : NumericalExpr) (positive : 0 < d)
    (legal : Source.FiniteLegal d [] e) :
    ∃ visible, Parents.NumericalView d (BMS.parentTable d (Source.labels e))
        (BMS.parentTable (d + 2) (fromSource d e)) visible ∧
      VisibleMaterials d (BMS.parentTable d (Source.labels e)) visible [] (Source.outerMaterials e)
        (encode d (Parents.annotate d [] e) [] []) := by
  obtain ⟨visible, _, view, known⟩ := encode_material_view d e [] [] [] [] [] positive
    (Parents.empty_coherent d) Parents.empty_context_valid (Parents.empty_numerical_view d)
    (empty_visibleMaterials d) legal
  exact ⟨visible, view, known⟩

/-- Every actual frame query has actual finite-legal source attachment
payloads, with no bound on syntax depth or the length of the execution. -/
theorem standard_readsMaterials {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) : ReadsMaterials d e [] [] [] [] [] :=
  source_readsMaterials d e positive (Source.standard_finiteLegal positive standard)

theorem standard_binding_materials {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) :
    ∃ visible, Parents.NumericalView d (BMS.parentTable d (Source.labels e))
        (BMS.parentTable (d + 2) (fromSource d e)) visible ∧
      VisibleMaterials d (BMS.parentTable d (Source.labels e)) visible [] (Source.outerMaterials e)
        (encode d (Parents.annotate d [] e) [] []) :=
  source_binding_materials d e positive (Source.standard_finiteLegal positive standard)

end BTnSSBMS.Encoder
