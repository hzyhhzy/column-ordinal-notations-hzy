import BTnSSBMS.ForestScope

/-!
The numerical view invariant is preserved through the entire real mutual
encoder, including every nested forest and restoration of the outer scope.
The only source shape premise here is literal row-zero forest separation.
Its preservation by source fundamental sequences is a different theorem;
neither standardness nor order preservation is concluded in this module.
-/
namespace BTnSSBMS.Encoder

mutual
  theorem encode_numerical_view (d : Nat) (e : NumericalExpr)
      (source : ParentContext) (visible : List Nat) (state : State d)
      (positive : 0 < d) (sourceCoherent : Parents.Coherent d source)
      (sourceValid : Parents.ContextValid source)
      (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
      (separated : Source.ForestSeparated e) :
      ∃ finalVisible, visible <+: finalVisible ∧
        Parents.NumericalView d (BMS.parentTableAux d source (Source.labels e))
          (BMS.parentTable (d + 2) (matrix (encode d (Parents.annotate d source e) visible state)))
          finalVisible := by
    cases e with
    | nil => exact ⟨visible, List.prefix_refl _, view⟩
    | cons coordinates hs tail =>
      have nextCoherent := Parents.coherent_append_label sourceCoherent coordinates
      have nextValid := Parents.context_valid_append_label d source sourceValid coordinates
      simp only [Parents.annotate, encode, Source.labels, BMS.parentTableAux]
      split
      next bound same =>
        obtain ⟨finalVisible, extended, result⟩ := encode_numerical_view d tail
          (source ++ [Parents.label d source coordinates]) (visible ++ [state.length])
          (emit state (vector state visible (Parents.label d source coordinates)) bound.height 0
            (smaller (frameAt state (representative visible (Parents.label d source coordinates) (d - 1)))
              (Keys.ofColumn d visible.length (Parents.label d source coordinates)
                (Parents.annotateForests d (source ++ [Parents.label d source coordinates]) hs)) ++
              [{bound with latest := some state.length}]))
          positive nextCoherent nextValid (emit_numerical_view state sourceCoherent sourceValid view
            coordinates bound.height 0 _) separated.2
        exact ⟨finalVisible, (List.prefix_append _ _).trans extended, result⟩
      next fresh =>
        let a := Parents.label d source coordinates
        let annotated := Parents.annotateForests d (source ++ [a]) hs
        let key := Keys.ofColumn d visible.length a annotated
        let below := smaller (frameAt state (representative visible a (d - 1))) key
        let c := (base below).height
        let u := vector state visible a
        let withGuard := emit (emit state u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 []
        let withForests := encodeForests d annotated visible u c below withGuard
        have gate := encodeForests_numerical_gate d hs source coordinates visible state withGuard u
          (state.length + 1) c below positive sourceCoherent sourceValid view
          (initial_numerical_gate state sourceCoherent sourceValid view coordinates c) separated.1
        have finalView := closing_numerical_view state withForests sourceValid view coordinates c
          (below ++ [⟨key, c + 2, some withForests.length, some state.length⟩]) gate
          (encodeForests_extends d annotated visible u c below withGuard) positive sourceCoherent
        obtain ⟨finalVisible, extended, result⟩ := encode_numerical_view d tail (source ++ [a])
          (visible ++ [withForests.length])
          (emit withForests (fun j => u j + 1) (c + 2) 0
            (below ++ [⟨key, c + 2, some withForests.length, some state.length⟩]))
          positive nextCoherent nextValid finalView separated.2
        exact ⟨finalVisible, (List.prefix_append _ _).trans extended, result⟩

  theorem encodeForests_numerical_gate (d : Nat) (hs : Forests (List Nat))
      (source : ParentContext) (coordinates : List Nat) (visible : List Nat)
      (original state : State d) (u : Nat → Nat) (gate c : Nat) (below : List Binding)
      (positive : 0 < d) (sourceCoherent : Parents.Coherent d source)
      (sourceValid : Parents.ContextValid source)
      (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix original)) visible)
      (scope : NumericalGate d source coordinates visible original state u gate)
      (separated : Source.ForestsAbove (coordinates[0]?.getD 0) hs) :
      NumericalGate d source coordinates visible original
        (encodeForests d (Parents.annotateForests d (source ++ [Parents.label d source coordinates]) hs)
          visible u c below state) u gate := by
    cases hs with
    | nil => exact scope
    | cons h hs =>
      let a := Parents.label d source coordinates
      let withSlot := emit state (fun j => u j + 2) (c + 2) 0 below
      have nextCoherent := Parents.coherent_append_label sourceCoherent coordinates
      have nextValid := Parents.context_valid_append_label d source sourceValid coordinates
      obtain ⟨finalVisible, extended, forestView⟩ := encode_numerical_view d h (source ++ [a])
        (visible ++ [state.length]) withSlot positive nextCoherent nextValid
        (scope.slot_view sourceValid view (c + 2) below) separated.2.1
      have nextScope := scope.after_forest positive sourceCoherent sourceValid view.length
        (c + 2) below (Source.labels h) (encode_extends d _ _ _) extended separated.1 forestView
      exact encodeForests_numerical_gate d hs source coordinates visible original
        (encode d (Parents.annotate d (source ++ [a]) h) (visible ++ [state.length]) withSlot)
        u gate c below positive sourceCoherent sourceValid view nextScope separated.2.2
end

/-- The actual full encoding realizes every numerical ancestor relation
of its source's outer sequence. This includes arbitrary nested forests
satisfying the finite separation condition, not merely bounded fixtures. -/
theorem source_numerical_view (d : Nat) (e : NumericalExpr) (positive : 0 < d)
    (separated : Source.ForestSeparated e) :
    ∃ visible, Parents.NumericalView d (BMS.parentTable d (Source.labels e))
      (BMS.parentTable (d + 2) (fromSource d e)) visible := by
  obtain ⟨visible, _, result⟩ := encode_numerical_view d e [] [] [] positive
    (Parents.empty_coherent d) Parents.empty_context_valid (Parents.empty_numerical_view d) separated
  exact ⟨visible, result⟩

end BTnSSBMS.Encoder
