import BTnSSBMS.NumericalKinds
import BTnSSBMS.SourceFiniteClosure

/-!
An exhaustive numerical-column classification for the complete encoder.
The trace records each source column's first output (new D or reused P),
not its closing representative. Auxiliary columns are classified using
their actually computed parents, including arbitrary nested forest scopes.
-/
namespace BTnSSBMS.Encoder

mutual
  def headPositions (d : Nat) (e : ParentExpr) (visible : List Nat) (state : State d) : List Nat :=
    match e with
    | .nil => []
    | .cons a hs tail =>
      let key := Keys.ofColumn d visible.length a hs
      let u := vector state visible a
      let below := smaller (frameAt state (representative visible a (d - 1))) key
      state.length :: (match equal (frameAt state (representative visible a (d - 1))) key with
      | some bound =>
        headPositions d tail (visible ++ [state.length])
          (emit state u bound.height 0 (below ++ [{bound with latest := some state.length}]))
      | none =>
        let c := (base below).height
        let guarded := emit (emit state u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 []
        let forests := encodeForests d hs visible u c below guarded
        forestHeadPositions d hs visible u c below guarded ++
          headPositions d tail (visible ++ [forests.length])
            (emit forests (fun j => u j + 1) (c + 2) 0
              (below ++ [⟨key, c + 2, some forests.length, some state.length⟩])))
  def forestHeadPositions (d : Nat) (hs : Forests ParentLabel) (visible : List Nat)
      (u : Nat → Nat) (c : Nat) (below : List Binding) (state : State d) : List Nat :=
    match hs with
    | .nil => []
    | .cons h hs =>
      let withSlot := emit state (fun j => u j + 2) (c + 2) 0 below
      let withForest := encode d h (visible ++ [state.length]) withSlot
      headPositions d h (visible ++ [state.length]) withSlot ++
        forestHeadPositions d hs visible u c below withForest
end

mutual
  theorem encode_numericalClasses (d : Nat) (e : NumericalExpr)
      (source : ParentContext) (visible : List Nat) (state : State d) (heads : List Nat)
      (positive : 0 < d) (sourceCoherent : Parents.Coherent d source)
      (sourceValid : Parents.ContextValid source)
      (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
      (separated : Source.ForestSeparated e) (zero : VisibleZero state visible)
      (classes : NumericalClasses state heads) :
      NumericalClasses (encode d (Parents.annotate d source e) visible state)
        (heads ++ headPositions d (Parents.annotate d source e) visible state) := by
    cases e with
    | nil => simpa only [Parents.annotate, encode, headPositions, List.append_nil] using classes
    | cons coordinates hs tail =>
      have nextCoherent := Parents.coherent_append_label sourceCoherent coordinates
      have nextValid := Parents.context_valid_append_label d source sourceValid coordinates
      let a := Parents.label d source coordinates
      let annotated := Parents.annotateForests d (source ++ [a]) hs
      let key := Keys.ofColumn d visible.length a annotated
      let below := smaller (frameAt state (representative visible a (d - 1))) key
      let u := vector state visible a
      simp only [Parents.annotate, headPositions, encode]
      split
      next bound found =>
        rw [found]
        let updated := below ++ [{bound with latest := some state.length}]
        let next := emit state u bound.height 0 updated
        have headClass : NumericalClasses next (heads ++ [state.length]) :=
          numericalClasses_emit_head classes u bound.height 0 updated
            (emitted_source_numericalHead state sourceCoherent sourceValid view zero coordinates bound.height 0 updated)
        have result := encode_numericalClasses d tail (source ++ [a]) (visible ++ [state.length]) next
          (heads ++ [state.length]) positive nextCoherent nextValid
          (emit_numerical_view state sourceCoherent sourceValid view coordinates bound.height 0 updated)
          separated.2 (visibleZero_emit zero u bound.height updated) headClass
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using result
      next fresh =>
        rw [fresh]
        let c := (base below).height
        let withD := emit state u (c + 1) 1 []
        let withH := emit withD (fun j => u j + 1) (c + 2) 2 []
        let withForests := encodeForests d annotated visible u c below withH
        have classesD : NumericalClasses withD (heads ++ [state.length]) :=
          numericalClasses_emit_head classes u (c + 1) 1 []
            (emitted_source_numericalHead state sourceCoherent sourceValid view zero coordinates (c + 1) 1 [])
        have classesH : NumericalClasses withH (heads ++ [state.length]) :=
          numericalClasses_emit_aux classesD (fun j => u j + 1) (c + 2) 2 []
            (by simpa only [withD, emit_length] using guard_numericalAuxiliary state u c)
        have zeroH : VisibleZero withH visible := zero.extends ((emit_extends ..).trans (emit_extends ..))
        have gate := initial_numerical_gate state sourceCoherent sourceValid view coordinates c
        have classesForests := encodeForests_numericalClasses d hs source coordinates visible state withH u c below
          (heads ++ [state.length]) positive sourceCoherent sourceValid view gate (List.prefix_refl _)
          separated.1 zeroH classesH
        have afterGate := encodeForests_numerical_gate d hs source coordinates visible state withH u
          (state.length + 1) c below positive sourceCoherent sourceValid view gate separated.1
        have forestExtends : withH <+: withForests := encodeForests_extends ..
        let finalFrame := below ++ [⟨key, c + 2, some withForests.length, some state.length⟩]
        let closed := emit withForests (fun j => u j + 1) (c + 2) 0 finalFrame
        have closeClasses : NumericalClasses closed
            ((heads ++ [state.length]) ++ forestHeadPositions d annotated visible u c below withH) :=
          numericalClasses_emit_aux classesForests (fun j => u j + 1) (c + 2) 0 finalFrame
            (afterGate.closing_numericalAuxiliary forestExtends positive (c + 2) 0 finalFrame)
        have closeView := closing_numerical_view state withForests sourceValid view coordinates c finalFrame
          afterGate forestExtends positive sourceCoherent
        have closeZero := visibleZero_emit (zeroH.extends forestExtends) (fun j => u j + 1) (c + 2) finalFrame
        have result := encode_numericalClasses d tail (source ++ [a]) (visible ++ [withForests.length]) closed
          ((heads ++ [state.length]) ++ forestHeadPositions d annotated visible u c below withH)
          positive nextCoherent nextValid closeView separated.2 closeZero closeClasses
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using result

  theorem encodeForests_numericalClasses (d : Nat) (hs : Forests (List Nat))
      (source : ParentContext) (coordinates : List Nat) (visible : List Nat)
      (original state : State d) (u : Nat → Nat) (c : Nat) (below : List Binding) (heads : List Nat)
      (positive : 0 < d) (sourceCoherent : Parents.Coherent d source)
      (sourceValid : Parents.ContextValid source)
      (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix original)) visible)
      (scope : NumericalGate d source coordinates visible original state u (original.length + 1))
      (headed : emit (emit original u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 [] <+: state)
      (separated : Source.ForestsAbove (coordinates[0]?.getD 0) hs)
      (zero : VisibleZero state visible) (classes : NumericalClasses state heads) :
      NumericalClasses (encodeForests d
        (Parents.annotateForests d (source ++ [Parents.label d source coordinates]) hs) visible u c below state)
        (heads ++ forestHeadPositions d
          (Parents.annotateForests d (source ++ [Parents.label d source coordinates]) hs) visible u c below state) := by
    cases hs with
    | nil => simpa only [Parents.annotateForests, encodeForests, forestHeadPositions, List.append_nil] using classes
    | cons h hs =>
      let a := Parents.label d source coordinates
      let withSlot := emit state (fun j => u j + 2) (c + 2) 0 below
      let withForest := encode d (Parents.annotate d (source ++ [a]) h) (visible ++ [state.length]) withSlot
      have nextCoherent := Parents.coherent_append_label sourceCoherent coordinates
      have nextValid := Parents.context_valid_append_label d source sourceValid coordinates
      have guardOutput : Readout state (original.length + 1) (c + 2) 2 := by
        have output := readout_emit (emit original u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 []
        exact readout_extends headed (by simpa only [emit_length] using output)
      have slotClasses := numericalClasses_emit_aux classes (fun j => u j + 2) (c + 2) 0 below
        (scope.slot_numericalAuxiliary (c + 2) guardOutput (c + 2) below)
      have slotView := scope.slot_view sourceValid view (c + 2) below
      have forestClasses := encode_numericalClasses d h (source ++ [a]) (visible ++ [state.length]) withSlot
        heads positive nextCoherent nextValid slotView separated.2.1
        (visibleZero_emit zero (fun j => u j + 2) (c + 2) below) slotClasses
      obtain ⟨finalVisible, extended, forestView⟩ := encode_numerical_view d h (source ++ [a])
        (visible ++ [state.length]) withSlot positive nextCoherent nextValid slotView separated.2.1
      have nextScope := scope.after_forest positive sourceCoherent sourceValid view.length
        (c + 2) below (Source.labels h) (encode_extends d _ _ _) extended separated.1 forestView
      have forestExtends : state <+: withForest := (emit_extends ..).trans (encode_extends ..)
      have result := encodeForests_numericalClasses d hs source coordinates visible original withForest u c below
        (heads ++ headPositions d (Parents.annotate d (source ++ [a]) h) (visible ++ [state.length]) withSlot)
        positive sourceCoherent sourceValid view nextScope (headed.trans forestExtends) separated.2.2
        (zero.extends forestExtends) forestClasses
      simpa only [Parents.annotateForests, encodeForests, forestHeadPositions, List.append_assoc] using result
end

theorem source_numericalClasses (d : Nat) (e : NumericalExpr) (positive : 0 < d)
    (separated : Source.ForestSeparated e) :
    NumericalClasses (encode d (Parents.annotate d [] e) [] [])
      (headPositions d (Parents.annotate d [] e) [] []) :=
  encode_numericalClasses d e [] [] [] [] positive (Parents.empty_coherent d) Parents.empty_context_valid
    (Parents.empty_numerical_view d) separated (by intro p member; simp at member)
    (by intro p inside; simp at inside)

theorem standard_numericalClasses {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) :
    NumericalClasses (encode d (Parents.annotate d [] e) [] [])
      (headPositions d (Parents.annotate d [] e) [] []) :=
  source_numericalClasses d e positive (Source.standard_finiteLegal positive standard).separated

/-- Every intermediate-row SB pair in an encoded standard source has two
actual source-entry endpoints. This does not yet compare their whole blocks. -/
theorem standard_intermediate_pair_heads {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {a b j : Nat}
    (rowPositive : 0 < j) (room : j < d) (before : a < b) (inside : b < (fromSource d e).length)
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (fromSource d e)) (j - 1) a b)
    (same : Parents.parent (BMS.parentTable (d + 2) (fromSource d e)) j a =
      Parents.parent (BMS.parentTable (d + 2) (fromSource d e)) j b) :
    a ∈ headPositions d (Parents.annotate d [] e) [] [] ∧
      b ∈ headPositions d (Parents.annotate d [] e) [] [] :=
  (standard_numericalClasses positive standard).intermediate_pair rowPositive room before
    (by simpa only [fromSource, matrix, List.length_map] using inside) path same

theorem standard_sibling_pair_types {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {a b : Nat}
    (before : a < b) (inside : b < (fromSource d e).length)
    (same : Parents.parent (BMS.parentTable (d + 2) (fromSource d e)) 0 a =
      Parents.parent (BMS.parentTable (d + 2) (fromSource d e)) 0 b) :
    (a ∈ headPositions d (Parents.annotate d [] e) [] [] ∧
      b ∈ headPositions d (Parents.annotate d [] e) [] []) ∨
      ∃ root height tag, (tag = 1 ∨ tag = 2) ∧
        Readout (encode d (Parents.annotate d [] e) [] []) root height tag ∧
        ∀ j, j < d →
          Parents.parent (BMS.parentTable (d + 2) (fromSource d e)) j a = some root ∧
          Parents.parent (BMS.parentTable (d + 2) (fromSource d e)) j b = some root := by
  have bBound : b < (encode d (Parents.annotate d [] e) [] []).length := by
    simpa only [fromSource, matrix, List.length_map] using inside
  exact (standard_numericalClasses positive standard).sibling_pair positive (by omega) bBound same

end BTnSSBMS.Encoder
