import BTnSSBMS.BindingSources
import BTnSSBMS.SourceFiniteClosure

/-!
Source provenance at every actual frame query, including arbitrary nested
forests. The recursive predicates below follow the existing encoder. An
owner is protected only while its forest is being encoded; exits restore
both the old visible context and the old owner list. This is a statement
about the entire execution, not just its final outer sequence.
-/
namespace BTnSSBMS.Encoder

mutual
  def ReadsSources (d : Nat) (e : NumericalExpr) (source : ParentContext)
      (visible owners : List Nat) (state : State d) : Prop :=
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
      InheritedSources d source coordinates visible owners frame ∧
        (match equal frame key with
        | some _ => True
        | none => ReadsSourcesForests d hs source coordinates visible owners u c below
            (emit (emit state u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 [])) ∧
        ReadsSources d tail (source ++ [a]) (visible ++ [headed.length - 1]) owners headed

  def ReadsSourcesForests (d : Nat) (hs : Forests (List Nat)) (source : ParentContext)
      (coordinates visible owners : List Nat) (u : Nat → Nat) (c : Nat)
      (below : List Binding) (state : State d) : Prop :=
    match hs with
    | .nil => True
    | .cons h hs =>
      let a := Parents.label d source coordinates
      let withSlot := emit state (fun j => u j + 2) (c + 2) 0 below
      let withForest := encode d (Parents.annotate d (source ++ [a]) h)
        (visible ++ [state.length]) withSlot
      ReadsSources d h (source ++ [a]) (visible ++ [state.length])
          (owners ++ [source.length]) withSlot ∧
        ReadsSourcesForests d hs source coordinates visible owners u c below withForest
end

mutual
  theorem encode_readsSources (d : Nat) (e : NumericalExpr) (source : ParentContext)
      (visible owners : List Nat) (state : State d) (positive : 0 < d)
      (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
      (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
      (sources : VisibleSources d source visible owners state)
      (separated : Source.ForestSeparated e) :
      ReadsSources d e source visible owners state := by
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
      have inherited : InheritedSources d source coordinates visible owners frame :=
        queried_frame_inheritedSources sources view coordinates
      change InheritedSources d source coordinates visible owners frame ∧
        (match equal frame key with
        | some _ => True
        | none => ReadsSourcesForests d hs source coordinates visible owners u c below guarded) ∧ _
      refine ⟨inherited, ?_, ?_⟩
      · cases found : equal frame key with
        | some bound => trivial
        | none =>
          exact encodeForests_readsSources d hs source coordinates visible owners state guarded u
            (state.length + 1) c below positive coherent valid view sources
            (initial_numerical_gate state coherent valid view coordinates c)
            (smaller_inheritedSources inherited key) separated.1
      · exact encode_readsSources d tail (source ++ [a])
          (visible ++ [(headState d a annotated visible state).length - 1]) owners
          (headState d a annotated visible state) positive
          (Parents.coherent_append_label coherent coordinates)
          (Parents.context_valid_append_label d source valid coordinates)
          (headState_view state positive coherent valid view coordinates hs separated.1)
          (headState_sources sources view coordinates hs) separated.2

  theorem encodeForests_readsSources (d : Nat) (hs : Forests (List Nat))
      (source : ParentContext) (coordinates visible owners : List Nat)
      (original state : State d) (u : Nat → Nat) (gate c : Nat) (below : List Binding)
      (positive : 0 < d) (coherent : Parents.Coherent d source)
      (valid : Parents.ContextValid source)
      (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix original)) visible)
      (sources : VisibleSources d source visible owners original)
      (scope : NumericalGate d source coordinates visible original state u gate)
      (inherited : InheritedSources d source coordinates visible owners below)
      (separated : Source.ForestsAbove (coordinates[0]?.getD 0) hs) :
      ReadsSourcesForests d hs source coordinates visible owners u c below state := by
    cases hs with
    | nil => trivial
    | cons h hs =>
      let a := Parents.label d source coordinates
      let withSlot := emit state (fun j => u j + 2) (c + 2) 0 below
      have nextCoherent := Parents.coherent_append_label coherent coordinates
      have nextValid := Parents.context_valid_append_label d source valid coordinates
      have slotView := scope.slot_view valid view (c + 2) below
      have slotSources := (sources.extends scope.extended).inherit_slot inherited
        (fun j => u j + 2) (c + 2)
      refine ⟨?_, ?_⟩
      · exact encode_readsSources d h (source ++ [a]) (visible ++ [state.length])
          (owners ++ [source.length]) withSlot positive nextCoherent nextValid slotView
          slotSources separated.2.1
      · obtain ⟨finalVisible, extended, forestView⟩ := encode_numerical_view d h (source ++ [a])
          (visible ++ [state.length]) withSlot positive nextCoherent nextValid slotView separated.2.1
        have nextScope := scope.after_forest positive coherent valid view.length
          (c + 2) below (Source.labels h) (encode_extends d _ _ _) extended separated.1 forestView
        exact encodeForests_readsSources d hs source coordinates visible owners original
          (encode d (Parents.annotate d (source ++ [a]) h) (visible ++ [state.length]) withSlot)
          u gate c below positive coherent valid view sources nextScope inherited separated.2.2
end

/-- The final visible list simultaneously realizes numerical ancestry and
source binding provenance. Inner forests are not appended to this list. -/
theorem encode_source_view (d : Nat) (e : NumericalExpr) (source : ParentContext)
    (visible owners : List Nat) (state : State d) (positive : 0 < d)
    (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (sources : VisibleSources d source visible owners state)
    (separated : Source.ForestSeparated e) :
    ∃ finalVisible, visible <+: finalVisible ∧
      Parents.NumericalView d (BMS.parentTableAux d source (Source.labels e))
        (BMS.parentTable (d + 2) (matrix (encode d (Parents.annotate d source e) visible state)))
        finalVisible ∧
      VisibleSources d (BMS.parentTableAux d source (Source.labels e)) finalVisible owners
        (encode d (Parents.annotate d source e) visible state) := by
  cases e with
  | nil => exact ⟨visible, List.prefix_refl _, view, sources⟩
  | cons coordinates hs tail =>
    let a := Parents.label d source coordinates
    let annotated := Parents.annotateForests d (source ++ [a]) hs
    let headed := headState d a annotated visible state
    obtain ⟨finalVisible, extended, finalView, finalSources⟩ := encode_source_view d tail
      (source ++ [a]) (visible ++ [headed.length - 1]) owners headed positive
      (Parents.coherent_append_label coherent coordinates)
      (Parents.context_valid_append_label d source valid coordinates)
      (headState_view state positive coherent valid view coordinates hs separated.1)
      (headState_sources sources view coordinates hs) separated.2
    refine ⟨finalVisible, (List.prefix_append _ _).trans extended, ?_, ?_⟩
    · simpa only [Source.labels, BMS.parentTableAux, Parents.annotate, encode_split_head] using finalView
    · simpa only [Source.labels, BMS.parentTableAux, Parents.annotate, encode_split_head] using finalSources

/-- The full outer result has real, unique visible source representatives;
all saved latest pointers in those frames follow highest numerical ancestry. -/
theorem source_binding_sources (d : Nat) (e : NumericalExpr) (positive : 0 < d)
    (separated : Source.ForestSeparated e) :
    ∃ visible, Parents.NumericalView d (BMS.parentTable d (Source.labels e))
        (BMS.parentTable (d + 2) (fromSource d e)) visible ∧
      VisibleSources d (BMS.parentTable d (Source.labels e)) visible []
        (encode d (Parents.annotate d [] e) [] []) := by
  obtain ⟨visible, _, view, sources⟩ := encode_source_view d e [] [] [] [] positive
    (Parents.empty_coherent d) Parents.empty_context_valid
    (Parents.empty_numerical_view d) (empty_visibleSources d) separated
  exact ⟨visible, view, sources⟩

/-- Every actual frame read has a visible, strictly older, non-owner source
origin on the highest numerical chain. No depth or execution bound occurs. -/
theorem source_readsSources (d : Nat) (e : NumericalExpr) (positive : 0 < d)
    (separated : Source.ForestSeparated e) : ReadsSources d e [] [] [] [] :=
  encode_readsSources d e [] [] [] [] positive (Parents.empty_coherent d)
    Parents.empty_context_valid (Parents.empty_numerical_view d) (empty_visibleSources d) separated

theorem standard_readsSources {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) : ReadsSources d e [] [] [] [] :=
  source_readsSources d e positive (Source.standard_finiteLegal positive standard).separated

theorem standard_binding_sources {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) :
    ∃ visible, Parents.NumericalView d (BMS.parentTable d (Source.labels e))
        (BMS.parentTable (d + 2) (fromSource d e)) visible ∧
      VisibleSources d (BMS.parentTable d (Source.labels e)) visible []
        (encode d (Parents.annotate d [] e) [] []) :=
  source_binding_sources d e positive (Source.standard_finiteLegal positive standard).separated

end BTnSSBMS.Encoder
