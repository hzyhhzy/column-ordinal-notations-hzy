import BTnSSBMS.FrameAncestry

/-! Key-row entry cases instantiated with the actual source parent search. -/
namespace BTnSSBMS.Encoder

theorem BindingRealized.definition_none_at_zero {state : State d} {b : Binding}
    (known : BindingRealized state b) (zero : b.height = 0) : b.definition = none := by
  cases found : b.definition with
  | none => rfl
  | some p =>
    have info := known.2.1
    rw [found] at info
    obtain ⟨h, height, _⟩ := info
    omega

theorem virtual_found_zero (key : Key) (bound : Binding) (found : equal virtualFrame key = some bound) :
    bound = zeroBinding := by
  have member := List.mem_of_find?_eq_some found
  simpa only [virtualFrame, List.mem_singleton] using member

theorem representative_position_bound {d : Nat} {source : ParentContext} {visible : List Nat}
    {state : State d}
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (coordinates : List Nat) (j position : Nat)
    (selected : representative visible (Parents.label d source coordinates) j = some position) :
    position < state.length := by
  rw [representative_eq_point view] at selected
  obtain ⟨p, parent, same⟩ := Option.map_eq_some_iff.mp selected
  have bound := view.bounded p (Parents.label_parent_bound d source coordinates j p parent)
  rw [table_length] at bound
  simpa only [same] using bound

theorem head_lower_parent {d : Nat} {source : ParentContext} {visible : List Nat}
    (state : State d) (sourceCoherent : Parents.Coherent d source)
    (sourceValid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (coordinates : List Nat) (height tag : Nat) (frame : List Binding) (positive : 0 < d) :
    Parents.parent (BMS.parentTable (d + 2) (matrix
      (emit state (vector state visible (Parents.label d source coordinates)) height tag frame)))
      (d - 1) state.length = representative visible (Parents.label d source coordinates) (d - 1) := by
  rw [emitted_parent]
  exact emitted_head_numerical_parents state sourceCoherent sourceValid view coordinates height tag (d - 1) (by omega)

/-- The actual reused-P key parent is the saved definition, including
the zero-key case with no parent. Its updated frame is anchored at P. -/
theorem reused_head_result {d : Nat} {source : ParentContext} {visible : List Nat}
    (state : State d) (sourceCoherent : Parents.Coherent d source)
    (sourceValid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (ordered : FramesOrdered state) (realized : FramesRealized state) (paths : FramesAncestral state)
    (coordinates : List Nat) (key : Key) (bound : Binding) (positive : 0 < d)
    (found : equal (frameAt state (representative visible (Parents.label d source coordinates) (d - 1))) key = some bound) :
    let frame := frameAt state (representative visible (Parents.label d source coordinates) (d - 1))
    let updated := smaller frame key ++ [{bound with latest := some state.length}]
    let next := emit state (vector state visible (Parents.label d source coordinates)) bound.height 0 updated
    Parents.parent (BMS.parentTable (d + 2) (matrix next)) d state.length = bound.definition ∧
      FrameAncestral next state.length updated := by
  dsimp only
  let frame := frameAt state (representative visible (Parents.label d source coordinates) (d - 1))
  let u := vector state visible (Parents.label d source coordinates)
  let updated := smaller frame key ++ [{bound with latest := some state.length}]
  let next := emit state u bound.height 0 updated
  have frameOrder : FrameOrdered frame := queried_frame_ordered ordered _
  have frameKnown : FrameRealized state frame := queried_frame_realized realized _
  have boundKnown := frameKnown bound (List.mem_of_find?_eq_some found)
  by_cases positiveHeight : 0 < bound.height
  · obtain ⟨position, representativeFound⟩ : ∃ p,
        representative visible (Parents.label d source coordinates) (d - 1) = some p := by
      cases selected : representative visible (Parents.label d source coordinates) (d - 1) with
      | none =>
        have virtualFound : equal virtualFrame key = some bound := by
          simpa only [selected, frameAt, Option.bind_none] using found
        have same := virtual_found_zero key bound virtualFound
        simp only [same, zeroBinding] at positiveHeight
        omega
      | some p => exact ⟨p, rfl⟩
    have positionBound := representative_position_bound view coordinates (d - 1) position representativeFound
    have framePaths : FrameAncestral state position frame := by
      simpa only [frame, representativeFound] using queried_frame_ancestral paths position positionBound
    obtain ⟨root, height, definition, heightEq, output, rootPath, belowPath⟩ :=
      reused_definition_anchor framePaths frameKnown frameOrder key bound found positiveHeight
    have lower : Parents.parent (BMS.parentTable (d + 2) (matrix next)) (d - 1) state.length = some position :=
      (head_lower_parent state sourceCoherent sourceValid view coordinates bound.height 0 updated positive).trans representativeFound
    have keyParent : Parents.parent (BMS.parentTable (d + 2) (matrix next)) d state.length = some root :=
      emitted_key_parent state u bound.height 0 updated positive position root lower rootPath
        (by rw [output.key_reading]; exact heightEq)
    refine ⟨keyParent.trans definition.symm, ?_⟩
    apply frame_ancestral_append
      ((belowPath.extends (emit_extends ..)).trans (.up keyParent (.refl _)))
      {bound with latest := some state.length} rfl
    intro q selected
    have same : q = root := by simpa only [definition, Option.some.injEq] using selected.symm
    subst q
    exact .up keyParent (.refl _)
  · have zero : bound.height = 0 := by omega
    have noDefinition := boundKnown.definition_none_at_zero zero
    have belowEmpty := smaller_empty_at_zero frameOrder key bound found zero
    refine ⟨?_, ?_⟩
    · rw [noDefinition, zero]
      exact emitted_key_zero ..
    · apply frame_ancestral_append
      · rw [belowEmpty]
        exact empty_frame_ancestral _ _
      · rfl
      · intro q selected
        simp [noDefinition] at selected

/-- A new definition is placed just above the latest representative of
the greatest retained binding. Every retained pointer remains its ancestor. -/
theorem fresh_head_result {d : Nat} {source : ParentContext} {visible : List Nat}
    (state : State d) (sourceCoherent : Parents.Coherent d source)
    (sourceValid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (ordered : FramesOrdered state) (realized : FramesRealized state) (paths : FramesAncestral state)
    (coordinates : List Nat) (key : Key) (positive : 0 < d)
    (position : Nat)
    (selected : representative visible (Parents.label d source coordinates) (d - 1) = some position)
    (nonempty : smaller (frameAt state (some position)) key ≠ []) :
    let below := smaller (frameAt state (some position)) key
    let c := (base below).height
    let next := emit state (vector state visible (Parents.label d source coordinates)) (c + 1) 1 []
    ∃ root, (base below).latest = some root ∧ Readout state root c 0 ∧
      Parents.parent (BMS.parentTable (d + 2) (matrix next)) d state.length = some root ∧
      FrameAncestral next state.length below := by
  dsimp only
  let frame := frameAt state (some position)
  let below := smaller frame key
  let c := (base below).height
  let u := vector state visible (Parents.label d source coordinates)
  have positionBound := representative_position_bound view coordinates (d - 1) position selected
  have framePaths := queried_frame_ancestral paths position positionBound
  have frameKnown := queried_frame_realized realized (some position)
  have frameOrder := queried_frame_ordered ordered (some position)
  obtain ⟨root, latest, output, path, belowPaths⟩ :=
    fresh_definition_anchor framePaths frameKnown frameOrder key nonempty
  have lower := (head_lower_parent state sourceCoherent sourceValid view coordinates (c + 1) 1 [] positive).trans selected
  have keyParent := emitted_key_parent state u (c + 1) 1 [] positive position root lower path
    (by rw [output.key_reading])
  exact ⟨root, latest, output, keyParent,
    (belowPaths.extends (emit_extends ..)).trans (.up keyParent (.refl _))⟩

end BTnSSBMS.Encoder
