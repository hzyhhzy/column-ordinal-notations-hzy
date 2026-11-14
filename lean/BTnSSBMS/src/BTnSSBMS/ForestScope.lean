import BTnSSBMS.ForestFence

/-!
Numerical forest scopes of the actual encoder. A gate records actual
computed ancestry and values, not a semantic rank. Slot entry, forest exit
and closing-P emission are proved separately so the mutual recursion can
use them without assuming its own preservation theorem.
-/
namespace BTnSSBMS.Source

mutual
  /-- Every attached forest stays strictly above its owner in row zero.
  This finite input condition is not asserted here for the standard domain. -/
  def ForestSeparated : NumericalExpr → Prop
    | .nil => True
    | .cons a hs t => ForestsAbove (a[0]?.getD 0) hs ∧ ForestSeparated t
  def ForestsAbove (owner : Nat) : Forests (List Nat) → Prop
    | .nil => True
    | .cons h hs =>
      (∀ col ∈ labels h, owner < col[0]?.getD 0) ∧
      ForestSeparated h ∧ ForestsAbove owner hs
end

end BTnSSBMS.Source

namespace BTnSSBMS.Encoder

structure NumericalGate (d : Nat) (source : ParentContext) (coordinates : List Nat)
    (visible : List Nat) (original state : State d) (u : Nat → Nat) (gate : Nat) : Prop where
  extended : original <+: state
  nonempty : 0 < state.length
  bounded : gate < state.length
  values : ∀ j, j < d →
    Parents.reading (BMS.parentTable (d + 2) (matrix state)) j gate = u j + 1
  roots : ∀ j, j < d → ∀ p,
    (Parents.label d source coordinates).parents[j]?.join = some p →
    Parents.Ancestor (BMS.parentTable (d + 2) (matrix state)) j (Parents.point visible p) gate
  fence : Parents.Ancestor (BMS.parentTable (d + 2) (matrix state)) 0 gate (state.length - 1)

theorem initial_numerical_gate {d : Nat} {source : ParentContext} {visible : List Nat}
    (state : State d) (sourceCoherent : Parents.Coherent d source)
    (sourceValid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (coordinates : List Nat) (c : Nat) :
    NumericalGate d source coordinates visible state
      (emit (emit state (vector state visible (Parents.label d source coordinates)) (c + 1) 1 [])
        (fun j => vector state visible (Parents.label d source coordinates) j + 1) (c + 2) 2 [])
      (vector state visible (Parents.label d source coordinates)) (state.length + 1) := by
  refine ⟨(emit_extends ..).trans (emit_extends ..), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [emit_length]; omega
  · simp only [emit_length]; omega
  · intro j room
    simpa only [emit_length] using emitted_numerical_value
      (emit state (vector state visible (Parents.label d source coordinates)) (c + 1) 1 [])
      (fun j => vector state visible (Parents.label d source coordinates) j + 1) (c + 2) 2 [] j room
  · intro j room p selected
    exact .up (guard_numerical_parents state _ c j room)
      ((emitted_source_parent_path state sourceCoherent sourceValid view coordinates (c + 1) 1 []
        j p room selected).prefix (table_emit_prefix ..))
  · simp only [emit_length, Nat.add_sub_cancel]
    exact .refl _

theorem NumericalGate.slot_parents {d : Nat} {source : ParentContext} {coordinates : List Nat}
    {visible : List Nat} {original state : State d} {u : Nat → Nat} {gate : Nat}
    (scope : NumericalGate d source coordinates visible original state u gate)
    (height : Nat) (frame : List Binding) (j : Nat) (inside : j < d) :
    Parents.parent (BMS.parentTable (d + 2) (matrix
      (emit state (fun k => u k + 2) height 0 frame))) j state.length = some gate := by
  apply auxiliary_numerical_parents state _ height 0 frame gate scope.nonempty scope.fence
    (fun k room => by rw [scope.values k room]) j inside

theorem NumericalGate.slot_view {d : Nat} {source : ParentContext} {coordinates : List Nat}
    {visible : List Nat} {original state : State d} {u : Nat → Nat} {gate : Nat}
    (scope : NumericalGate d source coordinates visible original state u gate)
    (sourceValid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix original)) visible)
    (height : Nat) (frame : List Binding) :
    Parents.NumericalView d (source ++ [Parents.label d source coordinates])
      (BMS.parentTable (d + 2) (matrix (emit state (fun k => u k + 2) height 0 frame)))
      (visible ++ [state.length]) := by
  apply view.append_stretched _ (Parents.context_valid_append_label d source sourceValid coordinates)
    (table_prefix (scope.extended.trans (emit_extends ..))) state.length
    (by rw [table_length, emit_length]; omega) (by rw [table_length, emit_length])
    (by rw [table_length]; exact scope.extended.length_le)
  intro j room p selected
  exact .up (scope.slot_parents height frame j room)
    ((scope.roots j room p selected).prefix (table_emit_prefix ..))

theorem NumericalGate.after_forest {d : Nat} {source : ParentContext} {coordinates : List Nat}
    {visible finalVisible : List Nat} {original state next : State d} {u : Nat → Nat} {gate : Nat}
    (scope : NumericalGate d source coordinates visible original state u gate)
    (positive : 0 < d) (sourceCoherent : Parents.Coherent d source)
    (sourceValid : Parents.ContextValid source) (visibleLength : visible.length = source.length)
    (height : Nat) (frame : List Binding) (m : Matrix)
    (nextExtends : emit state (fun k => u k + 2) height 0 frame <+: next)
    (visibleExtends : visible ++ [state.length] <+: finalVisible)
    (above : ∀ col ∈ m, coordinates[0]?.getD 0 < col[0]?.getD 0)
    (view : Parents.NumericalView d
      (BMS.parentTableAux d (source ++ [Parents.label d source coordinates]) m)
      (BMS.parentTable (d + 2) (matrix next)) finalVisible) :
    NumericalGate d source coordinates visible original next u gate := by
  have stateExtends := (emit_extends ..).trans nextExtends
  have tableExtends := table_prefix stateExtends
  have longer := stateExtends.length_le
  refine ⟨scope.extended.trans stateExtends, by have := scope.nonempty; omega,
    by have := scope.bounded; omega, ?_, ?_, ?_⟩
  · intro j room
    rw [← Parents.reading_prefix tableExtends j gate (by rw [table_length]; exact scope.bounded)]
    exact scope.values j room
  · intro j room p selected
    exact (scope.roots j room p selected).prefix tableExtends
  · have forestFence := forest_output_fence next m positive
      (Parents.coherent_append_label sourceCoherent coordinates)
      (Parents.context_valid_append_label d source sourceValid coordinates)
      (by simp) (by simp only [List.length_append, List.length_cons, List.length_nil, visibleLength])
      visibleExtends (by
        intro col member
        simpa only [List.length_append, List.length_cons, List.length_nil, Nat.add_sub_cancel,
          Parents.reading_append_label] using above col member) view
    have atOwner : Parents.point (visible ++ [state.length])
        ((source ++ [Parents.label d source coordinates]).length - 1) = state.length := by
      simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_sub_cancel,
        ← visibleLength, Parents.point_append_last]
    rw [atOwner] at forestFence
    exact ((Parents.Ancestor.up (scope.slot_parents height frame 0 positive) (.refl gate)).prefix
      (table_prefix nextExtends)).trans forestFence

/-- Closing a fresh owner restores the old source scope. Its numerical
parents are D, even when any number of nonempty forests intervened. -/
theorem closing_numerical_view {d : Nat} {source : ParentContext} {visible : List Nat}
    (state next : State d) (sourceValid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (coordinates : List Nat) (c : Nat) (frame : List Binding)
    (scope : NumericalGate d source coordinates visible state next
      (vector state visible (Parents.label d source coordinates)) (state.length + 1))
    (withGuardExtends :
      emit (emit state (vector state visible (Parents.label d source coordinates)) (c + 1) 1 [])
        (fun j => vector state visible (Parents.label d source coordinates) j + 1) (c + 2) 2 [] <+: next)
    (positive : 0 < d) (sourceCoherent : Parents.Coherent d source) :
    Parents.NumericalView d (source ++ [Parents.label d source coordinates])
      (BMS.parentTable (d + 2) (matrix (emit next
        (fun j => vector state visible (Parents.label d source coordinates) j + 1) (c + 2) 0 frame)))
      (visible ++ [next.length]) := by
  let u := vector state visible (Parents.label d source coordinates)
  let withD := emit state u (c + 1) 1 []
  let withH := emit withD (fun j => u j + 1) (c + 2) 2 []
  have dExtends : withD <+: next := (emit_extends ..).trans withGuardExtends
  have dBound : state.length < (BMS.parentTable (d + 2) (matrix withD)).length := by
    rw [table_length]; simp only [withD, emit_length]; omega
  have dToH : ∀ j, j < d → Parents.Ancestor (BMS.parentTable (d + 2) (matrix next)) j
      state.length (state.length + 1) := by
    intro j room
    exact (Parents.Ancestor.up (guard_numerical_parents state u c j room) (.refl _)).prefix
      (table_prefix withGuardExtends)
  have fence := (dToH 0 positive).trans scope.fence
  have parents : ∀ j, j < d → Parents.parent (BMS.parentTable (d + 2) (matrix
      (emit next (fun j => u j + 1) (c + 2) 0 frame))) j next.length = some state.length := by
    intro j room
    apply auxiliary_numerical_parents next _ (c + 2) 0 frame state.length scope.nonempty fence
      (fun k inside => ?_) j room
    rw [← Parents.reading_prefix (table_prefix dExtends) k state.length dBound]
    rw [emitted_numerical_value state u (c + 1) 1 [] k inside]
  apply view.append_stretched _ (Parents.context_valid_append_label d source sourceValid coordinates)
    (table_prefix (scope.extended.trans (emit_extends ..))) next.length
    (by rw [table_length, emit_length]; omega) (by rw [table_length, emit_length])
    (by rw [table_length]; exact scope.extended.length_le)
  intro j room p selected
  exact .up (parents j room)
    ((emitted_source_parent_path state sourceCoherent sourceValid view coordinates (c + 1) 1 []
      j p room selected).prefix (table_prefix (dExtends.trans (emit_extends ..))))

end BTnSSBMS.Encoder
