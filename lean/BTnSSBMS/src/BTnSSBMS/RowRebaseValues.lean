import BTnSSBMS.RowRebaseTrace

/-! Numerical coupling at the visible source representatives. The
shift is tested in the old actual output, not in source coordinates. -/
namespace BTnSSBMS.Encoder

def RowRebaseValues (j root amount count : Nat) (moved visible nextVisible : List Nat)
    (state next : State d) : Prop :=
  ∀ p, p < count →
    Parents.reading (BMS.parentTable (d + 2) (matrix next)) j
      (Parents.point nextVisible (Parents.point moved p)) =
    Parents.reading (BMS.parentTable (d + 2) (matrix state)) j (Parents.point visible p) +
      rowBump state j root amount (Parents.point visible p)

theorem rowBump_self (state : State d) (j root amount : Nat) :
    rowBump state j root amount root = amount := by
  classical
  simp only [rowBump, Parents.Ancestor.refl, if_true]

theorem rowBump_future (state : State d) (j root amount p : Nat) (before : p < root) :
    rowBump state j root amount p = 0 := by
  classical
  have impossible : ¬ Parents.Ancestor (BMS.parentTable (d + 2) (matrix state)) j root p := by
    intro path
    have prior := path.le (BMS.parentTable_valid _ _)
    omega
  simp only [rowBump, impossible, if_false]

theorem fixed_prefix_row_values {state next : State d} {visible nextVisible : List Nat} {count : Nat}
    (visibleLength : visible.length = count) (visiblePrefix : visible <+: nextVisible)
    (statePrefix : state <+: next)
    (bounded : ∀ p, p < count → Parents.point visible p < state.length)
    (j amount : Nat) :
    RowRebaseValues j state.length amount count (List.range count) visible nextVisible state next := by
  intro p inside
  have rangePoint : Parents.point (List.range count) p = p := by
    simp only [Parents.point, List.getElem?_range inside, Option.getD_some]
  obtain ⟨extra, rfl⟩ := visiblePrefix
  rw [rangePoint]
  have same : Parents.point (visible ++ extra) p = Parents.point visible p := by
    simp only [Parents.point, List.getElem?_append_left (show p < visible.length by omega)]
  rw [same, ← Parents.reading_prefix (table_prefix statePrefix) j (Parents.point visible p)
    (by rw [table_length]; exact bounded p inside), rowBump_future state j state.length amount _ (bounded p inside)]
  omega

theorem RowRebaseValues.extends {j root amount count : Nat} {moved visible nextVisible : List Nat}
    {state next result newResult : State d}
    (values : RowRebaseValues j root amount count moved visible nextVisible state next)
    (oldBound : ∀ p, p < count → Parents.point visible p < state.length)
    (newBound : ∀ p, p < count → Parents.point nextVisible (Parents.point moved p) < next.length)
    (oldPrefix : state <+: result) (newPrefix : next <+: newResult) :
    RowRebaseValues j root amount count moved visible nextVisible result newResult := by
  intro p inside
  rw [← Parents.reading_prefix (table_prefix oldPrefix) j (Parents.point visible p)
      (by rw [table_length]; exact oldBound p inside),
    ← Parents.reading_prefix (table_prefix newPrefix) j (Parents.point nextVisible (Parents.point moved p))
      (by rw [table_length]; exact newBound p inside),
    rowBump_prefix oldPrefix j root amount (Parents.point visible p) (oldBound p inside)]
  exact values p inside

theorem RowRebaseValues.append {j root amount count : Nat} {moved visible nextVisible : List Nat}
    {state next : State d}
    (values : RowRebaseValues j root amount count moved visible nextVisible state next)
    (movedLength : moved.length = count) (visibleLength : visible.length = count)
    (mappedBound : ∀ p, p < count → Parents.point moved p < nextVisible.length)
    (oldPosition newPosition : Nat)
    (last : Parents.reading (BMS.parentTable (d + 2) (matrix next)) j newPosition =
      Parents.reading (BMS.parentTable (d + 2) (matrix state)) j oldPosition +
        rowBump state j root amount oldPosition) :
    RowRebaseValues j root amount (count + 1) (moved ++ [nextVisible.length])
      (visible ++ [oldPosition]) (nextVisible ++ [newPosition]) state next := by
  intro p inside
  by_cases old : p < count
  · rw [Parents.point_append_old moved p nextVisible.length (by omega),
      Parents.point_append_old nextVisible (Parents.point moved p) newPosition (mappedBound p old),
      Parents.point_append_old visible p oldPosition (by omega)]
    exact values p old
  · have same : p = count := by omega
    subst p
    rw [← movedLength, Parents.point_append_last, movedLength,
      Parents.point_append_last, ← visibleLength, Parents.point_append_last]
    exact last

theorem RowRebaseValues.head_values {d : Nat} {source target : ParentContext}
    {moved visible nextVisible : List Nat} {state next : State d} {j root amount : Nat}
    (values : RowRebaseValues j root amount source.length moved visible nextVisible state next)
    (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
    (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
    (view : Parents.NumericalView d source target moved)
    (oldView : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (newView : Parents.NumericalView d target (BMS.parentTable (d + 2) (matrix next)) nextVisible)
    (coordinates : List Nat) (height tag : Nat) (frame : List Binding)
    (room : j < d) (rootBefore : root < state.length) :
    vector next nextVisible (Parents.label d target (Source.relocationHead d source target moved coordinates)) j =
      vector state visible (Parents.label d source coordinates) j +
        rowBump (emit state (vector state visible (Parents.label d source coordinates)) height tag frame)
          j root amount state.length := by
  have actual : Parents.parent (BMS.parentTable (d + 2) (matrix
      (emit state (vector state visible (Parents.label d source coordinates)) height tag frame))) j state.length =
        ((Parents.label d source coordinates).parents[j]?.join).map (Parents.point visible) := by
    rw [emitted_parent, emitted_head_numerical_parents state sourceCoherent sourceValid oldView
      coordinates height tag j room, representative_eq_point oldView]
  rw [vector_eq_represented newView, vector_eq_represented oldView]
  simp only [Parents.representedValue,
    Source.relocationHead_parents sourceCoherent sourceValid targetCoherent targetValid view coordinates j room]
  cases selected : (Parents.label d source coordinates).parents[j]?.join with
  | none =>
    simp only [selected, Option.map_none] at actual
    rw [rowBump_missing (by omega) actual]
    simp
  | some p =>
    have inside := Parents.label_parent_bound d source coordinates j p selected
    have oldBound : Parents.point visible p < state.length := by
      simpa only [table_length] using oldView.bounded p inside
    simp only [selected, Option.map_some] at actual
    rw [rowBump_parent (by omega) actual, rowBump_prefix (emit_extends ..) j root amount _ oldBound]
    simp only [Option.map_some, Option.getD_some]
    rw [values p inside]
    omega

theorem rowBump_guard (state : State d) (u : Nat → Nat) (c j root amount : Nat)
    (room : j < d) (rootBefore : root ≤ state.length) :
    rowBump (emit (emit state u (c + 1) 1 []) (fun k => u k + 1) (c + 2) 2 [])
      j root amount (state.length + 1) =
    rowBump (emit state u (c + 1) 1 []) j root amount state.length := by
  rw [rowBump_parent (by omega) (guard_numerical_parents state u c j room)]
  exact rowBump_prefix (emit_extends ..) j root amount state.length (by rw [emit_length]; omega)

theorem NumericalGate.rowBump_slot {d : Nat} {source : ParentContext} {coordinates visible : List Nat}
    {original state : State d} {u : Nat → Nat} {gate : Nat}
    (scope : NumericalGate d source coordinates visible original state u gate)
    (height : Nat) (frame : List Binding) (j root amount : Nat)
    (room : j < d) (rootBefore : root < state.length) :
    rowBump (emit state (fun k => u k + 2) height 0 frame) j root amount state.length =
      rowBump state j root amount gate := by
  rw [rowBump_parent (by omega) (scope.slot_parents height frame j room)]
  exact rowBump_prefix (emit_extends ..) j root amount gate scope.bounded

theorem NumericalGate.closing_parents {d : Nat} {source : ParentContext} {coordinates visible : List Nat}
    {original state : State d} {c : Nat}
    (scope : NumericalGate d source coordinates visible original state
      (vector original visible (Parents.label d source coordinates)) (original.length + 1))
    (guardPrefix : emit (emit original (vector original visible (Parents.label d source coordinates)) (c + 1) 1 [])
      (fun k => vector original visible (Parents.label d source coordinates) k + 1) (c + 2) 2 [] <+: state)
    (positive : 0 < d) (height tag : Nat) (frame : List Binding) :
    ∀ j, j < d → Parents.parent (BMS.parentTable (d + 2) (matrix
      (emit state (fun k => vector original visible (Parents.label d source coordinates) k + 1) height tag frame)))
      j state.length = some original.length := by
  let u := vector original visible (Parents.label d source coordinates)
  have definitionPrefix : emit original u (c + 1) 1 [] <+: state := (emit_extends ..).trans guardPrefix
  have fence : Parents.Ancestor (BMS.parentTable (d + 2) (matrix state)) 0 original.length (state.length - 1) :=
    ((Parents.Ancestor.up (guard_numerical_parents original u c 0 positive) (.refl _)).prefix
      (table_prefix guardPrefix)).trans scope.fence
  intro j room
  apply auxiliary_numerical_parents state _ height tag frame original.length scope.nonempty fence
    (fun k inside => ?_) j room
  rw [← Parents.reading_prefix (table_prefix definitionPrefix) k original.length
    (by rw [table_length, emit_length]; omega), emitted_numerical_value original u (c + 1) 1 [] k inside]

end BTnSSBMS.Encoder
