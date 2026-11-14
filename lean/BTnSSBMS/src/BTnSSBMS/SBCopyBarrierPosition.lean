import BTnSSBMS.SBCopyAncestry

/-! The same-class barrier for an arbitrary visible later position,
including the new forced root itself, rather than only an appended head. -/
namespace BTnSSBMS.Source

theorem ShiftView.next_root_shared_parent_excluded_at_position {d root cap phase : Nat}
    {source target later : ParentContext} {visible history delta : List Nat}
    (scope : ShiftView d source target visible history root cap delta phase)
    (terminal : List Nat) (width : terminal.length = d)
    (terminalUnit : Parents.UnitSteps d (source ++ [Parents.label d source terminal]))
    (rootWidth : (source[root]?.getD default).coordinates.length = d)
    (positive : 0 < cap) (room : cap < d)
    (selected : (Parents.label d source terminal).parents[cap]?.join = some root)
    (difference : ∀ row, row < cap → terminal[row]?.getD 0 =
      Parents.reading source row root + delta[row]?.getD 0)
    (exactAt : ∀ position, root < position → position < source.length →
      Parents.ExactPosition d source target visible position)
    {position : Nat} (after : root < position) (inside : position < source.length)
    (initial : target ++ [Parents.label d target
      (shift (source[root]?.getD default).coordinates cap delta (phase + 1))] <+: later)
    (coherent : Parents.Coherent d later) (valid : Parents.ContextValid later)
    (unit : Parents.UnitSteps d later) {endpoint : Nat} (endpointInside : endpoint < later.length)
    (oldPath : Parents.Ancestor later (cap - 1) (Parents.point visible position) endpoint)
    (rootPath : Parents.Ancestor later (cap - 1) target.length endpoint) :
    Parents.parent later cap endpoint ≠ Parents.parent later cap (Parents.point visible position) := by
  intro shared
  have oldInside := scope.view.bounded position inside
  have between := oldPath.between valid rootPath (by omega)
  have restricted := between.restrict initial valid (by simp)
  have sourcePath := scope.next_root_ancestor_reflect terminal width terminalUnit rootWidth room selected
    difference exactAt after inside (by omega : cap - 1 < cap) restricted
  have rowEq : cap - 1 + 1 = cap := by omega
  have sourceCoherent := Parents.coherent_append_label scope.sourceCoherent terminal
  have sourceValid := Parents.context_valid_append_label d source scope.sourceValid terminal
  have sourceEdge : Parents.parent (source ++ [Parents.label d source terminal]) cap source.length = some root := by
    rw [Parents.append_label_parent]
    exact selected
  have terminalHigher := Parents.parent_reading_lt sourceCoherent sourceEdge
  have pathFloor := Parents.parent_chain_barrier sourceCoherent sourceValid (row := cap - 1)
    (by omega) (by simpa only [rowEq] using sourceEdge) sourcePath after
  rw [rowEq] at pathFloor
  have sourceHigher : Parents.reading source cap root < Parents.reading source cap position := by
    rw [← Parents.reading_prefix (List.prefix_append source [Parents.label d source terminal])
      cap root scope.afterRoot] at terminalHigher
    rw [← Parents.reading_prefix (List.prefix_append source [Parents.label d source terminal])
      cap position inside] at pathFloor
    omega
  have targetPrefix : target <+: later := (List.prefix_append _ _).trans initial
  have oldValue : Parents.reading later cap (Parents.point visible position) =
      Parents.reading source cap position := by
    rw [← Parents.reading_prefix targetPrefix cap (Parents.point visible position) oldInside]
    exact scope.unshifted_row inside room (Nat.le_refl cap)
  have barrierValue : Parents.reading later cap target.length = Parents.reading source cap root := by
    rw [← Parents.reading_prefix initial cap target.length (by simp), Parents.reading_append_label,
      shift_unshifted_row _ _ cap (phase + 1) cap (Nat.le_refl cap) (by rw [rootWidth]; exact room)]
    rfl
  have oldLater : Parents.point visible position < later.length := by
    have bound := targetPrefix.length_le
    omega
  have lower : Parents.reading later cap (Parents.point visible position) ≤
      Parents.reading later cap target.length := by
    by_cases same : endpoint = target.length
    · have equal := unit.shared_parent_reading room oldLater endpointInside shared.symm
      rw [same] at equal
      exact Nat.le_of_eq equal
    · have result := Parents.shared_parent_barrier_floor_left coherent valid unit
        (row := cap - 1) (by omega) endpointInside oldInside (by omega) rootPath
        (by simpa only [rowEq] using shared.symm)
      simpa only [rowEq] using result
  rw [oldValue, barrierValue] at lower
  omega

end BTnSSBMS.Source
