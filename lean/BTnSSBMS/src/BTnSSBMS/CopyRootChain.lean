import BTnSSBMS.SBCopyAncestry

/-! Successive actual roots retain a lower-row ancestry chain. This is
a numerical seam lemma, not an assertion about arbitrary copied pairs. -/
namespace BTnSSBMS.Source

theorem ShiftView.next_root_retains_previous_root {d root cap phase : Nat}
    {source target : ParentContext} {visible history delta : List Nat}
    (scope : ShiftView d source target visible history root cap delta phase)
    (terminal : List Nat) (width : terminal.length = d)
    (terminalUnit : Parents.UnitSteps d (source ++ [Parents.label d source terminal]))
    (rootWidth : (source[root]?.getD default).coordinates.length = d)
    (room : cap < d) (selected : (Parents.label d source terminal).parents[cap]?.join = some root)
    (difference : ∀ row, row < cap → terminal[row]?.getD 0 =
      Parents.reading source row root + delta[row]?.getD 0)
    {row : Nat} (low : row < cap) :
    Parents.Ancestor (target ++ [Parents.label d target
      (shift (source[root]?.getD default).coordinates cap delta (phase + 1))])
      row (Parents.point visible root) target.length := by
  let current := shift terminal cap delta phase
  let next := shift (source[root]?.getD default).coordinates cap delta (phase + 1)
  have threshold := Keys.threshold_at_selected_root scope.sourceCoherent scope.sourceValid
    scope.historyCorrect scope.historyLength scope.afterRoot room terminal selected
  have transported := scope.head_parents terminal width terminalUnit cap room
  rw [threshold, selected, Option.map_some] at transported
  have path : Parents.Ancestor (target ++ [Parents.label d target current]) cap
      (Parents.point visible root) target.length := by
    exact .up (by rw [Parents.append_label_parent]; exact transported) (.refl _)
  have lower := path.lower_row (Parents.coherent_append_label scope.targetCoherent current)
    room (Nat.le_of_lt low)
  have oldParents := scope.head_parents terminal width terminalUnit row (by omega)
  rw [threshold] at oldParents
  have newParents := scope.next_head_parents terminal width terminalUnit rootWidth room selected
    difference row (by omega)
  rw [if_pos low] at newParents
  exact lower.replace_last scope.targetValid current next (scope.view.bounded root scope.afterRoot)
    (oldParents.trans newParents.symm)

end BTnSSBMS.Source
