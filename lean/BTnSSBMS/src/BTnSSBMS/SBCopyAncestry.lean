import BTnSSBMS.ExactAncestryReflection
import BTnSSBMS.SBCopyBarrier

/-!
Reflection through the actual next-phase root eliminates the assumed
source-path premise from the same-class cross-copy exclusion. Exactness
is required only at ordinary positions above the forced source root.
These position witnesses are constructed for actual copied outer entries
by ExactRelocationEntries; full nested seam classification remains open.
-/
namespace BTnSSBMS.Source

theorem ShiftView.next_head_parents {d root cap phase : Nat}
    {source target : ParentContext} {visible history delta : List Nat}
    (scope : ShiftView d source target visible history root cap delta phase)
    (terminal : List Nat) (width : terminal.length = d)
    (terminalUnit : Parents.UnitSteps d (source ++ [Parents.label d source terminal]))
    (rootWidth : (source[root]?.getD default).coordinates.length = d)
    (room : cap < d) (selected : (Parents.label d source terminal).parents[cap]?.join = some root)
    (difference : ∀ row, row < cap → terminal[row]?.getD 0 =
      Parents.reading source row root + delta[row]?.getD 0)
    (row : Nat) (rowRoom : row < d) :
    (Parents.label d target
      (shift (source[root]?.getD default).coordinates cap delta (phase + 1))).parents[row]?.join =
      if row < cap then ((Parents.label d source terminal).parents[row]?.join).map (Parents.point visible)
      else Parents.parent target row (Parents.point visible root) := by
  have threshold := Keys.threshold_at_selected_root scope.sourceCoherent scope.sourceValid
    scope.historyCorrect scope.historyLength scope.afterRoot room terminal selected
  have chosen : (Parents.label d target (shift terminal cap delta phase)).parents[cap]?.join =
      some (Parents.point visible root) := by
    have transported := scope.head_parents terminal width terminalUnit cap room
    rw [threshold, selected, Option.map_some] at transported
    exact transported
  have values := scope.next_head_values terminal width rootWidth room difference
  have computed := Parents.first_copy_head_parents scope.targetCoherent scope.targetValid
    (shift terminal cap delta phase)
    (shift (source[root]?.getD default).coordinates cap delta (phase + 1))
    room chosen values.1 values.2 row rowRoom
  rw [computed]
  by_cases low : row < cap
  · rw [if_pos low, if_pos low]
    have ordinary := scope.head_parents terminal width terminalUnit row rowRoom
    rw [threshold] at ordinary
    exact ordinary
  · rw [if_neg low, if_neg low]

theorem ShiftView.next_root_ancestor_reflect {d root cap phase : Nat}
    {source target : ParentContext} {visible history delta : List Nat}
    (scope : ShiftView d source target visible history root cap delta phase)
    (terminal : List Nat) (width : terminal.length = d)
    (terminalUnit : Parents.UnitSteps d (source ++ [Parents.label d source terminal]))
    (rootWidth : (source[root]?.getD default).coordinates.length = d)
    (room : cap < d) (selected : (Parents.label d source terminal).parents[cap]?.join = some root)
    (difference : ∀ row, row < cap → terminal[row]?.getD 0 =
      Parents.reading source row root + delta[row]?.getD 0)
    (exactAt : ∀ position, root < position → position < source.length →
      Parents.ExactPosition d source target visible position)
    {position row : Nat} (after : root < position) (inside : position < source.length) (low : row < cap)
    (path : Parents.Ancestor (target ++ [Parents.label d target
      (shift (source[root]?.getD default).coordinates cap delta (phase + 1))])
      row (Parents.point visible position) target.length) :
    Parents.Ancestor (source ++ [Parents.label d source terminal]) row position source.length := by
  let head := shift (source[root]?.getD default).coordinates cap delta (phase + 1)
  have oldInside := scope.view.bounded position inside
  obtain ⟨p, edge, previous⟩ := (Parents.Ancestor.iff_parent (by omega : Parents.point visible position ≠ target.length)).mp path
  rw [Parents.append_label_parent,
    scope.next_head_parents terminal width terminalUnit rootWidth room selected difference row (by omega),
    if_pos low] at edge
  cases oldEdge : (Parents.label d source terminal).parents[row]?.join with
  | none => simp only [oldEdge, Option.map_none] at edge; cases edge
  | some q =>
    have pointEq : Parents.point visible q = p := by
      simpa only [oldEdge, Option.map_some, Option.some.injEq] using edge
    rw [← pointEq] at previous
    have qInside := Parents.label_parent_bound d source terminal row q oldEdge
    have targetPath := previous.restrict (List.prefix_append target [Parents.label d target head])
      (Parents.context_valid_append_label d target scope.targetValid head) (scope.view.bounded q qInside)
    have sourcePath := scope.view.reflect_after scope.sourceValid scope.targetValid root exactAt
      (by omega) after inside qInside targetPath
    exact .up (by rw [Parents.append_label_parent]; exact oldEdge)
      (sourcePath.prefix (List.prefix_append source [Parents.label d source terminal]))

/-- Same-class cross-copy exclusion expressed entirely using actual
target ancestry. No source root-to-terminal path is an input here. -/
theorem ShiftView.next_root_shared_parent_excluded_of_ancestry {d root cap phase : Nat}
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
    (laterCoherent : Parents.Coherent d later) (laterValid : Parents.ContextValid later)
    (a : List Nat) (laterUnit : Parents.UnitSteps d (later ++ [Parents.label d later a]))
    (oldPath : Parents.Ancestor (later ++ [Parents.label d later a])
      (cap - 1) (Parents.point visible position) later.length)
    (rootPath : Parents.Ancestor (later ++ [Parents.label d later a])
      (cap - 1) target.length later.length) :
    (Parents.label d later a).parents[cap]?.join ≠
      Parents.parent later cap (Parents.point visible position) := by
  have oldInside := scope.view.bounded position inside
  have nextValid := Parents.context_valid_append_label d later laterValid a
  have between := oldPath.between nextValid rootPath (by omega)
  have restricted := between.restrict (initial.trans (List.prefix_append later [Parents.label d later a]))
    nextValid (by simp)
  have sourcePath := scope.next_root_ancestor_reflect terminal width terminalUnit rootWidth room selected
    difference exactAt after inside (by omega : cap - 1 < cap) restricted
  exact scope.next_root_shared_parent_excluded terminal positive room rootWidth selected after inside
    sourcePath initial laterCoherent laterValid a laterUnit rootPath

end BTnSSBMS.Source
