import BTnSSBMS.SBCopyHoleBarrier
import BTnSSBMS.ExactCopyBarrierPath
import BTnSSBMS.SBCopyBarrierPosition

/-!
Ordinary positions in one copy cannot be SB partners of the next copy's
terminal when the tested row equals the copy class. Both actual nested
hole contexts, the restart and the intervening-root ancestry are derived.
This does not cover forced-root pairs, other copy classes or donated forests.
-/
namespace BTnSSBMS.Source

theorem consecutive_copies_terminal_no_ordinary_SB {d : Nat}
    {context target : ParentContext} {a : List Nat} {visible : List Nat}
    {cap : Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d (context ++ [Parents.label d context a])
      (target ++ [Parents.label d target (shift a cap delta phase)]) visible
      (List.replicate context.length 0 ++ [cap]) context.length cap delta phase)
    (hs : Forests (List Nat)) (rest : NumericalExpr)
    (legal : FiniteLegal d context (.cons a hs rest)) (depth : Nat) {site : HoleSite}
    (found : holeSite d context none depth (.cons a hs rest) = some site)
    (positive : 0 < cap) (room : cap < d)
    (selected : (Parents.label d site.context site.terminal).parents[cap]?.join = some context.length)
    (difference : ∀ row, row < cap →
      site.terminal[row]?.getD 0 = a[row]?.getD 0 + delta[row]?.getD 0) :
    ∃ oldHole newHole oldVisible,
      holeSite d target none depth
        (copied d context.length cap delta phase context (List.replicate context.length 0)
          (.cons a hs rest)) = some oldHole ∧
      holeSite d oldHole.context none depth
        (copied d context.length cap delta (phase + 1) context (List.replicate context.length 0)
          (.cons a hs rest)) = some newHole ∧
      Parents.NumericalView d site.context oldHole.context oldVisible ∧
      ∀ position, context.length < position → position < site.context.length →
        Parents.Ancestor (newHole.context ++ [Parents.label d newHole.context newHole.terminal])
          (cap - 1) (Parents.point oldVisible position) newHole.context.length →
        (Parents.label d newHole.context newHole.terminal).parents[cap]?.join ≠
          Parents.parent newHole.context cap (Parents.point oldVisible position) := by
  have later := Parents.label_parent_bound d site.context site.terminal cap context.length selected
  have coordinates := holeSite_root_coordinates found later
  have rootTake := holeSite_root_take found later
  have sourceHole := (holeSite_finiteLegal depth (.cons a hs rest) legal
    (by intro bound impossible; cases impossible) found).1
  have rootWidth : (site.context[context.length]?.getD default).coordinates.length = d := by
    rw [coordinates]
    exact legal.1
  have actualDifference : ∀ row, row < cap → site.terminal[row]?.getD 0 =
      Parents.reading site.context row context.length + delta[row]?.getD 0 := by
    intro row below
    change site.terminal[row]?.getD 0 =
      (site.context[context.length]?.getD default).coordinates[row]?.getD 0 + delta[row]?.getD 0
    rw [coordinates]
    exact difference row below
  obtain ⟨oldHole, oldFound, oldHoleView⟩ :=
    copied_root_holeSite_exact scope hs rest legal depth found later
  obtain ⟨oldVisible, oldHistory, _, oldScope, oldExact, _, _⟩ := oldHoleView
  have restart := oldScope.restart site.terminal sourceHole.1 sourceHole.2.1
    rootWidth room selected actualDifference
  dsimp only at restart
  rw [rootTake, coordinates] at restart
  obtain ⟨newHole, newFound, newHoleView⟩ :=
    copied_root_holeSite_exact restart hs rest legal depth found later
  obtain ⟨newVisible, newHistory, newPrefix, newScope, newExact, terminalEq, _⟩ := newHoleView
  have fullScope := newScope.append site.terminal sourceHole.1 sourceHole.2.1
  have fullExact := newScope.exact_after_append newExact site.terminal sourceHole.1 sourceHole.2.1
  dsimp only at fullScope fullExact terminalEq
  rw [← terminalEq] at fullScope fullExact
  have rootPoint : Parents.point newVisible context.length = oldHole.context.length := by
    rw [← Parents.point_prefix newPrefix context.length (by
      rw [restart.view.length]
      simp)]
    exact root_view_point restart
  have targetLater : oldHole.context.length < newHole.context.length := by
    rw [← rootPoint]
    exact newScope.view.bounded context.length later
  have newFoundRoot := newFound
  rw [copied_at_root] at newFoundRoot
  have initial := holeSite_after_head newFoundRoot targetLater
  have actualInitial : oldHole.context ++ [Parents.label d oldHole.context
      (shift (site.context[context.length]?.getD default).coordinates cap delta (phase + 1))] <+:
      newHole.context := by
    simpa only [coordinates] using initial
  have endpointPoint : Parents.point (newVisible ++ [newHole.context.length]) site.context.length =
      newHole.context.length := by
    rw [← newScope.view.length, Parents.point_append_last]
  refine ⟨oldHole, newHole, oldVisible, oldFound, newFound, oldScope.view, ?_⟩
  intro position after inside oldPath
  have through := oldScope.view.restarted_gap_path fullScope.view fullScope.sourceValid fullScope.targetValid
    after inside (by omega : cap - 1 < d) fullExact
    (newPrefix.trans (List.prefix_append _ _))
    (by omega : context.length ≤ site.context.length) (by simp)
    (by simpa only [endpointPoint] using oldPath)
  rw [endpointPoint] at through
  exact oldScope.next_root_shared_parent_excluded_of_ancestry site.terminal sourceHole.1 sourceHole.2.1
    rootWidth positive room selected actualDifference oldExact after inside actualInitial
    newScope.targetCoherent newScope.targetValid newHole.terminal fullScope.targetUnit oldPath through

/-- The same exclusion covers every visible position of the next
copy, not just its terminal. The new forced root may be the endpoint;
the earlier position is still required to be an ordinary one. -/
theorem consecutive_copies_visible_no_ordinary_SB {d : Nat}
    {context target : ParentContext} {a : List Nat} {visible : List Nat}
    {cap : Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d (context ++ [Parents.label d context a])
      (target ++ [Parents.label d target (shift a cap delta phase)]) visible
      (List.replicate context.length 0 ++ [cap]) context.length cap delta phase)
    (hs : Forests (List Nat)) (rest : NumericalExpr)
    (legal : FiniteLegal d context (.cons a hs rest)) (depth : Nat) {site : HoleSite}
    (found : holeSite d context none depth (.cons a hs rest) = some site)
    (positive : 0 < cap) (room : cap < d)
    (selected : (Parents.label d site.context site.terminal).parents[cap]?.join = some context.length)
    (difference : ∀ row, row < cap →
      site.terminal[row]?.getD 0 = a[row]?.getD 0 + delta[row]?.getD 0) :
    ∃ oldHole newHole oldVisible newVisible,
      holeSite d target none depth
        (copied d context.length cap delta phase context (List.replicate context.length 0)
          (.cons a hs rest)) = some oldHole ∧
      holeSite d oldHole.context none depth
        (copied d context.length cap delta (phase + 1) context (List.replicate context.length 0)
          (.cons a hs rest)) = some newHole ∧
      Parents.NumericalView d site.context oldHole.context oldVisible ∧
      Parents.NumericalView d site.context newHole.context newVisible ∧
      ∀ position, context.length < position → position < site.context.length →
      ∀ endpoint, context.length ≤ endpoint → endpoint < site.context.length →
        Parents.Ancestor newHole.context (cap - 1)
          (Parents.point oldVisible position) (Parents.point newVisible endpoint) →
        Parents.parent newHole.context cap (Parents.point newVisible endpoint) ≠
          Parents.parent newHole.context cap (Parents.point oldVisible position) := by
  have later := Parents.label_parent_bound d site.context site.terminal cap context.length selected
  have coordinates := holeSite_root_coordinates found later
  have rootTake := holeSite_root_take found later
  have sourceHole := (holeSite_finiteLegal depth (.cons a hs rest) legal
    (by intro bound impossible; cases impossible) found).1
  have rootWidth : (site.context[context.length]?.getD default).coordinates.length = d := by
    rw [coordinates]
    exact legal.1
  have actualDifference : ∀ row, row < cap → site.terminal[row]?.getD 0 =
      Parents.reading site.context row context.length + delta[row]?.getD 0 := by
    intro row below
    change site.terminal[row]?.getD 0 =
      (site.context[context.length]?.getD default).coordinates[row]?.getD 0 + delta[row]?.getD 0
    rw [coordinates]
    exact difference row below
  obtain ⟨oldHole, oldFound, oldHoleView⟩ :=
    copied_root_holeSite_exact scope hs rest legal depth found later
  obtain ⟨oldVisible, oldHistory, _, oldScope, oldExact, _, _⟩ := oldHoleView
  have restart := oldScope.restart site.terminal sourceHole.1 sourceHole.2.1
    rootWidth room selected actualDifference
  dsimp only at restart
  rw [rootTake, coordinates] at restart
  obtain ⟨newHole, newFound, newHoleView⟩ :=
    copied_root_holeSite_exact restart hs rest legal depth found later
  obtain ⟨newVisible, newHistory, newPrefix, newScope, newExact, _, _⟩ := newHoleView
  have rootPoint : Parents.point newVisible context.length = oldHole.context.length := by
    rw [← Parents.point_prefix newPrefix context.length (by
      rw [restart.view.length]
      simp)]
    exact root_view_point restart
  have targetLater : oldHole.context.length < newHole.context.length := by
    rw [← rootPoint]
    exact newScope.view.bounded context.length later
  have newFoundRoot := newFound
  rw [copied_at_root] at newFoundRoot
  have initial := holeSite_after_head newFoundRoot targetLater
  have actualInitial : oldHole.context ++ [Parents.label d oldHole.context
      (shift (site.context[context.length]?.getD default).coordinates cap delta (phase + 1))] <+:
      newHole.context := by
    simpa only [coordinates] using initial
  refine ⟨oldHole, newHole, oldVisible, newVisible, oldFound, newFound, oldScope.view, newScope.view, ?_⟩
  intro position after inside endpoint endpointAfter endpointInside oldPath
  have through := oldScope.view.restarted_gap_path newScope.view newScope.sourceValid newScope.targetValid
    after inside (by omega : cap - 1 < d) newExact newPrefix endpointAfter endpointInside oldPath
  exact oldScope.next_root_shared_parent_excluded_at_position site.terminal sourceHole.1 sourceHole.2.1
    rootWidth positive room selected actualDifference oldExact after inside actualInitial
    newScope.targetCoherent newScope.targetValid newScope.targetUnit
    (newScope.view.bounded endpoint endpointInside) oldPath through

end BTnSSBMS.Source
