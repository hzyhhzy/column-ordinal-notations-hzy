import BTnSSBMS.SBConsecutiveCopies
import BTnSSBMS.CopyHoleDensity

/-! Same-class SB exclusion on entire actual visible intervals of two
successive copies. The second interval includes its forced root and its
terminal. No position-map surjectivity is a premise. This does not cover
an earlier forced root, different classes, or donated material. -/
namespace BTnSSBMS.Source

theorem consecutive_copies_interval_no_ordinary_SB {d : Nat}
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
    ∃ oldHole newHole,
      holeSite d target none depth
        (copied d context.length cap delta phase context (List.replicate context.length 0)
          (.cons a hs rest)) = some oldHole ∧
      holeSite d oldHole.context none depth
        (copied d context.length cap delta (phase + 1) context (List.replicate context.length 0)
          (.cons a hs rest)) = some newHole ∧
      ∀ earlier, target.length < earlier → earlier < oldHole.context.length →
      ∀ endpoint, oldHole.context.length ≤ endpoint → endpoint ≤ newHole.context.length →
        Parents.Ancestor (newHole.context ++ [Parents.label d newHole.context newHole.terminal])
          (cap - 1) earlier endpoint →
        Parents.parent (newHole.context ++ [Parents.label d newHole.context newHole.terminal]) cap endpoint ≠
          Parents.parent (newHole.context ++ [Parents.label d newHole.context newHole.terminal]) cap earlier := by
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
  obtain ⟨oldVisible, oldHistory, oldPrefix, oldScope, oldExact, _, _⟩ := oldHoleView
  have oldDensity := copied_root_hole_density scope hs rest depth found oldFound later oldScope.view oldPrefix
  have restart := oldScope.restart site.terminal sourceHole.1 sourceHole.2.1
    rootWidth room selected actualDifference
  dsimp only at restart
  rw [rootTake, coordinates] at restart
  obtain ⟨newHole, newFound, newHoleView⟩ :=
    copied_root_holeSite_exact restart hs rest legal depth found later
  obtain ⟨newVisible, newHistory, newPrefix, newScope, newExact, terminalEq, _⟩ := newHoleView
  have newDensity := copied_root_hole_density restart hs rest depth found newFound later newScope.view newPrefix
  have fullScope := newScope.append site.terminal sourceHole.1 sourceHole.2.1
  have fullExact := newScope.exact_after_append newExact site.terminal sourceHole.1 sourceHole.2.1
  dsimp only at fullScope fullExact terminalEq
  rw [← terminalEq] at fullScope fullExact
  have rootPoint : Parents.point (newVisible ++ [newHole.context.length]) context.length =
      oldHole.context.length := by
    rw [Parents.point_append_old _ context.length newHole.context.length (by rw [newScope.view.length]; exact later)]
    exact newDensity.1
  have sizes := copied_root_holeSite_span d cap delta (phase + 1) context oldHole.context a hs rest
    depth found newFound
  have span : (newHole.context ++ [Parents.label d newHole.context newHole.terminal]).length + context.length =
      (site.context ++ [Parents.label d site.context site.terminal]).length +
        Parents.point (newVisible ++ [newHole.context.length]) context.length := by
    rw [rootPoint]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have targetLater : oldHole.context.length < newHole.context.length := by
    rw [← newDensity.1]
    exact newScope.view.bounded context.length later
  have newFoundRoot := newFound
  rw [copied_at_root] at newFoundRoot
  have initial := holeSite_after_head newFoundRoot targetLater
  have actualInitial : oldHole.context ++ [Parents.label d oldHole.context
      (shift (site.context[context.length]?.getD default).coordinates cap delta (phase + 1))] <+:
      newHole.context ++ [Parents.label d newHole.context newHole.terminal] := by
    apply List.IsPrefix.trans ?_ (List.prefix_append _ _)
    simpa only [coordinates] using initial
  refine ⟨oldHole, newHole, oldFound, newFound, ?_⟩
  intro earlier earlierAfter earlierInside endpoint endpointAfter endpointInside oldPath
  obtain ⟨position, positionAfter, positionInside, positionEq⟩ :=
    oldDensity.2.2 earlier (by omega) earlierInside
  have positionStrict : context.length < position := by
    by_cases same : position = context.length
    · rw [same, oldDensity.1] at positionEq
      omega
    · omega
  obtain ⟨sourceEndpoint, sourceAfter, sourceInside, endpointEq⟩ :=
    fullScope.view.surjective_from_span (root := context.length) (by simp; omega) span
      (by simpa only [rootPoint] using endpointAfter) (by simp; omega)
  have mappedPath := oldPath
  rw [← positionEq, ← endpointEq] at mappedPath
  have through := oldScope.view.restarted_gap_path fullScope.view fullScope.sourceValid fullScope.targetValid
    positionStrict positionInside (by omega : cap - 1 < d) fullExact
    (newPrefix.trans (List.prefix_append _ _)) sourceAfter sourceInside mappedPath
  rw [endpointEq] at through
  have excluded := oldScope.next_root_shared_parent_excluded_at_position site.terminal sourceHole.1 sourceHole.2.1
    rootWidth positive room selected actualDifference oldExact positionStrict positionInside actualInitial
    fullScope.targetCoherent fullScope.targetValid fullScope.targetUnit
    (endpoint := endpoint) (by simp; omega) (by simpa only [positionEq] using oldPath) through
  simpa only [positionEq] using excluded

end BTnSSBMS.Source
