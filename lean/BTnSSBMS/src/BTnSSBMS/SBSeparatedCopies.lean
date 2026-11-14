import BTnSSBMS.SBConsecutiveIntervals
import BTnSSBMS.CopyRunBarrierPath

/-! Same-class SB exclusion across any finite number of intervening
copies. All copied holes, reset views, protected prefixes, root paths and
position preimages are constructed. Earlier forced roots, other classes
and donation are deliberately not claimed here. -/
namespace BTnSSBMS.Source

theorem separated_copies_interval_no_ordinary_SB {d : Nat}
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
      site.terminal[row]?.getD 0 = a[row]?.getD 0 + delta[row]?.getD 0) (count : Nat) :
    ∃ oldHole laterTarget newHole,
      holeSite d target none depth
        (copied d context.length cap delta phase context (List.replicate context.length 0)
          (.cons a hs rest)) = some oldHole ∧
      copyHoleAfter d cap delta context (.cons a hs rest) depth count (phase + 1) oldHole.context =
        some laterTarget ∧
      holeSite d laterTarget none depth
        (copied d context.length cap delta (phase + 1 + count) context (List.replicate context.length 0)
          (.cons a hs rest)) = some newHole ∧
      ∀ earlier, target.length < earlier → earlier < oldHole.context.length →
      ∀ endpoint, laterTarget.length ≤ endpoint → endpoint ≤ newHole.context.length →
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
  obtain ⟨laterTarget, laterVisible, run, laterEntry, fixed, protectedPrefix, roots⟩ :=
    copyHoleAfter_state restart hs rest legal depth found room selected difference count
  have targetPrefix := copyHoleAfter_prefix d cap delta context (.cons a hs rest)
    depth count (phase + 1) oldHole.context run
  obtain ⟨newHole, newFound, newHoleView⟩ :=
    copied_root_holeSite_exact laterEntry hs rest legal depth found later
  obtain ⟨newVisible, newHistory, newPrefix, newScope, newExact, terminalEq, _⟩ := newHoleView
  have newDensity := copied_root_hole_density laterEntry hs rest depth found newFound later newScope.view newPrefix
  have fullScope := newScope.append site.terminal sourceHole.1 sourceHole.2.1
  have fullExact := newScope.exact_after_append newExact site.terminal sourceHole.1 sourceHole.2.1
  dsimp only at fullScope fullExact terminalEq
  rw [← terminalEq] at fullScope fullExact
  have rootPoint : Parents.point (newVisible ++ [newHole.context.length]) context.length = laterTarget.length := by
    rw [Parents.point_append_old _ context.length newHole.context.length (by rw [newScope.view.length]; exact later)]
    exact newDensity.1
  have sizes := copied_root_holeSite_span d cap delta (phase + 1 + count) context laterTarget a hs rest
    depth found newFound
  have span : (newHole.context ++ [Parents.label d newHole.context newHole.terminal]).length + context.length =
      (site.context ++ [Parents.label d site.context site.terminal]).length +
        Parents.point (newVisible ++ [newHole.context.length]) context.length := by
    rw [rootPoint]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have fullFixed : (newVisible ++ [newHole.context.length]).take context.length =
      oldVisible.take context.length := by
    rw [take_visible_prefix (List.prefix_append _ _) (by rw [newScope.view.length]; omega),
      take_visible_prefix newPrefix (by rw [laterEntry.view.length]; simp), fixed]
    have takeLength : (oldVisible.take context.length).length = context.length := by
      simp only [List.length_take, oldScope.view.length]
      omega
    rw [List.take_append_of_le_length (by omega : context.length ≤ (oldVisible.take context.length).length),
      List.take_take, Nat.min_self]
  have targetLater : laterTarget.length < newHole.context.length := by
    rw [← newDensity.1]
    exact newScope.view.bounded context.length later
  have newFoundRoot := newFound
  rw [copied_at_root] at newFoundRoot
  have initial := holeSite_after_head newFoundRoot targetLater
  have fullInitial := initial.trans (List.prefix_append newHole.context [Parents.label d newHole.context newHole.terminal])
  have actualInitial : oldHole.context ++ [Parents.label d oldHole.context
      (shift (site.context[context.length]?.getD default).coordinates cap delta (phase + 1))] <+:
      newHole.context ++ [Parents.label d newHole.context newHole.terminal] := by
    simpa only [coordinates] using protectedPrefix.trans fullInitial
  refine ⟨oldHole, laterTarget, newHole, oldFound, run, newFound, ?_⟩
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
  have currentRootPath := oldScope.view.later_gap_path fullScope.view fullScope.sourceValid fullScope.targetValid
    positionStrict positionInside (by omega : cap - 1 < d) fullExact fullFixed
    (by rw [rootPoint]; exact targetPrefix.length_le) sourceAfter sourceInside mappedPath
  rw [rootPoint, endpointEq] at currentRootPath
  have firstRootPath := ((roots (cap - 1) (by omega)).prefix fullInitial).trans currentRootPath
  have excluded := oldScope.next_root_shared_parent_excluded_at_position site.terminal sourceHole.1 sourceHole.2.1
    rootWidth positive room selected actualDifference oldExact positionStrict positionInside actualInitial
    fullScope.targetCoherent fullScope.targetValid fullScope.targetUnit
    (endpoint := endpoint) (by simp; omega) (by simpa only [positionEq] using oldPath) firstRootPath
  simpa only [positionEq] using excluded

end BTnSSBMS.Source
