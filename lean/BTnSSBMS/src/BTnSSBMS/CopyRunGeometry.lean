import BTnSSBMS.CopyHoleRun

/-! Exact visible growth and stable high-row parents in a finite
sequence of actual copied-hole entries. No block inequality is assumed. -/
namespace BTnSSBMS.Source

theorem copyHoleAfter_length (d cap : Nat) (delta : List Nat) (context target : ParentContext)
    (a : List Nat) (hs : Forests (List Nat)) (rest : NumericalExpr) (depth count phase : Nat)
    {site : HoleSite} (found : holeSite d context none depth (.cons a hs rest) = some site)
    {result : ParentContext}
    (computed : copyHoleAfter d cap delta context (.cons a hs rest) depth count phase target = some result) :
    result.length = target.length + (site.context.length - context.length) * count := by
  induction count generalizing target phase with
  | zero =>
    have same : result = target := by simpa only [copyHoleAfter, Option.some.injEq] using computed.symm
    subst result
    simp
  | succ count ih =>
    simp only [copyHoleAfter] at computed
    cases targetFound : holeSite d target none depth
        (copied d context.length cap delta phase context (List.replicate context.length 0) (.cons a hs rest)) with
    | none => simp only [targetFound] at computed; cases computed
    | some targetSite =>
      simp only [targetFound] at computed
      have later := ih targetSite.context (phase + 1) computed
      have span := copied_root_holeSite_span d cap delta phase context target a hs rest depth found targetFound
      have originalBound := (holeSite_extends d context none depth (.cons a hs rest) found).length_le
      rw [Nat.mul_succ]
      omega

theorem copyHoleAfter_strict_length (d cap : Nat) (delta : List Nat) (context target : ParentContext)
    (a : List Nat) (hs : Forests (List Nat)) (rest : NumericalExpr) (depth count phase : Nat)
    {site : HoleSite} (found : holeSite d context none depth (.cons a hs rest) = some site)
    (later : context.length < site.context.length) (positive : 0 < count) {result : ParentContext}
    (computed : copyHoleAfter d cap delta context (.cons a hs rest) depth count phase target = some result) :
    target.length < result.length := by
  rw [copyHoleAfter_length d cap delta context target a hs rest depth count phase found computed]
  have growth : 0 < (site.context.length - context.length) * count := Nat.mul_pos (by omega) positive
  omega

theorem copyHoleAfter_high_parents {d : Nat} {context target : ParentContext} {a : List Nat}
    {visible : List Nat} {cap : Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d (context ++ [Parents.label d context a])
      (target ++ [Parents.label d target (shift a cap delta phase)]) visible
      (List.replicate context.length 0 ++ [cap]) context.length cap delta phase)
    (hs : Forests (List Nat)) (rest : NumericalExpr)
    (legal : FiniteLegal d context (.cons a hs rest)) (depth : Nat) {site : HoleSite}
    (found : holeSite d context none depth (.cons a hs rest) = some site)
    (room : cap < d)
    (selected : (Parents.label d site.context site.terminal).parents[cap]?.join = some context.length)
    (difference : ∀ row, row < cap → site.terminal[row]?.getD 0 = a[row]?.getD 0 + delta[row]?.getD 0)
    (count : Nat) {result : ParentContext}
    (computed : copyHoleAfter d cap delta context (.cons a hs rest) depth count phase target = some result)
    {row : Nat} (high : cap ≤ row) (rowRoom : row < d) :
    (Parents.label d result (shift a cap delta (phase + count))).parents[row]?.join =
      (Parents.label d target (shift a cap delta phase)).parents[row]?.join := by
  induction count generalizing target visible phase with
  | zero =>
    have same : result = target := by simpa only [copyHoleAfter, Option.some.injEq] using computed.symm
    subst result
    rfl
  | succ count ih =>
    have later := Parents.label_parent_bound d site.context site.terminal cap context.length selected
    have coordinates := holeSite_root_coordinates found later
    have rootTake := holeSite_root_take found later
    have sourceHole := (holeSite_finiteLegal depth (.cons a hs rest) legal
      (by intro bound impossible; cases impossible) found).1
    have rootWidth : (site.context[context.length]?.getD default).coordinates.length = d := by
      rw [coordinates]
      exact legal.1
    have actualDifference : ∀ j, j < cap → site.terminal[j]?.getD 0 =
        Parents.reading site.context j context.length + delta[j]?.getD 0 := by
      intro j low
      change site.terminal[j]?.getD 0 =
        (site.context[context.length]?.getD default).coordinates[j]?.getD 0 + delta[j]?.getD 0
      rw [coordinates]
      exact difference j low
    obtain ⟨hole, holeFound, holeView⟩ := copied_root_holeSite_exact scope hs rest legal depth found later
    obtain ⟨holeVisible, holeHistory, holePrefix, atHole, _, _, _⟩ := holeView
    have density := copied_root_hole_density scope hs rest depth found holeFound later atHole.view holePrefix
    have restart := atHole.restart site.terminal sourceHole.1 sourceHole.2.1 rootWidth room selected actualDifference
    dsimp only at restart
    rw [rootTake, coordinates] at restart
    have remaining : copyHoleAfter d cap delta context (.cons a hs rest) depth count (phase + 1) hole.context = some result := by
      simpa only [copyHoleAfter, holeFound] using computed
    have restParents := ih restart remaining
    have phaseEq : phase + (count + 1) = phase + 1 + count := by omega
    rw [phaseEq, restParents]
    have firstParents := atHole.next_head_parents site.terminal sourceHole.1 sourceHole.2.1
      rootWidth room selected actualDifference row rowRoom
    rw [if_neg (by omega : ¬ row < cap), coordinates, density.1] at firstParents
    rw [firstParents]
    have targetLater : target.length < hole.context.length := by
      rw [← density.1]
      exact atHole.view.bounded context.length later
    have rootFound := holeFound
    rw [copied_at_root] at rootFound
    have initial := holeSite_after_head rootFound targetLater
    rw [← Parents.parent_prefix_eq initial row target.length (by simp), Parents.append_label_parent]

end BTnSSBMS.Source
