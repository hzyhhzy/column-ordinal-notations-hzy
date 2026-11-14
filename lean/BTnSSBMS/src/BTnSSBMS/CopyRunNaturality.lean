import BTnSSBMS.CopySeamSquare
import BTnSSBMS.CopyIteration

/-! Complete ordinary copy runs commute with paired root transport.
The entering maps and the high parents of the forced root are explicit
finite premises; every subsequent hole map, seam head and remaining run
is constructed inside the induction. No block inequality is assumed. -/
namespace BTnSSBMS.Source

private theorem relocate_copies_as_rooted {d : Nat} {context target later : ParentContext}
    {a visible between head : List Nat} {cap : Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d (context ++ [Parents.label d context a])
      (target ++ [Parents.label d target (shift a cap delta phase)]) visible
      (List.replicate context.length 0 ++ [cap]) context.length cap delta phase)
    (hs : Forests (List Nat)) (rest : NumericalExpr)
    (legal : FiniteLegal d context (.cons a hs rest)) (depth : Nat) {site : HoleSite}
    (found : holeSite d context none depth (.cons a hs rest) = some site)
    (afterHead : context.length < site.context.length)
    (headEq : relocationHead d target later between (shift a cap delta phase) = head)
    (count : Nat) :
    let run := copies (mark cap context.length (List.replicate context.length 0)
      (Parents.annotate d context (.cons a hs rest))) depth delta none count phase
    relocate d target later between run =
      rootedRelocate d target later (between ++ [later.length]) head run := by
  dsimp only
  cases count with
  | zero => simp only [copies, relocate, rootedRelocate]
  | succ count =>
    obtain ⟨hole, holeFound, _⟩ := copied_root_holeSite scope hs rest legal depth found afterHead
    have span := copied_root_holeSite_span d cap delta phase context target a hs rest depth found holeFound
    rw [copied_at_root] at holeFound
    obtain ⟨forests, tail, shape⟩ := splice_after_head_shape holeFound (by omega)
      (copies (mark cap context.length (List.replicate context.length 0)
        (Parents.annotate d context (.cons a hs rest))) depth delta none count (phase + 1))
    rw [← copied_at_root] at shape
    simp only [copied] at shape
    rw [copies, ascendReplace_splice, shape]
    simp only [relocate, rootedRelocate, headEq]

theorem rooted_copies_relocation_square {d : Nat} {context target later : ParentContext} {a : List Nat}
    {visible nextVisible between : List Nat} {cap : Nat} {delta : List Nat} {phase nextPhase : Nat}
    (scope : ShiftView d (context ++ [Parents.label d context a])
      (target ++ [Parents.label d target (shift a cap delta phase)]) visible
      (List.replicate context.length 0 ++ [cap]) context.length cap delta phase)
    (next : ShiftView d (context ++ [Parents.label d context a])
      (later ++ [Parents.label d later (shift a cap delta nextPhase)]) nextVisible
      (List.replicate context.length 0 ++ [cap]) context.length cap delta nextPhase)
    (view : Parents.NumericalView d
      (target ++ [Parents.label d target (shift a cap delta phase)])
      (later ++ [Parents.label d later (shift a cap delta nextPhase)]) between)
    (square : visible.map (Parents.point between) = nextVisible)
    (highParents : ∀ row, cap ≤ row → row < d →
      Parents.parent (later ++ [Parents.label d later (shift a cap delta nextPhase)]) row
        (Parents.point between target.length) =
      (Parents.parent (target ++ [Parents.label d target (shift a cap delta phase)]) row target.length).map
        (Parents.point between))
    (hs : Forests (List Nat)) (rest : NumericalExpr)
    (legal : FiniteLegal d context (.cons a hs rest)) (depth : Nat) {site : HoleSite}
    (found : holeSite d context none depth (.cons a hs rest) = some site)
    (room : cap < d)
    (selected : (Parents.label d site.context site.terminal).parents[cap]?.join = some context.length)
    (difference : ∀ row, row < cap → site.terminal[row]?.getD 0 = a[row]?.getD 0 + delta[row]?.getD 0)
    (count : Nat) :
    let part := mark cap context.length (List.replicate context.length 0)
      (Parents.annotate d context (.cons a hs rest))
    rootedRelocate d target later between (shift a cap delta nextPhase)
      (copies part depth delta none count phase) = copies part depth delta none count nextPhase := by
  dsimp only
  induction count generalizing target later visible nextVisible between phase nextPhase with
  | zero => simp only [copies, rootedRelocate]
  | succ count ih =>
    have afterHead := Parents.label_parent_bound d site.context site.terminal cap context.length selected
    have coordinates := holeSite_root_coordinates found afterHead
    have rootTake := holeSite_root_take found afterHead
    have sourceHole := (holeSite_finiteLegal depth (.cons a hs rest) legal
      (by intro bound impossible; cases impossible) found).1
    have rootWidth : (site.context[context.length]?.getD default).coordinates.length = d := by
      rw [coordinates]; exact legal.1
    have actualDifference : ∀ row, row < cap → site.terminal[row]?.getD 0 =
        Parents.reading site.context row context.length + delta[row]?.getD 0 := by
      intro row below
      change site.terminal[row]?.getD 0 =
        (site.context[context.length]?.getD default).coordinates[row]?.getD 0 + delta[row]?.getD 0
      rw [coordinates]
      exact difference row below
    obtain ⟨oldHole, oldFound, oldExact⟩ := copied_root_holeSite_exact scope hs rest legal depth found afterHead
    obtain ⟨oldMap, oldHistory, oldExtended, oldScope, _, _, _⟩ := oldExact
    obtain ⟨newHole, newFound, newExact⟩ := copied_root_holeSite_exact next hs rest legal depth found afterHead
    obtain ⟨newMap, newHistory, newExtended, newScope, _, _, _⟩ := newExact
    have oldDensity := copied_root_hole_density scope hs rest depth found oldFound afterHead oldScope.view oldExtended
    have newDensity := copied_root_hole_density next hs rest depth found newFound afterHead newScope.view newExtended
    have oldLater : target.length < oldHole.context.length := by
      rw [← oldDensity.1]; exact oldScope.view.bounded context.length afterHead
    have newLater : later.length < newHole.context.length := by
      rw [← newDensity.1]; exact newScope.view.bounded context.length afterHead
    have oldFoundHead := oldFound
    have newFoundHead := newFound
    rw [copied_at_root] at oldFoundHead newFoundHead
    have oldPrefix := holeSite_after_head oldFoundHead oldLater
    have newPrefix := holeSite_after_head newFoundHead newLater
    have whole := rooted_copy_relocation_square scope next between (by simpa using view.length)
      square hs rest legal
    obtain ⟨movedHole, moved, movedFound, movedExtended, oc, ov, nc, nv, movedView, splicing⟩ :=
      rootedRelocate_splice_at_hole scope.targetCoherent scope.targetValid next.targetCoherent
        next.targetValid view
        (copiedForests d context.length cap delta phase (context ++ [Parents.label d context a])
          (List.replicate context.length 0 ++ [cap]) hs)
        (copied d context.length cap delta phase (context ++ [Parents.label d context a])
          (List.replicate context.length 0 ++ [cap]) rest) depth oldFoundHead oldLater
    have wholeHead := whole
    rw [copied_at_root] at wholeHead
    rw [wholeHead] at movedFound splicing
    have sameHole : movedHole = newHole := Option.some.inj (movedFound.symm.trans newFound)
    subst movedHole
    have holeSquare := copied_hole_map_square scope next between (by simpa using view.length)
      square hs rest depth found oldFound newFound afterHead oldScope.view newScope.view movedView
      oldExtended newExtended movedExtended
    have highAtHole : ∀ row, cap ≤ row → row < d →
        Parents.parent newHole.context row (Parents.point moved (Parents.point oldMap context.length)) =
          (Parents.parent oldHole.context row (Parents.point oldMap context.length)).map (Parents.point moved) := by
      intro row high rowRoom
      rw [oldDensity.1]
      exact Parents.parent_transport_extends view scope.targetValid (by simp)
        (highParents row high rowRoom) oldPrefix newPrefix movedExtended
    have seamHead := oldScope.next_head_relocation_square newScope movedView holeSquare site.terminal
      sourceHole.1 sourceHole.2.1 rootWidth room selected actualDifference highAtHole
    rw [coordinates] at seamHead
    have oldRestart := oldScope.restart site.terminal sourceHole.1 sourceHole.2.1 rootWidth room selected actualDifference
    have newRestart := newScope.restart site.terminal sourceHole.1 sourceHole.2.1 rootWidth room selected actualDifference
    dsimp only at oldRestart newRestart
    rw [rootTake, coordinates] at oldRestart newRestart
    have restartView := relocation_view_append oc ov nc nv movedView (shift a cap delta (phase + 1))
    rw [seamHead] at restartView
    have restartSquare := Parents.reset_composition_square oldScope.view movedView.length holeSquare
      context.length newHole.context.length
    have restartExact := Parents.exactPosition_append oc ov nc nv movedView (shift a cap delta (phase + 1))
    rw [seamHead] at restartExact
    have remaining := ih oldRestart newRestart restartView restartSquare
      (fun row _ rowRoom => restartExact row rowRoom)
    have remainingTransport := relocate_copies_as_rooted oldRestart hs rest legal depth found afterHead seamHead count
    dsimp only at remainingTransport
    rw [remaining] at remainingTransport
    rw [copies, ascendReplace_splice]
    have conclusion := splicing (copies (mark cap context.length (List.replicate context.length 0)
      (Parents.annotate d context (.cons a hs rest))) depth delta none count (phase + 1))
    rw [remainingTransport, ← copied_at_root] at conclusion
    simpa only [copies, ascendReplace_splice, copied] using conclusion

end BTnSSBMS.Source
