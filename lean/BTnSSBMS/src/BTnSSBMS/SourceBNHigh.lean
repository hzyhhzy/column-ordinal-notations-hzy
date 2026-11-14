import BTnSSBMS.SourceBNPositive
import BTnSSBMS.BNHighCopies

/-! BN for the whole actual highest-class source branch, including
the outer owners and the real previous-phase donated forest list. -/
namespace BTnSSBMS.Source

theorem ordinary_high_expand_BN
    {d root rootDepth stopDepth index : Nat} {e stop : NumericalExpr}
    (positive : 0 < d) (legal : FiniteLegal d [] e) (ordered : BN d [] e)
    (stopSelected : (spine e)[stopDepth]? = some stop)
    {terminal : List Nat} {attached : Forests (List Nat)}
    (stopLast : last? stop = some (terminal, attached))
    {parentStop : ParentExpr} {parentTerminal : ParentLabel} {parentAttached : Forests ParentLabel}
    (parentSelected : (spine (parents d e))[stopDepth]? = some parentStop)
    (parentLast : last? parentStop = some (parentTerminal, parentAttached))
    (chosen : highestParent 0 parentTerminal.parents = some (d, root))
    (location : locateRoot (spine e) root = some (rootDepth, index))
    {rootColumn : List Nat}
    (rootRead : ((((spine e).take (stopDepth + 1)).flatMap labels)[root]?) = some rootColumn)
    {rootPart tailPart : MarkedExpr}
    (partSelected : (spine (mark d root [] (parents d e)))[rootDepth]? = some rootPart)
    (tailSelected : (spine (mark d root [] (parents d e)))[stopDepth]? = some tailPart)
    {tailColumn : List Nat × Nat} {tailForests : Forests (List Nat × Nat)}
    (tailLast : last? tailPart = some (tailColumn, tailForests)) (count : Nat) :
    let delta := (List.range d).map (fun j => terminal[j]?.getD 0 - rootColumn[j]?.getD 0)
    BN d [] (ascendReplace (mark d root [] (parents d e))
      (copies (drop index rootPart) (stopDepth - rootDepth) delta (some (dropLastForest tailForests)) count 1)
      (some stopDepth) delta 0) := by
  obtain ⟨stopLayer, atStop, stopSame⟩ := layerAt_exists (d := d) [] none [] stopSelected
  have atTerminal : last? stopLayer.term = some (terminal, attached) := by rw [stopSame]; exact stopLast
  let terminalContext := outerContext d stopLayer.context (dropLast stopLayer.term)
  have earlierRoot : root < terminalContext.length :=
    (selected_top_scoped parentSelected parentLast chosen atStop).1
  have path := selected_top_numerical_ancestor positive parentSelected parentLast chosen atStop atTerminal
  have stopSize := layerAt_context_length stopDepth e atStop
  simp only [List.length_nil, Nat.zero_add] at stopSize
  have rootBeforeStop : root < (((spine e).take stopDepth).map length).sum + length stop := by
    dsimp only [terminalContext] at earlierRoot
    rw [outerContext_length, length_dropLast, stopSize, stopSame] at earlierRoot
    omega
  have layers := locateRoot_before (spine e) root rootDepth index stopDepth location stopSelected rootBeforeStop
  obtain ⟨rootLayer, a, hs, rest, atRoot, rootLookup, cut, rootSize, coherent, valid, pieceLegal⟩ :=
    extracted_root_finiteLegal legal location
  obtain ⟨located, locatedLookup, inside, _⟩ := locateRoot_sound (spine e) root rootDepth index location
  have samePart : located = rootLayer.term := Option.some.inj (locatedLookup.symm.trans rootLookup)
  subst located
  let rootContext := dropContext d rootLayer.context index rootLayer.term
  change rootContext.length = root at rootSize
  have sameVector : rootColumn = a := Option.some.inj
    (rootRead.symm.trans (actual_root_coordinates location layers atRoot cut))
  subst rootColumn
  let site : HoleSite := ⟨terminalContext,
    if stopDepth - rootDepth = 0 then none else stopLayer.owner, terminal, attached⟩
  have rootHole := root_hole_from_layers atRoot atStop layers inside atTerminal
  rw [cut] at rootHole
  change holeSite d rootContext none (stopDepth - rootDepth) (.cons a hs rest) = some site at rootHole
  have numerical : Parents.Ancestor (site.context ++ [Parents.label d site.context site.terminal])
      (d - 1) rootContext.length site.context.length := by
    rw [rootSize]
    exact path
  have later : rootContext.length < site.context.length := by rw [rootSize]; exact earlierRoot
  have nonowned := selected_top_root_tail parentSelected parentLast chosen atStop location atRoot cut
  have pieceOrdered : BN d rootContext (.cons a hs rest) := by
    rw [← cut]
    exact (BN.layerAt rootDepth e ordered atRoot).drop index
  obtain ⟨markedPart, markedSelected, markedCut, _⟩ := actual_marked_root_piece (Nat.le_refl d) location atRoot
  have sameMarked : markedPart = rootPart := Option.some.inj (markedSelected.symm.trans partSelected)
  subst markedPart
  rw [cut] at markedCut
  have donor := actual_marked_top_donation positive parentSelected parentLast chosen atStop atTerminal
    tailSelected tailLast site.owner
  change dropLastForest tailForests = donationAt d root site at donor
  have attachedNonempty := selected_high_terminal_attached stopSelected stopLast parentSelected parentLast chosen
  let delta := (List.range d).map (fun j => terminal[j]?.getD 0 - a[j]?.getD 0)
  let result := copies (drop index rootPart) (stopDepth - rootDepth) delta (some (dropLastForest tailForests)) count 1
  have replacement : BN d terminalContext result := by
    have computed := initial_copies_high_BN coherent valid pieceLegal pieceOrdered rootHole
      nonowned positive later attachedNonempty numerical count
    dsimp only at computed
    rw [rootSize] at computed
    dsimp only [result, delta]
    rw [markedCut, donor]
    exact computed
  have replacementFinite : FiniteLegal d terminalContext result := by
    have computed := (initial_copies_high_finiteLegal coherent valid pieceLegal rootHole
      nonowned positive later numerical count).1
    rw [rootSize] at computed
    dsimp only [result, delta]
    rw [markedCut, donor]
    exact computed
  have floor : TerminalFloor terminal result := by
    have computed := initial_copies_high_floor coherent valid pieceLegal rootHole nonowned positive later numerical count
    dsimp only at computed
    rw [rootSize] at computed
    dsimp only [result, delta]
    rw [markedCut, donor]
    exact computed
  have originalHole := layerAt_holeSite stopDepth e atStop atTerminal
  let whole : HoleSite := ⟨terminalContext, stopLayer.owner, terminal, attached⟩
  change holeSite d [] none stopDepth e = some whole at originalHole
  have decrease := ordinary_expand_lt positive legal stopSelected stopLast parentSelected parentLast
    chosen location rootRead partSelected tailSelected tailLast count
  dsimp only at decrease
  rw [if_pos rfl] at decrease
  change (ascendReplace (mark d root [] (parents d e)) result (some stopDepth) delta 0).compare
    (listCompare Ord.compare) e = .lt at decrease
  change BN d [] (ascendReplace (mark d root [] (parents d e)) result (some stopDepth) delta 0)
  have unchanged : (mark d root [] (parents d e)).map (fun a => shift a.1 a.2 delta 0) = e := by
    simp only [shift_zero, mark_erase, parents_erase]
  rw [ascendReplace_splice, unchanged] at decrease ⊢
  rw [splice_compare stopDepth e result originalHole] at decrease
  exact splice_BN stopDepth e result ordered positive legal originalHole replacement replacementFinite decrease floor

end BTnSSBMS.Source
