import BTnSSBMS.BNPositiveCopies

/-! BN for the full frozen positive low-class expansion, not just
for an extracted root template or an ordinary unspliced copy. -/
namespace BTnSSBMS.Source

theorem BN.layerAt {d : Nat} {context : ParentContext} {owner : Option Nat} {owners : List Nat}
    (depth : Nat) (e : NumericalExpr) (ordered : BN d context e) {layer : SpineLayer}
    (found : Source.layerAt d context owner owners depth e = some layer) : BN d layer.context layer.term := by
  induction depth generalizing context owner owners e layer with
  | zero =>
    have same : layer = ⟨context, owner, owners, e⟩ := by
      simpa only [Source.layerAt, Option.some.injEq] using found.symm
    subst layer
    exact ordered
  | succ depth ih =>
    simp only [Source.layerAt, Option.bind_eq_some_iff] at found
    obtain ⟨⟨a, hs⟩, last, h, child, next⟩ := found
    exact ih h ((ordered.last_context last).2.1.last child) next

theorem ordinary_positive_expand_BN
    {d cap root rootDepth stopDepth index : Nat} {e stop : NumericalExpr}
    (positiveCap : 0 < cap) (room : cap < d) (legal : FiniteLegal d [] e) (ordered : BN d [] e)
    (stopSelected : (spine e)[stopDepth]? = some stop)
    {terminal : List Nat} {attached : Forests (List Nat)}
    (stopLast : last? stop = some (terminal, attached))
    {parentStop : ParentExpr} {parentTerminal : ParentLabel} {parentAttached : Forests ParentLabel}
    (parentSelected : (spine (parents d e))[stopDepth]? = some parentStop)
    (parentLast : last? parentStop = some (parentTerminal, parentAttached))
    (chosen : highestParent 0 parentTerminal.parents = some (cap, root))
    (location : locateRoot (spine e) root = some (rootDepth, index))
    {rootColumn : List Nat}
    (rootRead : ((((spine e).take (stopDepth + 1)).flatMap labels)[root]?) = some rootColumn)
    {rootPart tailPart : MarkedExpr}
    (partSelected : (spine (mark cap root [] (parents d e)))[rootDepth]? = some rootPart)
    (tailSelected : (spine (mark cap root [] (parents d e)))[stopDepth]? = some tailPart)
    {tailColumn : List Nat × Nat} {tailForests : Forests (List Nat × Nat)}
    (tailLast : last? tailPart = some (tailColumn, tailForests)) (count : Nat) :
    let delta := (List.range cap).map (fun j => terminal[j]?.getD 0 - rootColumn[j]?.getD 0)
    let donation := if cap = d then some (dropLastForest tailForests) else none
    BN d [] (ascendReplace (mark cap root [] (parents d e))
      (copies (drop index rootPart) (stopDepth - rootDepth) delta donation count 1)
      (some stopDepth) delta 0) := by
  have positive : 0 < d := by omega
  have notTop : cap ≠ d := by omega
  obtain ⟨stopLayer, atStop, stopSame⟩ := layerAt_exists (d := d) [] none [] stopSelected
  have atTerminal : last? stopLayer.term = some (terminal, attached) := by rw [stopSame]; exact stopLast
  let terminalContext := outerContext d stopLayer.context (dropLast stopLayer.term)
  have numeric := selected_low_numerical_root parentSelected parentLast chosen room atStop atTerminal
  have earlierRoot : root < terminalContext.length :=
    Parents.label_parent_bound d terminalContext terminal cap root numeric
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
  have pieceOrdered : BN d rootContext (.cons a hs rest) := by
    rw [← cut]
    exact (BN.layerAt rootDepth e ordered atRoot).drop index
  obtain ⟨markedPart, markedSelected, markedCut, _⟩ := actual_marked_root_piece (Nat.le_of_lt room) location atRoot
  have sameMarked : markedPart = rootPart := Option.some.inj (markedSelected.symm.trans partSelected)
  subst markedPart
  rw [cut] at markedCut
  let delta := (List.range cap).map (fun j => terminal[j]?.getD 0 - a[j]?.getD 0)
  let donation := if cap = d then some (dropLastForest tailForests) else none
  let result := copies (drop index rootPart) (stopDepth - rootDepth) delta donation count 1
  have selected : (Parents.label d site.context site.terminal).parents[cap]?.join = some rootContext.length := by
    rw [rootSize]
    exact numeric
  have replacement : BN d terminalContext result := by
    have computed := initial_copies_positive_BN coherent valid pieceLegal pieceOrdered rootHole positiveCap room selected count
    dsimp only at computed
    rw [rootSize] at computed
    dsimp only [result, donation, delta]
    rw [if_neg notTop, markedCut]
    exact computed
  have replacementFinite : FiniteLegal d terminalContext result := by
    have computed := (initial_copies_low_finiteLegal coherent valid pieceLegal rootHole (.inl positiveCap) room selected count).1
    rw [rootSize] at computed
    dsimp only [result, donation, delta]
    rw [if_neg notTop, markedCut]
    exact computed
  have floor : TerminalFloor terminal result := by
    have computed := initial_copies_positive_floor coherent valid pieceLegal rootHole positiveCap room selected count
    dsimp only at computed
    rw [rootSize] at computed
    dsimp only [result, donation, delta]
    rw [if_neg notTop, markedCut]
    exact computed
  have originalHole := layerAt_holeSite stopDepth e atStop atTerminal
  let whole : HoleSite := ⟨terminalContext, stopLayer.owner, terminal, attached⟩
  change holeSite d [] none stopDepth e = some whole at originalHole
  have decrease := ordinary_expand_lt positive legal stopSelected stopLast parentSelected parentLast
    chosen location rootRead partSelected tailSelected tailLast count
  change (ascendReplace (mark cap root [] (parents d e)) result (some stopDepth) delta 0).compare
    (listCompare Ord.compare) e = .lt at decrease
  change BN d [] (ascendReplace (mark cap root [] (parents d e)) result (some stopDepth) delta 0)
  have unchanged : (mark cap root [] (parents d e)).map (fun a => shift a.1 a.2 delta 0) = e := by
    simp only [shift_zero, mark_erase, parents_erase]
  rw [ascendReplace_splice, unchanged] at decrease ⊢
  rw [splice_compare stopDepth e result originalHole] at decrease
  exact splice_BN stopDepth e result ordered positive legal originalHole replacement replacementFinite decrease floor

end BTnSSBMS.Source
