import BTnSSBMS.BNZeroForest
import BTnSSBMS.BNSpineLift

/-! The actual first stopping layer puts a zero-class root in the
same forest as its terminal. Restore the old prefix there, then lift
the BN proof through all outer attachment owners. -/
namespace BTnSSBMS.Source

theorem ordinary_zero_expand_BN
    {d root rootDepth stopDepth index : Nat} {e stop : NumericalExpr}
    (positive : 0 < d) (legal : FiniteLegal d [] e) (ordered : BN d [] e)
    (first : stopDepth = (spine e).findIdx stopping)
    (stopSelected : (spine e)[stopDepth]? = some stop)
    {terminal : List Nat} {attached : Forests (List Nat)}
    (stopLast : last? stop = some (terminal, attached))
    {parentStop : ParentExpr} {parentTerminal : ParentLabel} {parentAttached : Forests ParentLabel}
    (parentSelected : (spine (parents d e))[stopDepth]? = some parentStop)
    (parentLast : last? parentStop = some (parentTerminal, parentAttached))
    (chosen : highestParent 0 parentTerminal.parents = some (0, root))
    (location : locateRoot (spine e) root = some (rootDepth, index))
    {rootColumn : List Nat}
    (rootRead : ((((spine e).take (stopDepth + 1)).flatMap labels)[root]?) = some rootColumn)
    {rootPart tailPart : MarkedExpr}
    (partSelected : (spine (mark 0 root [] (parents d e)))[rootDepth]? = some rootPart)
    (tailSelected : (spine (mark 0 root [] (parents d e)))[stopDepth]? = some tailPart)
    {tailColumn : List Nat × Nat} {tailForests : Forests (List Nat × Nat)}
    (tailLast : last? tailPart = some (tailColumn, tailForests)) (count : Nat) :
    BN d [] (ascendReplace (mark 0 root [] (parents d e))
      (copies (drop index rootPart) (stopDepth - rootDepth) [] none count 1) (some stopDepth) [] 0) := by
  obtain ⟨stopLayer, atStop, stopSame⟩ := layerAt_exists (d := d) [] none [] stopSelected
  have atTerminal : last? stopLayer.term = some (terminal, attached) := by rw [stopSame]; exact stopLast
  have terminalSelected := selected_low_numerical_root parentSelected parentLast chosen positive atStop atTerminal
  let terminalContext := outerContext d stopLayer.context (dropLast stopLayer.term)
  have earlierRoot : root < terminalContext.length :=
    Parents.label_parent_bound d terminalContext terminal 0 root terminalSelected
  have within := selected_zero_root_in_layer positive legal first stopSelected stopLast
    parentSelected parentLast chosen atStop
  have stopSize := layerAt_context_length stopDepth e atStop
  simp only [List.length_nil, Nat.zero_add] at stopSize
  have rootBeforeStop : root < (((spine e).take stopDepth).map length).sum + length stop := by
    dsimp only [terminalContext] at earlierRoot
    rw [outerContext_length, length_dropLast, stopSize, stopSame] at earlierRoot
    omega
  have sameDepth := locateRoot_same_layer (spine e) root rootDepth index stopDepth location stopSelected
    (by rw [← stopSize]; exact within) rootBeforeStop
  subst rootDepth
  obtain ⟨rootLayer, a, hs, rest, atRoot, rootLookup, cut, rootSize, _, _, _⟩ :=
    extracted_root_finiteLegal legal location
  have sameLayer : rootLayer = stopLayer := by
    rw [atStop] at atRoot
    exact Option.some.inj atRoot.symm
  subst rootLayer
  have state := layerAt_legal (Parents.empty_coherent d) Parents.empty_context_valid stopDepth e legal
    (by intro bound impossible; cases impossible) atStop
  have old := BN.layerAt stopDepth e ordered atStop
  have selected : (Parents.label d terminalContext terminal).parents[0]?.join =
      some (dropContext d stopLayer.context index stopLayer.term).length := by
    rw [rootSize]
    exact terminalSelected
  have computed := zero_forest_expand_BN state.1 state.2.1 positive state.2.2.1 old index cut atTerminal selected count
  dsimp only at computed
  rw [rootSize] at computed
  obtain ⟨markedPart, markedSelected, markedCut, _⟩ :=
    actual_marked_root_piece (cap := 0) (Nat.zero_le d) location atStop
  have sameMarked : markedPart = rootPart := Option.some.inj (markedSelected.symm.trans partSelected)
  subst markedPart
  rw [cut] at markedCut
  let result := copies (drop index rootPart) 0 [] none count 1
  have localGood : BN d stopLayer.context (splice 0 result stopLayer.term) := by
    dsimp only [result]
    rw [markedCut]
    exact computed
  have originalHole := layerAt_holeSite stopDepth e atStop atTerminal
  let whole : HoleSite := ⟨terminalContext, stopLayer.owner, terminal, attached⟩
  change holeSite d [] none stopDepth e = some whole at originalHole
  have decrease := ordinary_expand_lt positive legal stopSelected stopLast parentSelected parentLast
    chosen location rootRead partSelected tailSelected tailLast count
  dsimp only at decrease
  rw [if_neg (by omega : (0 : Nat) ≠ d), List.range_zero, List.map_nil, Nat.sub_self] at decrease
  change (ascendReplace (mark 0 root [] (parents d e)) result (some stopDepth) [] 0).compare
    (listCompare Ord.compare) e = .lt at decrease
  rw [Nat.sub_self]
  change BN d [] (ascendReplace (mark 0 root [] (parents d e)) result (some stopDepth) [] 0)
  have unchanged : (mark 0 root [] (parents d e)).map (fun a => shift a.1 a.2 [] 0) = e := by
    simp only [shift_zero, mark_erase, parents_erase]
  rw [ascendReplace_splice, unchanged] at decrease ⊢
  rw [splice_compare stopDepth e result originalHole] at decrease
  exact splice_BN_at_layer stopDepth e result ordered positive legal atStop originalHole localGood decrease

end BTnSSBMS.Source
