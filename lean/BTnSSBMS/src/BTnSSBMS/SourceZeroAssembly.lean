import BTnSSBMS.SourceZeroSelection

/-! Assemble the actual zero-class branch. Its root stays in the stopping
forest, so the original root itself supplies the outer-owner fence. -/
namespace BTnSSBMS.Source

theorem ordinary_zero_finiteLegal
    {d root rootDepth stopDepth index : Nat} {e stop : NumericalExpr}
    (legal : FiniteLegal d [] e) (positive : 0 < d)
    (first : stopDepth = (spine e).findIdx stopping)
    (stopSelected : (spine e)[stopDepth]? = some stop)
    {terminal : List Nat} {attached : Forests (List Nat)}
    (stopLast : last? stop = some (terminal, attached))
    {parentStop : ParentExpr} {parentTerminal : ParentLabel} {parentAttached : Forests ParentLabel}
    (parentSelected : (spine (parents d e))[stopDepth]? = some parentStop)
    (parentLast : last? parentStop = some (parentTerminal, parentAttached))
    (chosen : highestParent 0 parentTerminal.parents = some (0, root))
    (location : locateRoot (spine e) root = some (rootDepth, index))
    {rootPart : MarkedExpr}
    (partSelected : (spine (mark 0 root [] (parents d e)))[rootDepth]? = some rootPart)
    (count : Nat) :
    FiniteLegal d [] (ascendReplace (mark 0 root [] (parents d e))
      (copies (drop index rootPart) (stopDepth - rootDepth) [] none count 1)
      (some stopDepth) [] 0) := by
  obtain ⟨stopLayer, atStop, stopSame⟩ := layerAt_exists (d := d) [] none [] stopSelected
  have terminalSelected := selected_low_numerical_root parentSelected parentLast chosen positive atStop
    (by rw [stopSame]; exact stopLast)
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
  obtain ⟨rootLayer, a, hs, rest, atRoot, rootLookup, cut, rootSize, coherent, valid, pieceLegal⟩ :=
    extracted_root_finiteLegal legal location
  have sameLayer : rootLayer = stopLayer := by
    rw [sameDepth, atStop] at atRoot
    exact Option.some.inj atRoot.symm
  obtain ⟨located, locatedLookup, inside, _⟩ := locateRoot_sound (spine e) root rootDepth index location
  have samePart : located = rootLayer.term := Option.some.inj (locatedLookup.symm.trans rootLookup)
  subst located
  let rootContext := dropContext d rootLayer.context index rootLayer.term
  let site : HoleSite := ⟨terminalContext,
    if stopDepth - rootDepth = 0 then none else stopLayer.owner, terminal, attached⟩
  have rootHole := root_hole_from_layers atRoot atStop (by omega) inside
    (by rw [stopSame]; exact stopLast)
  rw [cut] at rootHole
  change holeSite d rootContext none (stopDepth - rootDepth) (.cons a hs rest) = some site at rootHole
  have numerical : (Parents.label d site.context site.terminal).parents[0]?.join = some rootContext.length := by
    change (Parents.label d terminalContext terminal).parents[0]?.join = some _
    rw [rootSize]
    exact terminalSelected
  obtain ⟨markedPart, markedSelected, markedCut, _⟩ :=
    actual_marked_root_piece (cap := 0) (Nat.zero_le d) location atRoot
  have markedSame : markedPart = rootPart := Option.some.inj (markedSelected.symm.trans partSelected)
  subst markedPart
  rw [cut] at markedCut
  let result := copies (drop index rootPart) (stopDepth - rootDepth) [] none count 1
  have computed := initial_copies_low_finiteLegal coherent valid pieceLegal rootHole
    (Or.inr (by omega)) positive numerical count
  dsimp only at computed
  rw [rootSize] at computed
  have headZero : (shift a 0 [] 1)[0]?.getD 0 = a[0]?.getD 0 := by
    rw [shift_value _ _ _ _ 0 (by rw [pieceLegal.1]; exact positive)]
    simp
  have resultLegal : FiniteLegal d terminalContext result ∧
      ∀ col ∈ labels result, a[0]?.getD 0 ≤ col[0]?.getD 0 := by
    dsimp only [result]
    rw [markedCut]
    simpa only [List.range_zero, List.map_nil, headZero] using computed
  have originalHole := layerAt_holeSite stopDepth e atStop (by rw [stopSame]; exact stopLast)
  let wholeSite : HoleSite := ⟨terminalContext, stopLayer.owner, terminal, attached⟩
  change holeSite d [] none stopDepth e = some wholeSite at originalHole
  have rootState := layerAt_legal (Parents.empty_coherent d) Parents.empty_context_valid rootDepth e legal
    (by intro bound impossible; cases impossible) atRoot
  have rootMember : a ∈ labels rootLayer.term := List.mem_of_getElem? (labels_drop_head index rootLayer.term cut)
  have ownerFence : FitsOwner wholeSite.owner result := by
    intro bound owner col member
    have ownerAtRoot : rootLayer.owner = some bound := by rw [sameLayer]; exact owner
    have rootAbove := rootState.2.2.2 bound ownerAtRoot a rootMember
    exact Nat.lt_of_lt_of_le rootAbove (resultLegal.2 col member)
  have assembled := (splice_finiteLegal stopDepth e result legal
    (by intro bound impossible; cases impossible) originalHole resultLegal.1 ownerFence).1
  change FiniteLegal d [] (ascendReplace (mark 0 root [] (parents d e)) result (some stopDepth) [] 0)
  rw [ascendReplace_splice]
  have unchanged : (mark 0 root [] (parents d e)).map (fun a => shift a.1 a.2 [] 0) = e := by
    simp only [shift_zero, mark_erase, parents_erase]
  rw [unchanged]
  exact assembled

theorem expand_zero_class_finiteLegal {d root : Nat} {e f : NumericalExpr}
    (legal : FiniteLegal d [] e) (positive : 0 < d)
    {parentStop : ParentExpr} {parentTerminal : ParentLabel} {parentAttached : Forests ParentLabel}
    (parentSelected : (spine (parents d e))[(spine e).findIdx stopping]? = some parentStop)
    (parentLast : last? parentStop = some (parentTerminal, parentAttached))
    (chosen : highestParent 0 parentTerminal.parents = some (0, root))
    (count : Nat) (edge : expand? d e count = some f) : FiniteLegal d [] f := by
  cases atLast : last? e with
  | none =>
    have empty := (last_none_iff e).mp atLast
    subst e
    have same : f = .nil := by simpa only [expand_empty, Option.some.injEq] using edge.symm
    subst f
    trivial
  | some column =>
    by_cases zero : zeroColumn column = true
    · have result := expand_zero_finiteLegal d count legal atLast zero
      have same : f = dropLast e := Option.some.inj (edge.symm.trans result.1)
      subst f
      exact result.2
    · cases stopSelected : (spine e)[(spine e).findIdx stopping]? with
      | none => simp [expand?, atLast, zero, stopSelected] at edge
      | some stop =>
        cases stopLast : last? stop with
        | none => simp [expand?, atLast, zero, stopSelected, stopLast] at edge
        | some stopColumn =>
          obtain ⟨terminal, attached⟩ := stopColumn
          by_cases specialCase : specialColumn (terminal, attached) = true
          · have same : f = special count ((spine e).findIdx stopping) e := by
              simpa [expand?, atLast, zero, stopSelected, stopLast, specialCase] using edge.symm
            subst f
            exact special_spine_finiteLegal count _ legal stopSelected stopLast specialCase
          · cases location : locateRoot (spine e) root with
            | none =>
              simp [expand?, atLast, zero, stopSelected, stopLast, specialCase,
                parentSelected, parentLast, chosen, location] at edge
            | some pair =>
              obtain ⟨rootDepth, index⟩ := pair
              cases rootRead : ((((spine e).take ((spine e).findIdx stopping + 1)).flatMap labels)[root]?) with
              | none =>
                simp [expand?, atLast, zero, stopSelected, stopLast, specialCase,
                  parentSelected, parentLast, chosen, location, rootRead] at edge
              | some rootColumn =>
                cases partSelected : (spine (mark 0 root [] (parents d e)))[rootDepth]? with
                | none =>
                  simp [expand?, atLast, zero, stopSelected, stopLast, specialCase,
                    parentSelected, parentLast, chosen, location, rootRead, partSelected] at edge
                | some rootPart =>
                  cases tailSelected : (spine (mark 0 root [] (parents d e)))[(spine e).findIdx stopping]? with
                  | none =>
                    simp [expand?, atLast, zero, stopSelected, stopLast, specialCase,
                      parentSelected, parentLast, chosen, location, rootRead, tailSelected] at edge
                  | some tailPart =>
                    cases tailLast : last? tailPart with
                    | none =>
                      simp [expand?, atLast, zero, stopSelected, stopLast, specialCase,
                        parentSelected, parentLast, chosen, location, rootRead, tailSelected, tailLast] at edge
                    | some tailColumn =>
                      have result := ordinary_zero_finiteLegal legal positive rfl stopSelected stopLast
                        parentSelected parentLast chosen location partSelected count
                      have different : 0 ≠ d := by omega
                      simp [expand?, atLast, zero, stopSelected, stopLast, specialCase,
                        parentSelected, parentLast, chosen, location, rootRead, partSelected, tailSelected, tailLast,
                        different] at edge
                      rw [← edge]
                      exact result

end BTnSSBMS.Source
