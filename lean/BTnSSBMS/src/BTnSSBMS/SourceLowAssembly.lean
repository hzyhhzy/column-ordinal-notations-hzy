import BTnSSBMS.SourceRootCoordinates

/-!
The positive low-class branch is assembled on the whole original term.
Every supplied witness is a literal lookup performed by expand?; no
transport state, replacement legality, or root-template property is assumed.
Root existence and the zero-class cross-forest case are separate obligations.
-/
namespace BTnSSBMS.Source

theorem ordinary_positive_low_finiteLegal
    {d cap root rootDepth stopDepth index : Nat} {e stop : NumericalExpr}
    (legal : FiniteLegal d [] e) (positiveCap : 0 < cap) (room : cap < d)
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
    {rootPart : MarkedExpr}
    (partSelected : (spine (mark cap root [] (parents d e)))[rootDepth]? = some rootPart)
    (count : Nat) :
    let delta := (List.range cap).map (fun j => terminal[j]?.getD 0 - rootColumn[j]?.getD 0)
    FiniteLegal d [] (ascendReplace (mark cap root [] (parents d e))
      (copies (drop index rootPart) (stopDepth - rootDepth) delta none count 1)
      (some stopDepth) delta 0) := by
  obtain ⟨stopLayer, atStop, stopSame⟩ := layerAt_exists (d := d) [] none [] stopSelected
  have terminalSelected := selected_low_numerical_root parentSelected parentLast chosen room atStop
    (by rw [stopSame]; exact stopLast)
  let terminalContext := outerContext d stopLayer.context (dropLast stopLayer.term)
  have earlierRoot : root < terminalContext.length :=
    Parents.label_parent_bound d terminalContext terminal cap root terminalSelected
  have stopSize := layerAt_context_length stopDepth e atStop
  simp only [List.length_nil, Nat.zero_add] at stopSize
  have rootBeforeStop : root < (((spine e).take stopDepth).map length).sum + length stop := by
    dsimp only [terminalContext] at earlierRoot
    rw [outerContext_length, length_dropLast, stopSize, stopSame] at earlierRoot
    omega
  have layers := locateRoot_before (spine e) root rootDepth index stopDepth location stopSelected rootBeforeStop
  obtain ⟨rootLayer, a, hs, rest, atRoot, rootLookup, cut, rootSize, coherent, valid, pieceLegal⟩ :=
    extracted_root_finiteLegal legal location
  obtain ⟨located, locatedLookup, inside, offset⟩ := locateRoot_sound (spine e) root rootDepth index location
  have samePart : located = rootLayer.term := Option.some.inj (locatedLookup.symm.trans rootLookup)
  subst located
  let rootContext := dropContext d rootLayer.context index rootLayer.term
  have rootVector := actual_root_coordinates location layers atRoot cut
  have sameVector : rootColumn = a := Option.some.inj (rootRead.symm.trans rootVector)
  subst rootColumn
  let site : HoleSite := ⟨terminalContext,
    if stopDepth - rootDepth = 0 then none else stopLayer.owner, terminal, attached⟩
  have rootHole := root_hole_from_layers atRoot atStop layers inside
    (by rw [stopSame]; exact stopLast)
  rw [cut] at rootHole
  change holeSite d rootContext none (stopDepth - rootDepth) (.cons a hs rest) = some site at rootHole
  have numerical : (Parents.label d site.context site.terminal).parents[cap]?.join = some rootContext.length := by
    change (Parents.label d terminalContext terminal).parents[cap]?.join = some _
    rw [rootSize]
    exact terminalSelected
  obtain ⟨markedPart, markedSelected, markedCut, _⟩ :=
    actual_marked_root_piece (Nat.le_of_lt room) location atRoot
  have markedSame : markedPart = rootPart := Option.some.inj (markedSelected.symm.trans partSelected)
  subst markedPart
  rw [cut] at markedCut
  let delta := (List.range cap).map (fun j => terminal[j]?.getD 0 - a[j]?.getD 0)
  let result := copies (drop index rootPart) (stopDepth - rootDepth) delta none count 1
  have computed := initial_copies_low_finiteLegal coherent valid pieceLegal rootHole
    (Or.inl positiveCap) room numerical count
  dsimp only at computed
  rw [rootSize] at computed
  have resultLegal : FiniteLegal d terminalContext result ∧
      ∀ col ∈ labels result, (shift a cap delta 1)[0]?.getD 0 ≤ col[0]?.getD 0 := by
    dsimp only [result]
    rw [markedCut]
    exact computed
  have originalHole := layerAt_holeSite stopDepth e atStop (by rw [stopSame]; exact stopLast)
  let wholeSite : HoleSite := ⟨terminalContext, stopLayer.owner, terminal, attached⟩
  change holeSite d [] none stopDepth e = some wholeSite at originalHole
  have wholeLegal := holeSite_finiteLegal stopDepth e legal
    (by intro bound impossible; cases impossible) originalHole
  have states := holeSite_contexts coherent valid (stopDepth - rootDepth) (.cons a hs rest) rootHole
  have later : rootContext.length < site.context.length := by
    change rootContext.length < terminalContext.length
    rw [rootSize]
    exact earlierRoot
  have coordinates := holeSite_root_coordinates rootHole later
  have smaller := Parents.label_root_lower_value states.1 states.2 site.terminal room numerical
    (Nat.zero_le cap)
  change (site.context[rootContext.length]?.getD default).coordinates[0]?.getD 0 < terminal[0]?.getD 0 at smaller
  rw [coordinates] at smaller
  have headZero : (shift a cap delta 1)[0]?.getD 0 = terminal[0]?.getD 0 := by
    rw [shift_value _ _ _ _ 0 (by rw [pieceLegal.1]; omega)]
    simp only [if_pos positiveCap, delta, List.getElem?_map, List.getElem?_range positiveCap,
      Option.map_some, Option.getD_some, Nat.mul_one]
    omega
  have ownerFence : FitsOwner wholeSite.owner result := by
    intro bound owner col member
    have terminalAbove := wholeLegal.2.head bound owner
    have lower := resultLegal.2 col member
    rw [headZero] at lower
    exact Nat.lt_of_lt_of_le terminalAbove lower
  have assembled := (splice_finiteLegal stopDepth e result legal
    (by intro bound impossible; cases impossible) originalHole resultLegal.1 ownerFence).1
  dsimp only
  change FiniteLegal d [] (ascendReplace (mark cap root [] (parents d e)) result (some stopDepth) delta 0)
  rw [ascendReplace_splice]
  have unchanged : (mark cap root [] (parents d e)).map (fun a => shift a.1 a.2 delta 0) = e := by
    simp only [shift_zero, mark_erase, parents_erase]
  rw [unchanged]
  exact assembled

/-- Every defined positive low-class expansion of the actual function
preserves finite legality. The branch is identified by its literal
stopping-layer parent lookup; no extra copied-material hypothesis occurs. -/
theorem expand_positive_low_finiteLegal {d cap root : Nat} {e f : NumericalExpr}
    (legal : FiniteLegal d [] e) (positiveCap : 0 < cap) (room : cap < d)
    {parentStop : ParentExpr} {parentTerminal : ParentLabel} {parentAttached : Forests ParentLabel}
    (parentSelected : (spine (parents d e))[(spine e).findIdx stopping]? = some parentStop)
    (parentLast : last? parentStop = some (parentTerminal, parentAttached))
    (chosen : highestParent 0 parentTerminal.parents = some (cap, root))
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
                cases partSelected : (spine (mark cap root [] (parents d e)))[rootDepth]? with
                | none =>
                  simp [expand?, atLast, zero, stopSelected, stopLast, specialCase,
                    parentSelected, parentLast, chosen, location, rootRead, partSelected] at edge
                | some rootPart =>
                  cases tailSelected : (spine (mark cap root [] (parents d e)))[(spine e).findIdx stopping]? with
                  | none =>
                    simp [expand?, atLast, zero, stopSelected, stopLast, specialCase,
                      parentSelected, parentLast, chosen, location, rootRead, tailSelected] at edge
                  | some tailPart =>
                    cases tailLast : last? tailPart with
                    | none =>
                      simp [expand?, atLast, zero, stopSelected, stopLast, specialCase,
                        parentSelected, parentLast, chosen, location, rootRead, tailSelected, tailLast] at edge
                    | some tailColumn =>
                      have result := ordinary_positive_low_finiteLegal legal positiveCap room stopSelected stopLast
                        parentSelected parentLast chosen location rootRead partSelected count
                      have different : cap ≠ d := by omega
                      simp [expand?, atLast, zero, stopSelected, stopLast, specialCase,
                        parentSelected, parentLast, chosen, location, rootRead, partSelected, tailSelected, tailLast,
                        different] at edge
                      rw [← edge]
                      exact result

end BTnSSBMS.Source
