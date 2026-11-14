import BTnSSBMS.HWHighCopies

/-! Hereditary nonincrease of every attached forest list on the actual
seed-reachable domain. This proves HW, not the BN, SB or G block conditions. -/
namespace BTnSSBMS.Source

mutual
  theorem splice_compare {d : Nat} {context : ParentContext} {owner : Option Nat}
      (depth : Nat) (e replacement : NumericalExpr) {site : HoleSite}
      (found : holeSite d context owner depth e = some site) :
      (splice depth replacement e).compare (listCompare Ord.compare) e =
        replacement.compare (listCompare Ord.compare) (.cons site.terminal site.attached .nil) := by
    cases e with
    | nil => simp [holeSite] at found
    | cons a hs rest =>
      cases rest with
      | nil =>
        cases depth with
        | zero =>
          have same : site = ⟨context, owner, a, hs⟩ := by simpa only [holeSite, Option.some.injEq] using found.symm
          subst site
          rw [splice]
        | succ depth =>
          rw [holeSite] at found
          simp only [splice, Expr.compare, columnCompare_self,
            spliceForests_compare depth hs replacement found]
          cases replacement.compare (listCompare Ord.compare) (.cons site.terminal site.attached .nil) <;> rfl
      | cons b ks t =>
        rw [holeSite] at found
        simp only [splice, Expr.compare, columnCompare_self, forests_compare_self]
        exact splice_compare depth (.cons b ks t) replacement found
  theorem spliceForests_compare {d : Nat} {context : ParentContext} {owner : Nat}
      (depth : Nat) (hs : Forests (List Nat)) (replacement : NumericalExpr) {site : HoleSite}
      (found : holeSiteForests d context owner depth hs = some site) :
      (spliceForests depth replacement hs).compare (listCompare Ord.compare) hs =
        replacement.compare (listCompare Ord.compare) (.cons site.terminal site.attached .nil) := by
    cases hs with
    | nil => simp [holeSiteForests] at found
    | cons h rest =>
      cases rest with
      | nil =>
        rw [holeSiteForests] at found
        simp only [spliceForests, Forests.compare, splice_compare depth h replacement found]
        cases replacement.compare (listCompare Ord.compare) (.cons site.terminal site.attached .nil) <;> rfl
      | cons k ks =>
        rw [holeSiteForests] at found
        simp only [spliceForests, Forests.compare, expr_compare_self]
        exact spliceForests_compare depth (.cons k ks) replacement found
end

theorem ordinary_expand_HW
    {d cap root rootDepth stopDepth index : Nat} {e stop : NumericalExpr}
    (positive : 0 < d) (legal : FiniteLegal d [] e) (ordered : HW e)
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
    HW (ascendReplace (mark cap root [] (parents d e))
      (copies (drop index rootPart) (stopDepth - rootDepth) delta donation count 1)
      (some stopDepth) delta 0) := by
  obtain ⟨stopLayer, atStop, stopSame⟩ := layerAt_exists (d := d) [] none [] stopSelected
  have atTerminal : last? stopLayer.term = some (terminal, attached) := by rw [stopSame]; exact stopLast
  let terminalContext := outerContext d stopLayer.context (dropLast stopLayer.term)
  have width := selected_parent_width stopSelected stopLast parentSelected parentLast
  have bounded : cap ≤ d := by
    have bound := (highestParent_found parentTerminal.parents 0 cap root chosen).2.1
    rw [width] at bound
    omega
  have earlierRoot : root < terminalContext.length := by
    by_cases top : cap = d
    · subst cap
      exact (selected_top_scoped parentSelected parentLast chosen atStop).1
    · have numeric := selected_low_numerical_root parentSelected parentLast chosen (by omega) atStop atTerminal
      exact Parents.label_parent_bound d terminalContext terminal cap root numeric
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
  have earlier : rootContext.length < site.context.length := by rw [rootSize]; exact earlierRoot
  have pieceOrdered : HW (.cons a hs rest) := by
    rw [← cut]
    exact (ordered.spine rootDepth rootLookup).drop index
  obtain ⟨markedPart, markedSelected, markedCut, _⟩ := actual_marked_root_piece bounded location atRoot
  have sameMarked : markedPart = rootPart := Option.some.inj (markedSelected.symm.trans partSelected)
  subst markedPart
  rw [cut] at markedCut
  let delta := (List.range cap).map (fun j => terminal[j]?.getD 0 - a[j]?.getD 0)
  let donation := if cap = d then some (dropLastForest tailForests) else none
  let result := copies (drop index rootPart) (stopDepth - rootDepth) delta donation count 1
  have replacement : HW result := by
    by_cases top : cap = d
    · subst cap
      have path := selected_top_numerical_ancestor positive parentSelected parentLast chosen atStop atTerminal
      have numerical : Parents.Ancestor (site.context ++ [Parents.label d site.context site.terminal])
          (d - 1) rootContext.length site.context.length := by
        rw [rootSize]
        exact path
      have donor := actual_marked_top_donation positive parentSelected parentLast chosen atStop atTerminal
        tailSelected tailLast site.owner
      change dropLastForest tailForests = donationAt d root site at donor
      have attachedNonempty := selected_high_terminal_attached stopSelected stopLast parentSelected parentLast chosen
      have computed := initial_copies_high_HW coherent valid pieceLegal pieceOrdered rootHole
        positive earlier attachedNonempty numerical count
      dsimp only at computed
      rw [rootSize] at computed
      dsimp only [result, donation, delta]
      rw [if_pos rfl, markedCut, donor]
      exact computed
    · have room : cap < d := by omega
      have numeric := selected_low_numerical_root parentSelected parentLast chosen room atStop atTerminal
      have selected : (Parents.label d site.context site.terminal).parents[cap]?.join = some rootContext.length := by
        rw [rootSize]
        exact numeric
      have computed := initial_copies_low_HW coherent valid pieceLegal pieceOrdered rootHole room selected count
      dsimp only at computed
      rw [rootSize] at computed
      dsimp only [result, donation, delta]
      rw [if_neg top, markedCut]
      exact computed
  have originalHole := layerAt_holeSite stopDepth e atStop atTerminal
  let whole : HoleSite := ⟨terminalContext, stopLayer.owner, terminal, attached⟩
  change holeSite d [] none stopDepth e = some whole at originalHole
  have decrease := ordinary_expand_lt positive legal stopSelected stopLast parentSelected parentLast
    chosen location rootRead partSelected tailSelected tailLast count
  change (ascendReplace (mark cap root [] (parents d e)) result (some stopDepth) delta 0).compare
    (listCompare Ord.compare) e = .lt at decrease
  change HW (ascendReplace (mark cap root [] (parents d e)) result (some stopDepth) delta 0)
  have unchanged : (mark cap root [] (parents d e)).map (fun a => shift a.1 a.2 delta 0) = e := by
    simp only [shift_zero, mark_erase, parents_erase]
  rw [ascendReplace_splice, unchanged] at decrease ⊢
  rw [splice_compare stopDepth e result originalHole] at decrease
  exact splice_HW stopDepth e result ordered replacement originalHole decrease

theorem expand_HW {d : Nat} (positive : 0 < d) {e f : NumericalExpr}
    (legal : FiniteLegal d [] e) (ordered : HW e) (count : Nat)
    (edge : expand? d e count = some f) : HW f := by
  cases outer : last? e with
  | none =>
    have same : f = .nil := by simpa only [expand?, outer, Option.pure_def, Option.some.injEq] using edge.symm
    subst f
    trivial
  | some outerColumn =>
    by_cases zero : zeroColumn outerColumn = true
    · have same : f = dropLast e := by simpa only [expand?, outer, zero, if_true, Option.pure_def, Option.some.injEq] using edge.symm
      rw [same]
      exact ordered.dropLast
    · simp only [expand?, outer] at edge
      rw [if_neg zero] at edge
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at edge
      obtain ⟨stop, stopSelected, stopColumn, stopLast, edge⟩ := edge
      obtain ⟨terminal, attached⟩ := stopColumn
      split at edge
      next specialCase =>
        have same : f = special count ((spine e).findIdx stopping) e := by
          simpa only [Option.pure_def, Option.some.injEq] using edge.symm
        obtain ⟨h, child, nonempty⟩ := specialColumn_last_nonempty specialCase
        rw [same]
        exact special_spine_HW count _ ordered stopSelected stopLast child nonempty
      next ordinary =>
        simp only [Option.bind_eq_some_iff] at edge
        obtain ⟨parentStop, parentSelected, parentColumn, parentLast, pair, chosen,
          locationPair, location, rootColumn, rootRead, rootPart, partSelected,
          tailPart, tailSelected, tailColumn, tailLast, result⟩ := edge
        obtain ⟨parentTerminal, parentAttached⟩ := parentColumn
        obtain ⟨cap, root⟩ := pair
        obtain ⟨rootDepth, index⟩ := locationPair
        obtain ⟨lastVector, lastForests⟩ := tailColumn
        have preserved := ordinary_expand_HW positive legal ordered stopSelected stopLast parentSelected parentLast
          chosen location rootRead partSelected tailSelected tailLast count
        simp only [Option.pure_def, Option.some.injEq] at result
        rw [← result]
        exact preserved

theorem Reachable.HW {d : Nat} (positive : 0 < d) {start e : NumericalExpr}
    (path : Reachable d start e) (legal : FiniteLegal d [] start) (ordered : Source.HW start) : Source.HW e := by
  induction path with
  | refl => exact ordered
  | step path edge ih => exact expand_HW positive (path.finiteLegal positive legal) ih _ edge

theorem standard_HW {d : Nat} (positive : 0 < d) {e : NumericalExpr} (standard : Standard d e) : HW e := by
  obtain ⟨k, path⟩ := standard
  exact path.HW positive (seed_finiteLegal d k positive) (seed_HW d k)

end BTnSSBMS.Source
