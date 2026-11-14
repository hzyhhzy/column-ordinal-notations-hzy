import BTnSSBMS.SourceCopyDescent
import BTnSSBMS.SourceEncodingOrder

/-!
Strict raw-order descent for every nonempty, finite-legal source expansion.
This is used by the source block-order argument's delayed-change step.
It is not well-foundedness of the raw order or the BMS upper-bound theorem.
-/
namespace BTnSSBMS.Source

theorem ordinary_expand_lt
    {d cap root rootDepth stopDepth index : Nat} {e stop : NumericalExpr}
    (positive : 0 < d) (legal : FiniteLegal d [] e)
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
    (ascendReplace (mark cap root [] (parents d e))
      (copies (drop index rootPart) (stopDepth - rootDepth) delta donation count 1)
      (some stopDepth) delta 0).compare (listCompare Ord.compare) e = .lt := by
  obtain ⟨stopLayer, atStop, stopSame⟩ := layerAt_exists (d := d) [] none [] stopSelected
  have atTerminal : last? stopLayer.term = some (terminal, attached) := by rw [stopSame]; exact stopLast
  let terminalContext := outerContext d stopLayer.context (dropLast stopLayer.term)
  have stopLegal := (layerAt_legal (Parents.empty_coherent d) Parents.empty_context_valid stopDepth e legal
    (by intro bound impossible; cases impossible) atStop).2.2.1.last_context atTerminal
  change FiniteLegal d terminalContext (.cons terminal attached .nil) at stopLegal
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
  have coordinates := holeSite_root_coordinates rootHole earlier
  have contexts := holeSite_contexts coherent valid (stopDepth - rootDepth) (.cons a hs rest) rootHole
  have originalHole := layerAt_holeSite stopDepth e atStop atTerminal
  let whole : HoleSite := ⟨terminalContext, stopLayer.owner, terminal, attached⟩
  change holeSite d [] none stopDepth e = some whole at originalHole
  obtain ⟨markedPart, markedSelected, markedCut, _⟩ := actual_marked_root_piece bounded location atRoot
  have sameMarked : markedPart = rootPart := Option.some.inj (markedSelected.symm.trans partSelected)
  subst markedPart
  rw [cut] at markedCut
  let delta := (List.range cap).map (fun j => terminal[j]?.getD 0 - a[j]?.getD 0)
  let donation := if cap = d then some (dropLastForest tailForests) else none
  let result := copies (drop index rootPart) (stopDepth - rootDepth) delta donation count 1
  apply marked_splice_lt cap root stopDepth delta e result originalHole
  change result.compare (listCompare Ord.compare) (.cons terminal attached .nil) = .lt
  cases count with
  | zero => simp only [result, copies, Expr.compare]
  | succ count =>
    obtain ⟨ks, tail, shape, donated⟩ := marked_root_copies_first_head a hs rest delta donation count 1
      (holeSite_root_not_terminal rootHole earlier)
    rw [rootSize, ← markedCut] at shape
    change result = .cons (shift a cap delta 1) ks tail at shape
    rw [shape]
    by_cases top : cap = d
    · subst cap
      have path := selected_top_numerical_ancestor positive parentSelected parentLast chosen atStop atTerminal
      have rootValues : ∀ j, j < d → a[j]?.getD 0 < terminal[j]?.getD 0 := by
        intro j room
        have lowerPath := path.lower_row (lower := j) (Parents.coherent_append_label contexts.1 terminal) (by omega) (by omega)
        have lower := lowerPath.reading_lt (Parents.coherent_append_label contexts.1 terminal)
          (by change root ≠ terminalContext.length; omega)
        rw [Parents.reading_append_label,
          ← Parents.reading_prefix (List.prefix_append terminalContext [Parents.label d terminalContext terminal])
            j root earlierRoot] at lower
        change (terminalContext[root]?.getD default).coordinates[j]?.getD 0 < terminal[j]?.getD 0 at lower
        have rootAt : (terminalContext[root]?.getD default).coordinates = a := by
          simpa only [site, rootSize] using coordinates
        rwa [rootAt] at lower
      have headSame := first_high_shift_eq pieceLegal.1 stopLegal.1
        (fun j room => Nat.le_of_lt (rootValues j room))
      change shift a d delta 1 = terminal at headSame
      have donor := actual_marked_top_donation positive parentSelected parentLast chosen atStop atTerminal
        tailSelected tailLast site.owner
      change dropLastForest tailForests = donationAt d root site at donor
      have newForests := donated (dropLastForest tailForests) (by simp only [donation, if_true])
      rw [Nat.sub_self, donor, donationAt_zero] at newForests
      have attachedNonempty := selected_high_terminal_attached stopSelected stopLast parentSelected parentLast chosen
      rw [headSame, newForests]
      exact by simp only [site, Expr.compare, columnCompare_self, dropLastForest_lt attachedNonempty]
    · have room : cap < d := by omega
      have numeric := selected_low_numerical_root parentSelected parentLast chosen room atStop atTerminal
      have rootValues : ∀ j, j ≤ cap → a[j]?.getD 0 < terminal[j]?.getD 0 := by
        intro j small
        have lower := Parents.label_root_lower_value contexts.1 contexts.2 terminal room numeric small
        change (terminalContext[root]?.getD default).coordinates[j]?.getD 0 < terminal[j]?.getD 0 at lower
        have rootAt : (terminalContext[root]?.getD default).coordinates = a := by
          simpa only [site, rootSize] using coordinates
        rwa [rootAt] at lower
      have smaller := first_low_shift_lt (by rw [pieceLegal.1]; exact room)
        (by rw [stopLegal.1]; exact room) rootValues
      change listCompare Ord.compare (shift a cap delta 1) terminal = .lt at smaller
      simp only [Expr.compare, smaller]

/-- Every successful nonempty step of the actual frozen function strictly
decreases the raw recursive comparison. No block invariant is assumed. -/
theorem expand_lt {d : Nat} (positive : 0 < d) {e f : NumericalExpr}
    (legal : FiniteLegal d [] e) (nonempty : e ≠ .nil) (count : Nat)
    (edge : expand? d e count = some f) : f.compare (listCompare Ord.compare) e = .lt := by
  cases outer : last? e with
  | none => exact False.elim (nonempty ((last_none_iff e).mp outer))
  | some outerColumn =>
    by_cases zero : zeroColumn outerColumn = true
    · have result : f = dropLast e := by simpa only [expand?, outer, zero, if_true, Option.pure_def, Option.some.injEq] using edge.symm
      rw [result]
      exact dropLast_lt nonempty
    · simp only [expand?, outer] at edge
      rw [if_neg zero] at edge
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at edge
      obtain ⟨stop, stopSelected, stopColumn, stopLast, edge⟩ := edge
      obtain ⟨terminal, attached⟩ := stopColumn
      split at edge
      next specialCase =>
        have result : f = special count ((spine e).findIdx stopping) e := by
          simpa only [Option.pure_def, Option.some.injEq] using edge.symm
        obtain ⟨h, child, childNonempty⟩ := specialColumn_last_nonempty specialCase
        rw [result]
        exact special_spine_lt count _ stopSelected stopLast child childNonempty
      next ordinary =>
        simp only [Option.bind_eq_some_iff] at edge
        obtain ⟨parentStop, parentSelected, parentColumn, parentLast, pair, chosen,
          locationPair, location, rootColumn, rootRead, rootPart, partSelected,
          tailPart, tailSelected, tailColumn, tailLast, result⟩ := edge
        obtain ⟨parentTerminal, parentAttached⟩ := parentColumn
        obtain ⟨cap, root⟩ := pair
        obtain ⟨rootDepth, index⟩ := locationPair
        obtain ⟨lastVector, lastForests⟩ := tailColumn
        have smaller := ordinary_expand_lt positive legal stopSelected stopLast parentSelected parentLast
          chosen location rootRead partSelected tailSelected tailLast count
        simp only [Option.pure_def, Option.some.injEq] at result
        rw [← result]
        exact smaller

theorem standard_expand_lt {d : Nat} (positive : 0 < d) {e f : NumericalExpr}
    (standard : Standard d e) (nonempty : e ≠ .nil) (count : Nat)
    (edge : expand? d e count = some f) : f.compare (listCompare Ord.compare) e = .lt :=
  expand_lt positive (standard_finiteLegal positive standard) nonempty count edge

theorem expr_compare_lt_trans (a b c : NumericalExpr)
    (first : a.compare (listCompare Ord.compare) b = .lt)
    (second : b.compare (listCompare Ord.compare) c = .lt) :
    a.compare (listCompare Ord.compare) c = .lt :=
  Expr.compare_lt_trans _
    (fun _ _ same => listCompare_eq_imp _ (fun _ _ h => Nat.compare_eq_eq.mp h) _ _ same)
    (fun x y z xy yz => listCompare_lt_trans _ (fun _ _ h => Nat.compare_eq_eq.mp h)
      (fun _ _ _ ab bc => Nat.compare_eq_lt.mpr (Nat.lt_trans (Nat.compare_eq_lt.mp ab) (Nat.compare_eq_lt.mp bc)))
      x y z xy yz) a b c first second

/-- Every finite actual path is nonincreasing, and every nontrivial endpoint
change is strict. This does not establish absence of infinite descending paths. -/
theorem reachable_compare {d : Nat} (positive : 0 < d) {start e : NumericalExpr}
    (legal : FiniteLegal d [] start) (path : Reachable d start e) :
    FiniteLegal d [] e ∧ (e = start ∨ e.compare (listCompare Ord.compare) start = .lt) := by
  induction path with
  | refl => exact ⟨legal, Or.inl rfl⟩
  | @step count middle next path edge ih =>
    refine ⟨expand_finiteLegal positive ih.1 count edge, ?_⟩
    by_cases empty : middle = .nil
    · have same : next = middle := by
        rw [empty, expand_empty] at edge
        exact (Option.some.inj edge).symm.trans empty.symm
      rw [same]
      exact ih.2
    · have less := expand_lt positive ih.1 empty count edge
      right
      rcases ih.2 with same | prior
      · rwa [same] at less
      · exact expr_compare_lt_trans next middle start less prior

theorem no_return_after_step {d : Nat} (positive : 0 < d) {e f : NumericalExpr}
    (legal : FiniteLegal d [] e) (nonempty : e ≠ .nil) (count : Nat)
    (edge : expand? d e count = some f) : ¬ Reachable d f e := by
  intro path
  have down := expand_lt positive legal nonempty count edge
  have back := (reachable_compare positive (expand_finiteLegal positive legal count edge) path).2
  rcases back with same | strict
  · rw [same, expr_compare_self] at down
    cases down
  · have impossible := expr_compare_lt_trans e f e strict down
    rw [expr_compare_self] at impossible
    cases impossible

end BTnSSBMS.Source

namespace BTnSSBMS.Encoder

/-- Actual source expansion strictly decreases its raw matrix encoding.
This is not a simulation by BMS expansion steps or BMS standardness. -/
theorem standard_expansion_lt {d : Nat} (positive : 0 < d) {e f : NumericalExpr}
    (standard : Source.Standard d e) (nonempty : e ≠ .nil) (count : Nat)
    (edge : Source.expand? d e count = some f) :
    matrixCompare (fromSource d f) (fromSource d e) = .lt := by
  rw [standard_compare positive (Source.standard_closed d e f count standard edge) standard]
  exact Source.standard_expand_lt positive standard nonempty count edge

end BTnSSBMS.Encoder
