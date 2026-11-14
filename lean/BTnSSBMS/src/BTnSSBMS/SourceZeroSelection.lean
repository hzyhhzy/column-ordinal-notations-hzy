import BTnSSBMS.SourceZeroGeometry

/-! The actual first stopping layer forces a zero-class root to stay in
that same forest. This is a consequence of the frozen special test, not
an extra restriction on the source domain. -/
namespace BTnSSBMS.Source

theorem stopping_before {e part : NumericalExpr} {depth : Nat}
    (selected : (spine e)[depth]? = some part)
    (earlier : depth < (spine e).findIdx stopping) : stopping part = false := by
  obtain ⟨inside, same⟩ := List.getElem?_eq_some_iff.mp selected
  have result := List.not_of_lt_findIdx earlier
  rw [same] at result
  exact result

theorem selected_zero_root_in_layer {d root depth : Nat} {e stop : NumericalExpr}
    (positive : 0 < d) (legal : FiniteLegal d [] e)
    (first : depth = (spine e).findIdx stopping)
    (stopSelected : (spine e)[depth]? = some stop)
    {terminal : List Nat} {attached : Forests (List Nat)}
    (stopLast : last? stop = some (terminal, attached))
    {parentStop : ParentExpr} {parentTerminal : ParentLabel} {parentAttached : Forests ParentLabel}
    (parentSelected : (spine (parents d e))[depth]? = some parentStop)
    (parentLast : last? parentStop = some (parentTerminal, parentAttached))
    (chosen : highestParent 0 parentTerminal.parents = some (0, root))
    {layer : SpineLayer} (atStop : layerAt d [] none [] depth e = some layer) :
    layer.context.length ≤ root := by
  have leaf := selected_low_terminal_leaf positive legal positive stopSelected stopLast
    parentSelected parentLast chosen
  subst attached
  have tailZero := selected_zero_terminal_tail legal stopSelected stopLast parentSelected parentLast chosen
  have stopSame : layer.term = stop := by
    have equation := layerAt_term d [] none [] depth e
    rw [atStop, Option.map_some, stopSelected] at equation
    exact Option.some.inj equation
  have last : last? layer.term = some (terminal, .nil) := by rw [stopSame]; exact stopLast
  have numeric := selected_low_numerical_root parentSelected parentLast chosen positive atStop last
  by_cases lower : layer.context.length ≤ root
  · exact lower
  have outside : root < layer.context.length := Nat.lt_of_not_ge lower
  cases depth with
  | zero =>
    have same : layer = ⟨[], none, [], e⟩ := by
      simpa only [layerAt, Option.some.injEq] using atStop.symm
    subst layer
    simp at outside
  | succ depth =>
    have previous := layerAt_add d [] none [] depth 1 e
    rw [atStop] at previous
    obtain ⟨prior, atPrior, childLayer⟩ := Option.bind_eq_some_iff.mp previous
    simp only [layerAt, Option.bind_eq_some_iff] at childLayer
    obtain ⟨⟨owner, forests⟩, previousLast, h, child, same⟩ := childLayer
    have layerEq : layer = ⟨
        outerContext d prior.context (dropLast prior.term) ++
          [Parents.label d (outerContext d prior.context (dropLast prior.term)) owner],
        some (owner[0]?.getD 0),
        prior.owners ++ [(outerContext d prior.context (dropLast prior.term)).length], h⟩ := by
      simpa only [Option.some.injEq] using same.symm
    subst layer
    have state := layerAt_legal (Parents.empty_coherent d) Parents.empty_context_valid depth e legal
      (by intro bound impossible; cases impossible) atPrior
    have lastLegal := state.2.2.1.last_context previousLast
    have inner := lastLegal.2.2.2.1.last child
    have special := zero_parent_outside_forest_special positive
      (outerContext d prior.context (dropLast prior.term)) owner forests child
      inner.2 inner.1 last tailZero numeric outside
    have priorLookup : (spine e)[depth]? = some prior.term := by
      have equation := layerAt_term d [] none [] depth e
      simpa only [atPrior, Option.map_some] using equation.symm
    have notStop := stopping_before priorLookup (by omega)
    simp only [stopping, previousLast, special, Bool.true_or] at notStop
    cases notStop

theorem locateRoot_same_layer (sp : List (Expr α)) (root rootDepth index depth : Nat)
    (found : locateRoot sp root = some (rootDepth, index)) {part : Expr α}
    (selected : sp[depth]? = some part)
    (lower : ((sp.take depth).map length).sum ≤ root)
    (upper : root < ((sp.take depth).map length).sum + length part) : rootDepth = depth := by
  induction sp generalizing root rootDepth index depth with
  | nil => simp at selected
  | cons head rest ih =>
    cases depth with
    | zero =>
      have same : head = part := by simpa only [List.getElem?_cons_zero, Option.some.injEq] using selected
      subst part
      simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add] at upper
      rw [locateRoot, if_pos upper] at found
      exact (congrArg Prod.fst (Option.some.inj found)).symm
    | succ depth =>
      have next : rest[depth]? = some part := by simpa only [List.getElem?_cons_succ] using selected
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons] at lower upper
      have beyond : ¬root < length head := by omega
      rw [locateRoot, if_neg beyond] at found
      obtain ⟨⟨nextDepth, nextIndex⟩, child, same⟩ := Option.map_eq_some_iff.mp found
      have nextLower : ((rest.take depth).map length).sum ≤ root - length head := by omega
      have nextUpper : root - length head < ((rest.take depth).map length).sum + length part := by omega
      have equal := ih (root - length head) nextDepth nextIndex depth child next nextLower nextUpper
      have depthEq := congrArg Prod.fst same
      dsimp only at depthEq
      omega

end BTnSSBMS.Source
