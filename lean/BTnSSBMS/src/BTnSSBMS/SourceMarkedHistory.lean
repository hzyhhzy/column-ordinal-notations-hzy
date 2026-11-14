import BTnSSBMS.SourceTopAncestry

/-!
Activation history along the actual right spine, including the part
before the root and the root itself. Only the last column's final forest
is entered; closed forests never enter the surrounding history.
-/
namespace BTnSSBMS.Source

/-- This is exactly the local threshold expression in the frozen mark. -/
def markThreshold (cap root : Nat) (history : List Nat) (a : ParentLabel) : Nat :=
  if history.length < root then 0
  else if history.length = root then cap else Keys.threshold cap root history a

theorem markThreshold_activation {d root cap : Nat} {context : ParentContext} {history : List Nat}
    (length : history.length = context.length) (a : List Nat) :
    markThreshold cap root history (Parents.label d context a) =
      BMS.activation (context ++ [Parents.label d context a]) root cap history context.length := by
  simp only [markThreshold, BMS.activation, length, List.getElem?_concat_length, Option.getD_some]
  rfl

theorem history_append_markThreshold {d root cap : Nat} {context : ParentContext} {history : List Nat}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    (correct : BMS.HistoryCorrect context root cap history) (length : history.length = context.length)
    (bounded : cap ≤ d) (a : List Nat) :
    BMS.HistoryCorrect (context ++ [Parents.label d context a]) root cap
      (history ++ [markThreshold cap root history (Parents.label d context a)]) := by
  have nextValid := Parents.context_valid_append_label d context valid a
  have previous := correct.extend_context (List.prefix_append ..) nextValid (by omega)
  intro i inside j
  by_cases old : i < history.length
  · rw [List.getElem?_append_left old]
    exact previous i old j
  · have same : i = history.length := by
      simp only [List.length_append, List.length_cons, List.length_nil] at inside
      omega
    subst i
    rw [List.getElem?_concat_length, Option.getD_some, markThreshold_activation length, length]
    exact BMS.activation_correct nextValid (Parents.coherent_append_label coherent a)
      root cap bounded history context.length length previous j

theorem last_mark_annotate {d root cap : Nat} {context : ParentContext} {history : List Nat}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    (correct : BMS.HistoryCorrect context root cap history) (length : history.length = context.length)
    (bounded : cap ≤ d) (e : NumericalExpr) {a : List Nat} {hs : Forests (List Nat)}
    (found : last? e = some (a, hs)) :
    let before := outerContext d context (dropLast e)
    ∃ prior, prior.length = before.length ∧ BMS.HistoryCorrect before root cap prior ∧
      last? (mark cap root history (Parents.annotate d context e)) =
        some ((a, markThreshold cap root prior (Parents.label d before a)),
          markForests cap root (prior ++ [markThreshold cap root prior (Parents.label d before a)])
            (Parents.annotateForests d (before ++ [Parents.label d before a]) hs)) := by
  cases e with
  | nil => simp [last?] at found
  | cons b ks rest =>
    cases rest with
    | nil =>
      have same : (b, ks) = (a, hs) := by simpa only [last?, Option.some.injEq] using found
      cases same
      simp only [dropLast, outerContext]
      refine ⟨history, length, correct, ?_⟩
      simp only [Parents.annotate, mark, Bool.and_false,
        Bool.false_eq_true, if_false, last?, markThreshold, Parents.label]
    | cons c js tail =>
      let next := history ++ [markThreshold cap root history (Parents.label d context b)]
      have nextCorrect := history_append_markThreshold coherent valid correct length bounded b
      have nextLength : next.length = (context ++ [Parents.label d context b]).length := by
        simp only [next, List.length_append, List.length_cons, List.length_nil, length]
      have result := last_mark_annotate (Parents.coherent_append_label coherent b)
        (Parents.context_valid_append_label d context valid b) nextCorrect nextLength bounded (.cons c js tail)
        (by simpa only [last?] using found)
      simpa only [Parents.annotate, mark, last?, dropLast, outerContext, next, markThreshold] using result

theorem layerAt_contexts {d : Nat} {context : ParentContext} {owner : Option Nat} {owners : List Nat}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    (depth : Nat) (e : NumericalExpr) {layer : SpineLayer}
    (found : layerAt d context owner owners depth e = some layer) :
    Parents.Coherent d layer.context ∧ Parents.ContextValid layer.context := by
  induction depth generalizing context owner owners e layer with
  | zero =>
    have same : layer = ⟨context, owner, owners, e⟩ := by
      simpa only [layerAt, Option.some.injEq] using found.symm
    subst layer
    exact ⟨coherent, valid⟩
  | succ depth ih =>
    simp only [layerAt, Option.bind_eq_some_iff] at found
    obtain ⟨⟨a, hs⟩, _, h, _, below⟩ := found
    exact ih (Parents.coherent_append_label (outerContext_coherent coherent (dropLast e)) a)
      (Parents.context_valid_append_label d _ (outerContext_valid valid (dropLast e)) a) h below

theorem marked_annotate_layer_history {d root cap : Nat} {context : ParentContext}
    {history : List Nat} {owner : Option Nat} {owners : List Nat}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    (correct : BMS.HistoryCorrect context root cap history) (length : history.length = context.length)
    (bounded : cap ≤ d) (depth : Nat) (e : NumericalExpr) {layer : SpineLayer}
    (found : layerAt d context owner owners depth e = some layer) :
    ∃ prior, prior.length = layer.context.length ∧ BMS.HistoryCorrect layer.context root cap prior ∧
      (spine (mark cap root history (Parents.annotate d context e)))[depth]? =
        some (mark cap root prior (Parents.annotate d layer.context layer.term)) := by
  induction depth generalizing context history owner owners e layer with
  | zero =>
    have same : layer = ⟨context, owner, owners, e⟩ := by
      simpa only [layerAt, Option.some.injEq] using found.symm
    subst layer
    exact ⟨history, length, correct, rfl⟩
  | succ depth ih =>
    simp only [layerAt, Option.bind_eq_some_iff] at found
    obtain ⟨⟨a, hs⟩, last, h, child, below⟩ := found
    obtain ⟨prior, size, exactHistory, markedLast⟩ := last_mark_annotate coherent valid correct length bounded e last
    let before := outerContext d context (dropLast e)
    let threshold := markThreshold cap root prior (Parents.label d before a)
    have nextCorrect := history_append_markThreshold (outerContext_coherent coherent (dropLast e))
      (outerContext_valid valid (dropLast e)) exactHistory size bounded a
    have nextLength : (prior ++ [threshold]).length = (before ++ [Parents.label d before a]).length := by
      simp only [List.length_append, List.length_cons, List.length_nil, size, before]
    obtain ⟨finalHistory, finalLength, finalCorrect, finalLookup⟩ := ih
      (Parents.coherent_append_label (outerContext_coherent coherent (dropLast e)) a)
      (Parents.context_valid_append_label d _ (outerContext_valid valid (dropLast e)) a)
      nextCorrect nextLength h below
    refine ⟨finalHistory, finalLength, finalCorrect, ?_⟩
    rw [spine_get_succ]
    simp only [lastChild?, markedLast, Option.bind_some,
      markForests_last cap root _ _ (lastForest_annotate d _ hs child)]
    exact finalLookup

/-- The donation selected from the actual global marking is precisely
the fixed marked terminal material used in the all-copy theorem. -/
theorem actual_marked_top_donation {d depth root : Nat} (positive : 0 < d)
    {e : NumericalExpr} {parentPart : ParentExpr} {a : ParentLabel} {hs : Forests ParentLabel}
    (parentSelected : (spine (parents d e))[depth]? = some parentPart)
    (parentLast : last? parentPart = some (a, hs))
    (chosen : highestParent 0 a.parents = some (d, root))
    {layer : SpineLayer} (found : layerAt d [] none [] depth e = some layer)
    {terminal : List Nat} {attached : Forests (List Nat)}
    (atLast : last? layer.term = some (terminal, attached))
    {part : MarkedExpr} (selected : (spine (mark d root [] (parents d e)))[depth]? = some part)
    {markedTerminal : List Nat × Nat} {markedAttached : Forests (List Nat × Nat)}
    (last : last? part = some (markedTerminal, markedAttached)) (owner : Option Nat) :
    dropLastForest markedAttached = donationAt d root
      ⟨outerContext d layer.context (dropLast layer.term), owner, terminal, attached⟩ := by
  have states := layerAt_contexts (Parents.empty_coherent d) Parents.empty_context_valid depth e found
  have beforeCoherent := outerContext_coherent states.1 (dropLast layer.term)
  have beforeValid := outerContext_valid (d := d) states.2 (dropLast layer.term)
  have earlier := (selected_top_scoped parentSelected parentLast chosen found).1
  have path := selected_top_numerical_ancestor positive parentSelected parentLast chosen found atLast
  obtain ⟨prior, size, correct, lookup⟩ := marked_annotate_layer_history
    (Parents.empty_coherent d) Parents.empty_context_valid
    (show BMS.HistoryCorrect [] root d [] from by intro i bound; simp at bound)
    rfl (Nat.le_refl d) depth e found
  rw [← mark_parents_eq_numeric d d root [] (Nat.le_refl d) e] at lookup
  have same : part = mark d root prior (Parents.annotate d layer.context layer.term) :=
    Option.some.inj (selected.symm.trans lookup)
  rw [same] at last
  obtain ⟨finalHistory, finalLength, finalCorrect, markedLast⟩ :=
    last_mark_annotate states.1 states.2 correct size (Nat.le_refl d) layer.term atLast
  have top : markThreshold d root finalHistory
      (Parents.label d (outerContext d layer.context (dropLast layer.term)) terminal) = d := by
    rw [markThreshold, if_neg (by omega), if_neg (by omega)]
    exact Keys.threshold_at_top_ancestor beforeCoherent beforeValid finalCorrect finalLength earlier positive terminal path
  rw [top] at markedLast
  have attachedEqual := congrArg Prod.snd (Option.some.inj (last.symm.trans markedLast))
  dsimp only at attachedEqual
  rw [attachedEqual]
  exact (donationAt_actual_history
    (site := ⟨outerContext d layer.context (dropLast layer.term), owner, terminal, attached⟩)
    (history := finalHistory) beforeCoherent beforeValid finalCorrect finalLength).symm

end BTnSSBMS.Source
