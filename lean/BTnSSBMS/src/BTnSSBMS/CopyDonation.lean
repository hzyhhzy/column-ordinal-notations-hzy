import BTnSSBMS.CopyAnnotation

/-!
The highest numerical seam has two different source views of the same
new target head: the next ordinary copy uses the old root at phase+1,
whereas donated forests use the terminal at the previous phase.
-/
namespace BTnSSBMS.Keys

theorem threshold_at_top_ancestor {d : Nat} {source : ParentContext} {history : List Nat}
    {root : Nat} (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
    (correct : BMS.HistoryCorrect source root d history) (length : history.length = source.length)
    (afterRoot : root < source.length) (positive : 0 < d) (a : List Nat)
    (path : Parents.Ancestor (source ++ [Parents.label d source a]) (d - 1) root source.length) :
    threshold d root history (Parents.label d source a) = d := by
  have correctAt := threshold_at_label coherent valid correct length afterRoot (Nat.le_refl d) a
  apply Nat.le_antisymm
  · by_cases done : threshold d root history (Parents.label d source a) ≤ d
    · exact done
    have active : d < threshold d root history (Parents.label d source a) := by omega
    have impossible := ((correctAt d).mp active).1
    omega
  · by_cases done : d ≤ threshold d root history (Parents.label d source a)
    · exact done
    have below : threshold d root history (Parents.label d source a) < d := by omega
    have lower := path.lower_row (Parents.coherent_append_label coherent a)
      (by omega : d - 1 < d) (by omega : threshold d root history (Parents.label d source a) ≤ d - 1)
    have impossible := (correctAt _).mpr ⟨below, lower⟩
    omega

end BTnSSBMS.Keys

namespace BTnSSBMS.Source

theorem ShiftView.zero {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    (unit : Parents.UnitSteps d context) (root cap : Nat) (delta : List Nat)
    (inside : root < context.length) (bounded : cap ≤ d) :
    ShiftView d context context (List.range context.length)
      (BMS.thresholdPrefix context root cap context.length) root cap delta 0 := by
  refine ⟨coherent, valid, coherent, valid, unit, Parents.numericalView_identity d context,
    BMS.thresholdPrefix_length .., BMS.thresholdPrefix_correct valid coherent root cap bounded _,
    inside, bounded, ?_⟩
  intro p before j room
  rw [Parents.point_range _ p before]
  simp only [Nat.mul_zero, ite_self, Nat.add_zero]

/-- The complete shifted vectors agree, not just their row-zero values. -/
theorem top_shift_eq (d : Nat) (root terminal delta : List Nat) (phase : Nat)
    (rootWidth : root.length = d) (terminalWidth : terminal.length = d)
    (difference : ∀ j, j < d → terminal[j]?.getD 0 = root[j]?.getD 0 + delta[j]?.getD 0) :
    shift root d delta (phase + 1) = shift terminal d delta phase := by
  apply List.ext_getElem
  · simp only [shift_width, rootWidth, terminalWidth]
  · intro j left right
    have room : j < d := by simpa only [shift_width, rootWidth] using left
    have result : (shift root d delta (phase + 1))[j]?.getD 0 =
        (shift terminal d delta phase)[j]?.getD 0 := by
      rw [shift_value _ _ _ _ j (by omega), shift_value _ _ _ _ j (by omega),
        if_pos room, if_pos room, difference j room, Nat.mul_succ]
      omega
    simpa only [List.getElem?_eq_getElem left, List.getElem?_eq_getElem right, Option.getD_some] using result

/-- The actual highest-class new head supplies the ordinary root view
for the next phase. Its old-root ancestors are lifted through the virtual
terminal, whose computed target vector is exactly that new head. -/
theorem ShiftView.restart_high {d : Nat} {source target : ParentContext}
    {visible history : List Nat} {root : Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d source target visible history root d delta phase) (positive : 0 < d)
    (terminal : List Nat) (width : terminal.length = d)
    (terminalUnit : Parents.UnitSteps d (source ++ [Parents.label d source terminal]))
    (rootWidth : (source[root]?.getD default).coordinates.length = d)
    (path : Parents.Ancestor (source ++ [Parents.label d source terminal]) (d - 1) root source.length)
    (difference : ∀ j, j < d → terminal[j]?.getD 0 = Parents.reading source j root + delta[j]?.getD 0) :
    let nextHead := shift (source[root]?.getD default).coordinates d delta (phase + 1)
    ShiftView d (source.take (root + 1)) (target ++ [Parents.label d target nextHead])
      (visible.take root ++ [target.length]) (List.replicate root 0 ++ [d]) root d delta (phase + 1) := by
  dsimp only
  let nextHead := shift (source[root]?.getD default).coordinates d delta (phase + 1)
  have threshold := Keys.threshold_at_top_ancestor scope.sourceCoherent scope.sourceValid
    scope.historyCorrect scope.historyLength scope.afterRoot positive terminal path
  have same : nextHead = shift terminal d delta phase := top_shift_eq d _ terminal delta phase rootWidth width difference
  have next := scope.append terminal width terminalUnit
  dsimp only at next
  rw [threshold, ← same] at next
  have targetPrefix := List.prefix_append target [Parents.label d target nextHead]
  have sourceLength : (source.take (root + 1)).length = root + 1 := by
    simp only [List.length_take]; have bound := scope.afterRoot; omega
  have visibleLength : (visible.take root).length = root := by
    simp only [List.length_take, scope.view.length]; have bound := scope.afterRoot; omega
  have nextView : Parents.NumericalView d (source.take (root + 1))
      (target ++ [Parents.label d target nextHead]) (visible.take root ++ [target.length]) := by
    apply scope.view.reset_root scope.sourceValid scope.afterRoot targetPrefix (position := target.length) (by simp) (by simp)
    intro j room p before originalPath
    have lower := path.lower_row next.sourceCoherent (by omega : d - 1 < d) (by omega : j ≤ d - 1)
    have joined := (originalPath.prefix (List.prefix_append source [Parents.label d source terminal])).trans lower
    have transported := next.view.lift j room p source.length (by simp; have bound := scope.afterRoot; omega)
      (by simp) joined
    rw [Parents.point_append_old visible p target.length (by rw [scope.view.length]; have bound := scope.afterRoot; omega),
      ← scope.view.length, Parents.point_append_last] at transported
    exact transported
  refine ⟨scope.sourceCoherent.restrict (List.take_prefix ..), scope.sourceValid.restrict (List.take_prefix ..),
    next.targetCoherent, next.targetValid, next.targetUnit, nextView, by simp [sourceLength],
    BMS.HistoryCorrect.at_root (scope.sourceValid.restrict (List.take_prefix ..)) root d,
    by omega, Nat.le_refl d, ?_⟩
  intro p inside j room
  by_cases before : p < root
  · have pBound : p < source.length := by have bound := scope.afterRoot; omega
    have inactive := scope.historyCorrect.before scope.sourceValid (by rw [scope.historyLength]; exact pBound) before
    rw [Parents.point_append_old _ p target.length (by omega), Parents.point_take visible root p before,
      List.getElem?_append_left (show p < (List.replicate root 0).length by simpa using before),
      List.getElem?_replicate_of_lt before, Option.getD_some, if_neg (by omega), Nat.add_zero,
      ← Parents.reading_prefix targetPrefix j (Parents.point visible p) (scope.view.bounded p pBound),
      scope.values p pBound j room, inactive, if_neg (by omega), Nat.add_zero,
      Parents.reading_prefix (List.take_prefix (root + 1) source) j p inside]
    rfl
  · have sameRoot : p = root := by omega
    subst p
    have rootPoint : Parents.point (visible.take root ++ [target.length]) root = target.length := by
      simpa only [visibleLength] using Parents.point_append_last (visible.take root) target.length
    have marked : (List.replicate root 0 ++ [d])[root]? = some d := by
      simpa only [List.length_replicate] using
        (List.getElem?_concat_length (l := List.replicate root 0) (a := d))
    rw [rootPoint, marked, Option.getD_some, Parents.reading_append_label,
      Parents.reading_prefix (List.take_prefix (root + 1) source) j root inside]
    exact shift_value _ _ _ _ j (by omega)

/-- Previous-phase donation in its actual new owner context. The forests
are shifted at phase, while the new ordinary root is at phase+1. The whole
donated list, including arbitrary nesting and owner separation, is checked. -/
theorem ShiftView.donation_finiteLegal {d : Nat} {source target : ParentContext}
    {visible history : List Nat} {root : Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d source target visible history root d delta phase) (positive : 0 < d)
    (terminal : List Nat) (width : terminal.length = d)
    (terminalUnit : Parents.UnitSteps d (source ++ [Parents.label d source terminal]))
    (rootWidth : (source[root]?.getD default).coordinates.length = d)
    (path : Parents.Ancestor (source ++ [Parents.label d source terminal]) (d - 1) root source.length)
    (difference : ∀ j, j < d → terminal[j]?.getD 0 = Parents.reading source j root + delta[j]?.getD 0)
    (hs : Forests (List Nat))
    (legal : FiniteLegalForests d (source ++ [Parents.label d source terminal]) (terminal[0]?.getD 0) hs) :
    let nextHead := shift (source[root]?.getD default).coordinates d delta (phase + 1)
    FiniteLegalForests d (target ++ [Parents.label d target nextHead]) (nextHead[0]?.getD 0)
      (copiedForests d root d delta phase (source ++ [Parents.label d source terminal]) (history ++ [d]) hs) := by
  dsimp only
  have threshold := Keys.threshold_at_top_ancestor scope.sourceCoherent scope.sourceValid
    scope.historyCorrect scope.historyLength scope.afterRoot positive terminal path
  have same := top_shift_eq d (source[root]?.getD default).coordinates terminal delta phase rootWidth width difference
  have next := scope.append terminal width terminalUnit
  dsimp only at next
  rw [threshold, ← same] at next
  have result := copiedForests_finiteLegal next positive source.length (by simp)
    (by simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_sub_cancel]; exact .refl _) hs
    (by rw [Parents.reading_append_label]; exact legal)
  rw [← scope.view.length, Parents.point_append_last, Parents.reading_append_label] at result
  exact result

end BTnSSBMS.Source
