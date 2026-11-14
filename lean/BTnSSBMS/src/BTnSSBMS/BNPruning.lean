import BTnSSBMS.BNSpecial

/-! BN at index zero of every successful frozen FS branch, including
ordinary copying. The result is actual last-spine pruning, not a new
zero-index convention. Positive-index ordinary closure remains separate. -/
namespace BTnSSBMS.Source

theorem modifyLastForest_le (f : NumericalExpr → NumericalExpr) (hs : Forests (List Nat))
    (lower : ∀ h, lastForest? hs = some h → ExprLE (f h) h) :
    (modifyLastForest f hs).compare (listCompare Ord.compare) hs ≠ .gt := by
  cases hs with
  | nil => simp only [modifyLastForest, Forests.compare]; decide
  | cons h rest =>
    cases rest with
    | nil =>
      have small := lower h (by rw [lastForest?])
      unfold ExprLE at small
      simp only [modifyLastForest, Forests.compare]
      cases order : (f h).compare (listCompare Ord.compare) h <;> simp_all
    | cons k ks =>
      simp only [modifyLastForest, Forests.compare, expr_compare_self]
      exact modifyLastForest_le f (.cons k ks) (fun h found => lower h (by simpa only [lastForest?] using found))

theorem pruneAt_le (depth : Nat) (e : NumericalExpr) : ExprLE (pruneAt depth e) e := by
  induction depth generalizing e with
  | zero => exact dropLast_le e
  | succ depth ih =>
    rw [pruneAt]
    exact modifyLast_forests_le (fun _ hs => modifyLastForest (pruneAt depth) hs) e
      (fun _ hs _ => modifyLastForest_le (pruneAt depth) hs (fun h _ => ih h))

theorem pruneAt_BN (depth : Nat) {d : Nat} {context : ParentContext} {e : NumericalExpr}
    (ordered : BN d context e) (positive : 0 < d) (legal : FiniteLegal d context e) :
    BN d context (pruneAt depth e) := by
  induction depth generalizing context e with
  | zero => exact ordered.dropLast positive legal
  | succ depth ih =>
    rw [pruneAt]
    apply ordered.modifyLastForests positive legal (fun _ hs => modifyLastForest (pruneAt depth) hs)
    · intro ctx a hs _ finite good
      exact good.modifyLast finite.2.2.2.1 (pruneAt depth) (fun _ _ hLegal hGood => ih hGood hLegal)
    · intro _ hs _
      exact modifyLastForest_le (pruneAt depth) hs (fun h _ => pruneAt_le depth h)

theorem expand_zero_index_BN {d : Nat} {context : ParentContext} {e f : NumericalExpr}
    (ordered : BN d context e) (positive : 0 < d) (legal : FiniteLegal d context e)
    (step : expand? d e 0 = some f) : BN d context f := by
  simp only [expand?] at step
  split at step
  · simp only [Option.pure_def, Option.some.injEq] at step
    subst f
    trivial
  next last atLast =>
    split at step
    · simp only [Option.pure_def, Option.some.injEq] at step
      subst f
      exact ordered.dropLast positive legal
    next nonzero =>
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at step
      obtain ⟨stop, selected, stopColumn, atStop, step⟩ := step
      split at step
      · rename_i specialCase
        simp only [Option.pure_def, Option.some.injEq] at step
        subst f
        obtain ⟨h, child, nonempty⟩ := specialColumn_last_nonempty specialCase
        exact special_spine_BN 0 _ ordered positive legal selected atStop child nonempty
      next ordinary =>
        simp only [Option.bind_eq_some_iff] at step
        obtain ⟨stopP, _, stopLabel, _, rootPair, _, layerPair, _, rootCol, _,
          rootPart, _, tailPart, _, tailColumn, _, result⟩ := step
        simp only [copies, Option.pure_def, ascendReplace_empty_zero, mark_erase, parents_erase,
          Option.some.injEq] at result
        subst f
        exact pruneAt_BN _ ordered positive legal

end BTnSSBMS.Source
