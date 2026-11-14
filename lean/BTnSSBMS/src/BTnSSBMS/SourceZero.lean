import BTnSSBMS.SourcePruning

/-! Every defined index-zero expansion preserves finite legality,
including all ordinary-copy and donation branches. This does not yet
establish that ordinary expansions are always defined. -/
namespace BTnSSBMS

mutual
  theorem Expr.map_map (f : α → β) (g : β → γ) (e : Expr α) :
      (e.map f).map g = e.map (fun a => g (f a)) := by
    cases e with
    | nil => rfl
    | cons a hs t => simp only [Expr.map, Forests.map_map f g hs, Expr.map_map f g t]
  theorem Forests.map_map (f : α → β) (g : β → γ) (hs : Forests α) :
      (hs.map f).map g = hs.map (fun a => g (f a)) := by
    cases hs with
    | nil => rfl
    | cons h rest => simp only [Forests.map, Expr.map_map f g h, Forests.map_map f g rest]
end

namespace Source

mutual
  theorem fillTop_erase (d : Nat) (context : KeyContext) (owners : List Nat) (e : ParentExpr) :
      (fillTop d context owners e).map ParentLabel.coordinates = e.map ParentLabel.coordinates := by
    cases e with
    | nil => rfl
    | cons a hs t => simp only [fillTop, Expr.map, fillTopForests_erase, fillTop_erase]
  theorem fillTopForests_erase (d : Nat) (context : KeyContext) (owners : List Nat) (hs : Forests ParentLabel) :
      (fillTopForests d context owners hs).map ParentLabel.coordinates = hs.map ParentLabel.coordinates := by
    cases hs with
    | nil => rfl
    | cons h rest => simp only [fillTopForests, Forests.map, fillTop_erase, fillTopForests_erase]
end

theorem parents_erase (d : Nat) (e : NumericalExpr) : (parents d e).map ParentLabel.coordinates = e := by
  rw [parents, fillTop_erase, Parents.annotate_erase]

mutual
  theorem mark_erase (branch root : Nat) (history : List Nat) (e : ParentExpr) :
      (mark branch root history e).map Prod.fst = e.map ParentLabel.coordinates := by
    cases e with
    | nil => rfl
    | cons a hs t =>
      unfold mark
      simp only [Expr.map, mark_erase]
      by_cases before : history.length < root
      · cases t with
        | nil => simp [before, markForests_erase]
        | cons b ks u => simp [before, Forests.map_map]
      · simp [before, markForests_erase]
  theorem markForests_erase (branch root : Nat) (history : List Nat) (hs : Forests ParentLabel) :
      (markForests branch root history hs).map Prod.fst = hs.map ParentLabel.coordinates := by
    cases hs with
    | nil => rfl
    | cons h rest => simp only [markForests, Forests.map, mark_erase, markForests_erase]
end

mutual
  theorem ascendReplace_nohole_zero (e : MarkedExpr) (tail : NumericalExpr) (delta : List Nat) :
      ascendReplace e tail none delta 0 = e.map Prod.fst := by
    cases e with
    | nil => rfl
    | cons a hs rest =>
      unfold ascendReplace
      simp only [Option.none_beq_some, Bool.and_false, Bool.false_eq_true, if_false, Option.map_none,
        ite_self, shift_zero, Expr.map, ascendReplace_nohole_zero, ascendForests_nohole_zero]
  theorem ascendForests_nohole_zero (hs : Forests (List Nat × Nat)) (tail : NumericalExpr) (delta : List Nat) :
      ascendForests hs tail none delta 0 = hs.map Prod.fst := by
    cases hs with
    | nil => rfl
    | cons h rest =>
      unfold ascendForests
      simp only [ite_self, Forests.map, ascendReplace_nohole_zero, ascendForests_nohole_zero]
end

def pruneAt : Nat → NumericalExpr → NumericalExpr
  | 0, e => dropLast e
  | depth + 1, e => modifyLast (fun c => (c.1, modifyLastForest (pruneAt depth) c.2)) e

theorem pruneAt_labels_subset (depth : Nat) (e : NumericalExpr) :
    ∀ a ∈ labels (pruneAt depth e), a ∈ labels e := by
  cases depth with
  | zero => exact labels_dropLast_subset e
  | succ depth =>
    rw [pruneAt, labels_modifyLast_forests (fun _ hs => modifyLastForest (pruneAt depth) hs)]
    exact fun _ member => member

theorem pruneAt_finiteLegal (depth : Nat) {d : Nat} {context : ParentContext} {e : NumericalExpr}
    (legal : FiniteLegal d context e) : FiniteLegal d context (pruneAt depth e) := by
  induction depth generalizing context e with
  | zero => exact legal.dropLast
  | succ depth ih =>
    simp only [pruneAt]
    apply legal.modifyLast
    intro ctx a hs _ finite
    refine ⟨finite.1, finite.2.1, ?_, ?_, trivial⟩
    · intro nonempty
      apply finite.2.2.1
      intro empty
      simp only [empty, modifyLastForest] at nonempty
      exact nonempty rfl
    · exact finite.2.2.2.1.modifyLast (pruneAt depth) (pruneAt_labels_subset depth)
        (fun _ _ hLegal => ih hLegal)

mutual
  theorem ascendReplace_empty_zero (e : MarkedExpr) (delta : List Nat) (depth : Nat) :
      ascendReplace e .nil (some depth) delta 0 = pruneAt depth (e.map Prod.fst) := by
    cases e with
    | nil => cases depth <;> simp [ascendReplace, pruneAt, Expr.map, dropLast, modifyLast]
    | cons a hs rest =>
      cases rest with
      | nil =>
        cases depth with
        | zero => simp [ascendReplace, pruneAt, Expr.map, dropLast]
        | succ depth =>
          unfold ascendReplace
          simp [shift_zero, Expr.map, pruneAt, modifyLast, ascendForests_empty_zero, ascendReplace]
      | cons b ks t =>
        unfold ascendReplace
        simp only [Bool.false_and, Bool.false_eq_true, if_false, shift_zero,
          ascendForests_nohole_zero, ascendReplace_empty_zero]
        cases depth <;> simp only [Expr.map, pruneAt, dropLast, modifyLast]
  theorem ascendForests_empty_zero (hs : Forests (List Nat × Nat)) (delta : List Nat) (depth : Nat) :
      ascendForests hs .nil (some depth) delta 0 = modifyLastForest (pruneAt depth) (hs.map Prod.fst) := by
    cases hs with
    | nil => simp [ascendForests, Forests.map, modifyLastForest]
    | cons h rest =>
      cases rest with
      | nil =>
        unfold ascendForests
        simp [Forests.map, modifyLastForest, ascendReplace_empty_zero, ascendForests]
      | cons k ks =>
        unfold ascendForests
        simp only [Bool.false_eq_true, if_false, ascendReplace_nohole_zero, ascendForests_empty_zero,
          Forests.map, modifyLastForest]
end

theorem expand_zero_index_finiteLegal (d : Nat) {context : ParentContext} {e f : NumericalExpr}
    (legal : FiniteLegal d context e) (step : expand? d e 0 = some f) : FiniteLegal d context f := by
  simp only [expand?] at step
  split at step
  · simp only [Option.pure_def, Option.some.injEq] at step
    subst f
    trivial
  next last atLast =>
    split at step
    · simp only [Option.pure_def, Option.some.injEq] at step
      subst f
      exact legal.dropLast
    next nonzero =>
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at step
      obtain ⟨stop, selected, stopColumn, atStop, step⟩ := step
      split at step
      · simp only [Option.pure_def, Option.some.injEq] at step
        subst f
        exact special_spine_finiteLegal 0 _ legal selected atStop (by assumption)
      next ordinary =>
        simp only [Option.bind_eq_some_iff] at step
        obtain ⟨stopP, _, stopLabel, _, rootPair, _, layerPair, _, rootCol, _,
          rootPart, _, tailPart, _, tailColumn, _, result⟩ := step
        simp only [copies, Option.pure_def, ascendReplace_empty_zero, mark_erase, parents_erase,
          Option.some.injEq] at result
        subst f
        exact pruneAt_finiteLegal _ legal

end Source
end BTnSSBMS
