import BTnSSBMS.CopySeam

/-!
The copy transport uses the numerical parent annotation. The actual FS
also appends a highest key-parent coordinate. This module proves that
the appended coordinate cannot affect activation at caps at most d.
-/
namespace BTnSSBMS.Keys

private theorem takeWhile_congr_on (xs : List α) (p q : α → Bool)
    (same : ∀ x ∈ xs, p x = q x) : xs.takeWhile p = xs.takeWhile q := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.takeWhile_cons, List.takeWhile_cons, same x (by simp)]
    rw [ih (fun a member => same a (by simp; exact Or.inr member))]

theorem threshold_append_parents (cap root : Nat) (history : List Nat) (a : ParentLabel)
    (extra : List (Option Nat)) (bounded : cap ≤ a.parents.length) :
    threshold cap root history {a with parents := a.parents ++ extra} = threshold cap root history a := by
  unfold threshold
  apply congrArg List.length
  apply takeWhile_congr_on
  intro j member
  have inside : j < cap := List.mem_range.mp member
  rw [List.getElem?_append_left (by omega : j < a.parents.length)]

end BTnSSBMS.Keys

namespace BTnSSBMS.Source

mutual
  theorem fillTop_map_coordinates (d : Nat) (context : KeyContext) (owners : List Nat)
      (f : List Nat → α) (e : ParentExpr) :
      (fillTop d context owners e).map (fun a => f a.coordinates) = e.map (fun a => f a.coordinates) := by
    cases e with
    | nil => rfl
    | cons a hs t => simp only [fillTop, Expr.map, fillTopForests_map_coordinates, fillTop_map_coordinates]
  theorem fillTopForests_map_coordinates (d : Nat) (context : KeyContext) (owners : List Nat)
      (f : List Nat → α) (hs : Forests ParentLabel) :
      (fillTopForests d context owners hs).map (fun a => f a.coordinates) = hs.map (fun a => f a.coordinates) := by
    cases hs with
    | nil => rfl
    | cons h rest => simp only [fillTopForests, Forests.map, fillTop_map_coordinates, fillTopForests_map_coordinates]
end

mutual
  theorem mark_fillTop_annotate (d cap root : Nat) (history : List Nat) (bounded : cap ≤ d)
      (keyContext : KeyContext) (owners : List Nat) (context : ParentContext) (e : NumericalExpr) :
      mark cap root history (fillTop d keyContext owners (Parents.annotate d context e)) =
        mark cap root history (Parents.annotate d context e) := by
    cases e with
    | nil => rfl
    | cons a hs t =>
      simp only [Parents.annotate, fillTop]
      unfold mark
      simp only [Keys.threshold_append_parents cap root history (Parents.label d context a) _
        (by rw [Parents.label_width]; exact bounded)]
      simp only [mark_fillTop_annotate d cap root _ bounded,
        markForests_fillTop_annotate d cap root _ bounded]
      by_cases before : history.length < root
      · cases t with
        | nil => simp only [Parents.annotate, fillTop, before, if_true, decide_true, Bool.true_and,
            Bool.false_eq_true, if_false, mark]
        | cons b ks u =>
          simp only [Parents.annotate, fillTop, before, if_true, decide_true, Bool.true_and]
          congr 1
          exact fillTopForests_map_coordinates d _ _ (fun a => (a, 0)) _
      · simp only [before, decide_false, Bool.false_and, Bool.false_eq_true, if_false]
  theorem markForests_fillTop_annotate (d cap root : Nat) (history : List Nat) (bounded : cap ≤ d)
      (keyContext : KeyContext) (owners : List Nat) (context : ParentContext) (hs : Forests (List Nat)) :
      markForests cap root history (fillTopForests d keyContext owners (Parents.annotateForests d context hs)) =
        markForests cap root history (Parents.annotateForests d context hs) := by
    cases hs with
    | nil => rfl
    | cons h rest =>
      simp only [Parents.annotateForests, fillTopForests, markForests,
        mark_fillTop_annotate d cap root history bounded, markForests_fillTop_annotate d cap root history bounded]
end

theorem mark_parents_eq_numeric (d cap root : Nat) (history : List Nat) (bounded : cap ≤ d)
    (e : NumericalExpr) :
    mark cap root history (parents d e) = mark cap root history (Parents.annotate d [] e) :=
  mark_fillTop_annotate d cap root history bounded [] [] [] e

end BTnSSBMS.Source
