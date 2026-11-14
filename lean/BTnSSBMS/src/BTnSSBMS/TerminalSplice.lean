import BTnSSBMS.BNRootCopy
import BTnSSBMS.BNLastChange

/-! Exact outer-terminal replacement geometry. These are facts about
the existing splice operation, not additional expansion rules. -/
namespace BTnSSBMS.Source

theorem splice_zero_le (e replacement : NumericalExpr) {terminal : List Nat} {attached : Forests (List Nat)}
    (last : last? e = some (terminal, attached))
    (lower : ExprLE replacement (.cons terminal attached .nil)) :
    ExprLE (splice 0 replacement e) e := by
  cases e with
  | nil => simp [last?] at last
  | cons a hs rest =>
    cases rest with
    | nil =>
      have same : (a, hs) = (terminal, attached) := by simpa only [last?, Option.some.injEq] using last
      cases same
      simpa only [splice] using lower
    | cons b ks tail =>
      simpa only [splice] using
        (splice_zero_le (.cons b ks tail) replacement (by simpa only [last?] using last) lower).cons a hs

/-- A later output head either survives from before the old terminal,
or lies inside the replacement at the old terminal's exact entry. -/
theorem splice_zero_drop_cases (d : Nat) (context : ParentContext) (e replacement : NumericalExpr)
    (index : Nat) {a : List Nat} {hs : Forests (List Nat)} {tail : NumericalExpr}
    (found : drop index (splice 0 replacement e) = .cons a hs tail) :
    (∃ rest, drop index e = .cons a hs rest ∧ rest ≠ .nil ∧
      dropContext d context index (splice 0 replacement e) = dropContext d context index e ∧
      .cons a hs tail = splice 0 replacement (.cons a hs rest)) ∨
    (∃ offset, drop offset replacement = .cons a hs tail ∧
      dropContext d context index (splice 0 replacement e) =
        dropContext d (outerContext d context (dropLast e)) offset replacement) := by
  induction index generalizing context e with
  | zero =>
    cases e with
    | nil => simp [splice, drop] at found
    | cons b ks rest =>
      cases rest with
      | nil =>
        refine Or.inr ⟨0, ?_, ?_⟩
        · simpa only [splice] using found
        · simp only [splice, dropLast, outerContext]
      | cons c js more =>
        have same : b = a ∧ ks = hs ∧ splice 0 replacement (.cons c js more) = tail := by
          simpa only [splice, drop, Expr.cons.injEq] using found
        obtain ⟨rfl, rfl, rfl⟩ := same
        refine Or.inl ⟨.cons c js more, rfl, ?_, rfl, ?_⟩
        · intro h
          cases h
        · rw [splice]
  | succ index ih =>
    cases e with
    | nil => simp [splice, drop] at found
    | cons b ks rest =>
      cases rest with
      | nil =>
        refine Or.inr ⟨index + 1, ?_, ?_⟩
        · simpa only [splice] using found
        · simp only [splice, dropLast, outerContext]
      | cons c js more =>
        have next := ih (context ++ [Parents.label d context b]) (.cons c js more)
          (by simpa only [splice, drop] using found)
        rcases next with ⟨after, selected, nonempty, contexts, value⟩ | ⟨offset, selected, contexts⟩
        · refine Or.inl ⟨after, ?_, nonempty, ?_, value⟩
          · simpa only [drop] using selected
          · simpa only [splice, dropContext] using contexts
        · refine Or.inr ⟨offset, selected, ?_⟩
          simpa only [splice, dropContext, dropLast, outerContext] using contexts

theorem takeAbove_splice_zero_surviving {e : NumericalExpr} {a : List Nat}
    {hs : Forests (List Nat)} {tail : NumericalExpr} (replacement : NumericalExpr)
    (index floor : Nat) (found : drop index e = .cons a hs tail) (nonempty : tail ≠ .nil)
    (low : a[0]?.getD 0 ≤ floor) :
    takeAbove floor (splice 0 replacement e) = takeAbove floor e := by
  induction index generalizing e with
  | zero =>
    change e = .cons a hs tail at found
    subst e
    cases tail with
    | nil => exact False.elim (nonempty rfl)
    | cons b ks rest => simp only [splice, takeAbove, show ¬ floor < a[0]?.getD 0 by omega, if_false]
  | succ index ih =>
    cases e with
    | nil => simp [drop] at found
    | cons b ks rest =>
      cases rest with
      | nil => cases index <;> simp [drop] at found
      | cons c js more =>
        have same := ih (e := .cons c js more) found
        simp only [splice, takeAbove]
        split
        · exact congrArg (Expr.cons b ks) same
        · rfl

theorem takeAbove_splice_zero_last (e replacement : NumericalExpr) (floor : Nat)
    {a : List Nat} {hs : Forests (List Nat)} (last : last? e = some (a, hs))
    (low : a[0]?.getD 0 ≤ floor) (cut : takeAbove floor replacement = .nil) :
    takeAbove floor (splice 0 replacement e) = takeAbove floor e := by
  cases e with
  | nil => simp [last?] at last
  | cons b ks rest =>
    cases rest with
    | nil =>
      have same : (b, ks) = (a, hs) := by simpa only [last?, Option.some.injEq] using last
      cases same
      simp only [splice, cut, takeAbove, show ¬ floor < a[0]?.getD 0 by omega, if_false]
    | cons c js more =>
      have same := takeAbove_splice_zero_last (.cons c js more) replacement floor
        (by simpa only [last?] using last) low cut
      simp only [splice, takeAbove]
      split
      · exact congrArg (Expr.cons b ks) same
      · rfl

theorem drop_last_singleton (e : Expr α) {a : α} {hs : Forests α}
    (last : last? e = some (a, hs)) : drop (length e - 1) e = .cons a hs .nil := by
  cases e with
  | nil => simp [last?] at last
  | cons b ks rest =>
    cases rest with
    | nil =>
      have same : (b, ks) = (a, hs) := by simpa only [last?, Option.some.injEq] using last
      cases same
      rfl
    | cons c js more =>
      have size : length (.cons b ks (.cons c js more)) - 1 = (length (.cons c js more) - 1) + 1 := by
        simp only [length]
        omega
      rw [size, drop]
      exact drop_last_singleton (.cons c js more) (by simpa only [last?] using last)

theorem last_drop_of_cons (index : Nat) (e : Expr α) {a : α} {hs : Forests α} {tail : Expr α}
    (found : drop index e = .cons a hs tail) : last? (.cons a hs tail) = last? e := by
  induction index generalizing e with
  | zero => change e = .cons a hs tail at found; rw [found]
  | succ index ih =>
    cases e with
    | nil => simp [drop] at found
    | cons b ks rest =>
      cases rest with
      | nil => cases index <;> simp [drop] at found
      | cons c js more => simpa only [last?] using ih (.cons c js more) found

theorem dropContext_last (d : Nat) (context : ParentContext) (e : NumericalExpr) :
    dropContext d context (length e - 1) e = outerContext d context (dropLast e) := by
  cases e with
  | nil => simp [length, dropContext, dropLast, outerContext]
  | cons a hs rest =>
    cases rest with
    | nil => simp [length, dropContext, dropLast, outerContext]
    | cons b ks tail =>
      have size : length (.cons a hs (.cons b ks tail)) - 1 = (length (.cons b ks tail) - 1) + 1 := by
        simp only [length]
        omega
      rw [size, dropContext, dropLast, outerContext]
      exact dropContext_last d (context ++ [Parents.label d context a]) (.cons b ks tail)

end BTnSSBMS.Source
