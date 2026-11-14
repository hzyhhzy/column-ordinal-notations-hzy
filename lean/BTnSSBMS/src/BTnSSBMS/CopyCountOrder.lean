import BTnSSBMS.SourceBlockOrder

/-! Increasing the number of ordinary copies is monotone in the frozen
recursive comparison, at a fixed starting phase. This is a syntactic
order statement, not well-foundedness. It covers arbitrary marked material
and does not impose a nesting-depth or copy-count bound. -/
namespace BTnSSBMS.Source

mutual
  theorem splice_mono (depth : Nat) (e : NumericalExpr) {left right : NumericalExpr}
      (lower : ExprLE left right) :
      ExprLE (splice depth left e) (splice depth right e) := by
    cases e with
    | nil => simp only [splice]; exact .refl _
    | cons a hs rest =>
      cases rest with
      | nil =>
        cases depth with
        | zero => simpa only [splice] using lower
        | succ depth =>
          have forests := spliceForests_mono depth hs lower
          simp only [splice, ExprLE, Expr.compare, columnCompare_self]
          cases c : (spliceForests depth left hs).compare (listCompare Ord.compare)
              (spliceForests depth right hs) <;> simp_all only [ne_eq, reduceCtorEq, not_false_eq_true, not_true_eq_false]
      | cons b ks tail =>
        simpa only [splice] using (splice_mono depth (.cons b ks tail) lower).cons a hs

  theorem spliceForests_mono (depth : Nat) (hs : Forests (List Nat)) {left right : NumericalExpr}
      (lower : ExprLE left right) :
      (spliceForests depth left hs).compare (listCompare Ord.compare) (spliceForests depth right hs) ≠ .gt := by
    cases hs with
    | nil => simp only [spliceForests, Forests.compare, ne_eq, reduceCtorEq, not_false_eq_true]
    | cons h rest =>
      cases rest with
      | nil =>
        have terms := splice_mono depth h lower
        simp only [ExprLE] at terms
        simp only [spliceForests, Forests.compare]
        cases c : (splice depth left h).compare (listCompare Ord.compare) (splice depth right h) <;>
          simp_all only [ne_eq, reduceCtorEq, not_false_eq_true, not_true_eq_false]
      | cons k ks =>
        simpa only [spliceForests, Forests.compare, expr_compare_self] using
          spliceForests_mono depth (.cons k ks) lower
end

theorem copies_count_mono (part : MarkedExpr) (depth : Nat) (delta : List Nat)
    (small large phase : Nat) (counts : small ≤ large) :
    ExprLE (copies part depth delta none small phase) (copies part depth delta none large phase) := by
  induction small generalizing large phase with
  | zero => rw [copies]; exact .nil _
  | succ small ih =>
    cases large with
    | zero => omega
    | succ large =>
      rw [copies, copies, ascendReplace_splice, ascendReplace_splice]
      exact splice_mono depth _ (ih large (phase + 1) (by omega))

theorem copies_rootBlock_count_mono (part : MarkedExpr) (depth : Nat) (delta : List Nat)
    (small large phase : Nat) (counts : small ≤ large) :
    ExprLE (rootBlock (copies part depth delta none small phase))
      (rootBlock (copies part depth delta none large phase)) :=
  rootBlock_mono (copies_count_mono part depth delta small large phase counts)

end BTnSSBMS.Source
