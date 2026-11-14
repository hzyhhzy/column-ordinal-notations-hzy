import BTnSSBMS.SBHistory

/-! The actual outer zero-column deletion branch preserves every source
SB level. Historical owner blocks are explicitly updated; no claim is
made here for deleting a positive terminal inside a copied template. -/
namespace BTnSSBMS.Source

theorem takeAbove_dropLast_zero (floor : Nat) (e : NumericalExpr)
    {a : List Nat} {hs : Forests (List Nat)}
    (last : last? e = some (a, hs)) (zero : a[0]?.getD 0 = 0) :
    takeAbove floor (dropLast e) = takeAbove floor e := by
  cases e with
  | nil => simp [last?] at last
  | cons b ks rest =>
    cases rest with
    | nil =>
      have same : b = a ∧ ks = hs := by simpa only [last?, Option.some.injEq, Prod.mk.injEq] using last
      obtain ⟨rfl, rfl⟩ := same
      simp only [dropLast, takeAbove, zero, Nat.not_lt_zero, if_false]
    | cons c js tail =>
      have later := takeAbove_dropLast_zero floor (.cons c js tail) (by simpa only [last?] using last) zero
      simp only [dropLast, takeAbove]
      split
      · exact congrArg (Expr.cons b ks) later
      · rfl

theorem rootBlock_dropLast_zero (b c : List Nat) (ks js : Forests (List Nat)) (tail : NumericalExpr)
    {a : List Nat} {hs : Forests (List Nat)}
    (last : last? (.cons c js tail) = some (a, hs)) (zero : a[0]?.getD 0 = 0) :
    rootBlock (dropLast (.cons b ks (.cons c js tail))) = rootBlock (.cons b ks (.cons c js tail)) := by
  simp only [dropLast, rootBlock]
  exact congrArg (Expr.cons b ks) (takeAbove_dropLast_zero (b[0]?.getD 0) (.cons c js tail) last zero)

theorem SB.dropLast_zero {d cut : Nat} {context : ParentContext} {history : List NumericalExpr}
    {e : NumericalExpr} (ordered : SB d cut context history e)
    (length : history.length = context.length) {a : List Nat} {hs : Forests (List Nat)}
    (last : last? e = some (a, hs)) (zero : a[0]?.getD 0 = 0) :
    SB d cut context history (dropLast e) := by
  cases e with
  | nil => rw [dropLast]; trivial
  | cons b ks rest =>
    cases rest with
    | nil => rw [dropLast]; trivial
    | cons c js tail =>
      have atTail : last? (.cons c js tail) = some (a, hs) := by simpa only [last?] using last
      have unchanged := rootBlock_dropLast_zero b c ks js tail atTail zero
      have oldLength : (history ++ [Expr.cons b ks (.cons c js tail)]).length =
          (context ++ [Parents.label d context b]).length := by
        simp only [List.length_append, List.length_cons, List.length_nil, length]
      have newLength : (history ++ [dropLast (Expr.cons b ks (.cons c js tail))]).length =
          (context ++ [Parents.label d context b]).length := by
        simp only [List.length_append, List.length_cons, List.length_nil, length]
      have agreement : ∀ root, root < (context ++ [Parents.label d context b]).length →
          rootBlock ((history ++ [Expr.cons b ks (.cons c js tail)])[root]?.getD .nil) =
            rootBlock ((history ++ [dropLast (Expr.cons b ks (.cons c js tail))])[root]?.getD .nil) := by
        simpa only [List.length_append, List.length_cons, List.length_nil] using
          append_block_history_eq length length (fun _ _ => rfl) unchanged.symm
      rw [dropLast] at unchanged newLength agreement
      rw [dropLast]
      refine ⟨?_, ?_, ?_⟩
      · intro positive room root inside path shared
        have prior := ordered.1 positive room root inside path shared
        rw [unchanged]
        exact prior
      · exact SBForests.history_congr ks oldLength newLength agreement ordered.2.1
      · exact SB.history_congr (dropLast (.cons c js tail)) oldLength newLength agreement
          (ordered.2.2.dropLast_zero oldLength atTail zero)

theorem zeroColumn_first_zero {a : List Nat} {hs : Forests (List Nat)}
    (zero : zeroColumn (a, hs) = true) : a[0]?.getD 0 = 0 := by
  cases a with
  | nil => rfl
  | cons x rest =>
    simp only [zeroColumn, List.all_cons, Bool.and_eq_true, beq_iff_eq] at zero
    exact zero.1.1

theorem expand_outer_zero_SB {d cut : Nat} {e f : NumericalExpr}
    (ordered : SB d cut [] [] e) {a : List Nat} {hs : Forests (List Nat)}
    (last : last? e = some (a, hs)) (zero : zeroColumn (a, hs) = true)
    (count : Nat) (edge : expand? d e count = some f) : SB d cut [] [] f := by
  have same : f = dropLast e := by
    simpa only [expand?, last, zero, if_true, Option.pure_def, Option.some.injEq] using edge.symm
  rw [same]
  exact ordered.dropLast_zero rfl last (zeroColumn_first_zero zero)

end BTnSSBMS.Source
