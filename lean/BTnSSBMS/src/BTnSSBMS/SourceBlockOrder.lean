import BTnSSBMS.SourceHWClosure
import BTnSSBMS.SourceBlocks

/-! Order and terminal deletion for complete source zero-blocks.
These are actual syntactic blocks, retaining all attached forests. -/
namespace BTnSSBMS.Source

theorem ExprLE.nil (e : NumericalExpr) : ExprLE .nil e := by
  cases e <;> simp only [ExprLE, Expr.compare, ne_eq, reduceCtorEq, not_false_eq_true]

theorem ExprLE.cons (a : List Nat) (hs : Forests (List Nat)) {e f : NumericalExpr}
    (lower : ExprLE e f) : ExprLE (.cons a hs e) (.cons a hs f) := by
  simpa only [ExprLE, Expr.compare, columnCompare_self, forests_compare_self] using lower

theorem column_not_gt_zero {a b : List Nat}
    (lower : listCompare Ord.compare a b ≠ .gt) : a[0]?.getD 0 ≤ b[0]?.getD 0 := by
  cases a with
  | nil => simp
  | cons x xs =>
    cases b with
    | nil => simp [listCompare] at lower
    | cons y ys =>
      cases first : compare x y with
      | gt => simp [listCompare, first] at lower
      | lt => simpa only [List.getElem?_cons_zero, Option.getD_some] using Nat.le_of_lt (Nat.compare_eq_lt.mp first)
      | eq => simpa only [List.getElem?_cons_zero, Option.getD_some] using Nat.le_of_eq (Nat.compare_eq_eq.mp first)

theorem takeAbove_le (floor : Nat) (e : NumericalExpr) : ExprLE (takeAbove floor e) e := by
  cases e with
  | nil => exact .refl _
  | cons a hs tail =>
    rw [takeAbove]
    split
    · exact (takeAbove_le floor tail).cons a hs
    · exact .nil _

theorem takeAbove_mono (floor : Nat) {e f : NumericalExpr} (lower : ExprLE e f) :
    ExprLE (takeAbove floor e) (takeAbove floor f) := by
  cases e with
  | nil => exact .nil _
  | cons a hs tail =>
    cases f with
    | nil => simp [ExprLE, Expr.compare] at lower
    | cons b ks rest =>
      have heads : listCompare Ord.compare a b ≠ .gt := by
        intro bad
        simp [ExprLE, Expr.compare, bad] at lower
      have first := column_not_gt_zero heads
      by_cases active : floor < a[0]?.getD 0
      · have active' : floor < b[0]?.getD 0 := by omega
        rw [takeAbove, if_pos active, takeAbove, if_pos active']
        cases numerical : listCompare Ord.compare a b with
        | gt => exact False.elim (heads numerical)
        | lt => simp only [ExprLE, Expr.compare, numerical, ne_eq, reduceCtorEq, not_false_eq_true]
        | eq =>
          cases forests : hs.compare (listCompare Ord.compare) ks with
          | gt => simp [ExprLE, Expr.compare, numerical, forests] at lower
          | lt => simp only [ExprLE, Expr.compare, numerical, forests, ne_eq, reduceCtorEq, not_false_eq_true]
          | eq =>
            have tails : ExprLE tail rest := by simpa only [ExprLE, Expr.compare, numerical, forests] using lower
            simpa only [ExprLE, Expr.compare, numerical, forests] using takeAbove_mono floor tails
      · rw [takeAbove, if_neg active]
        exact .nil _

theorem rootBlock_le (e : NumericalExpr) : ExprLE (rootBlock e) e := by
  cases e with
  | nil => exact .refl _
  | cons a hs tail => exact (takeAbove_le (a[0]?.getD 0) tail).cons a hs

theorem rootBlock_mono {e f : NumericalExpr} (lower : ExprLE e f) :
    ExprLE (rootBlock e) (rootBlock f) := by
  cases e with
  | nil => exact .nil _
  | cons a hs tail =>
    cases f with
    | nil => simp [ExprLE, Expr.compare] at lower
    | cons b ks rest =>
      cases numerical : listCompare Ord.compare a b with
      | gt => simp [ExprLE, Expr.compare, numerical] at lower
      | lt => simp only [rootBlock, ExprLE, Expr.compare, numerical, ne_eq, reduceCtorEq, not_false_eq_true]
      | eq =>
        have same : a = b := listCompare_eq_imp _ (fun _ _ h => Nat.compare_eq_eq.mp h) a b numerical
        subst b
        cases forests : hs.compare (listCompare Ord.compare) ks with
        | gt => simp [ExprLE, Expr.compare, numerical, forests] at lower
        | lt => simp only [rootBlock, ExprLE, Expr.compare, numerical, forests, ne_eq, reduceCtorEq, not_false_eq_true]
        | eq =>
          have tails : ExprLE tail rest := by simpa only [ExprLE, Expr.compare, numerical, forests] using lower
          simpa only [rootBlock, ExprLE, Expr.compare, numerical, forests] using takeAbove_mono (a[0]?.getD 0) tails

theorem rootBlock_dropLast_le (e : NumericalExpr) :
    ExprLE (rootBlock (dropLast e)) (rootBlock e) := rootBlock_mono (dropLast_le e)

theorem drop_dropLast (index : Nat) (e : Expr α) :
    drop index (dropLast e) = dropLast (drop index e) := by
  induction index generalizing e with
  | zero => rfl
  | succ index ih =>
    cases e with
    | nil => simp only [dropLast, drop]
    | cons a hs tail =>
      cases tail with
      | nil => cases index <;> simp only [dropLast, drop]
      | cons b ks rest => simpa only [dropLast, drop] using ih (.cons b ks rest)

theorem dropLast_cons_inv {e : Expr α} {a : α} {hs : Forests α} {tail : Expr α}
    (shape : dropLast e = .cons a hs tail) :
    ∃ rest, e = .cons a hs rest ∧ dropLast rest = tail ∧ rest ≠ .nil := by
  cases e with
  | nil => simp [dropLast] at shape
  | cons b ks rest =>
    cases rest with
    | nil => simp [dropLast] at shape
    | cons c js after =>
      simp only [dropLast, Expr.cons.injEq] at shape
      obtain ⟨rfl, rfl, same⟩ := shape
      exact ⟨.cons c js after, rfl, same, by intro impossible; cases impossible⟩

theorem drop_shape_inside {index : Nat} {e : Expr α} {a : α} {hs : Forests α} {tail : Expr α}
    (shape : drop index e = .cons a hs tail) : index < length e := by
  induction index generalizing e with
  | zero => cases e <;> simp_all [drop, length] <;> omega
  | succ index ih =>
    cases e with
    | nil => simp [drop] at shape
    | cons b ks rest =>
      have inside := ih (e := rest) shape
      simp only [length]
      omega

theorem takeAbove_dropLast_of_boundary {e : NumericalExpr} {a : List Nat}
    {hs : Forests (List Nat)} {tail : NumericalExpr} (index floor : Nat)
    (shape : drop index e = .cons a hs tail) (after : tail ≠ .nil)
    (low : a[0]?.getD 0 ≤ floor) : takeAbove floor (dropLast e) = takeAbove floor e := by
  induction index generalizing e with
  | zero =>
    change e = .cons a hs tail at shape
    subst e
    cases tail with
    | nil => exact False.elim (after rfl)
    | cons b ks rest => simp only [dropLast, takeAbove, show ¬ floor < a[0]?.getD 0 by omega, if_false]
  | succ index ih =>
    cases e with
    | nil => simp [drop] at shape
    | cons b ks rest =>
      cases rest with
      | nil => cases index <;> simp [drop] at shape
      | cons c js more =>
        have same := ih (e := .cons c js more) shape
        simp only [dropLast, takeAbove]
        split
        · exact congrArg (Expr.cons b ks) same
        · rfl

theorem rootBlock_dropLast_of_sibling {a b : List Nat} {hs ks : Forests (List Nat)}
    {rest tail : NumericalExpr} (index : Nat)
    (shape : drop index rest = .cons b ks tail) (after : tail ≠ .nil)
    (same : b[0]?.getD 0 = a[0]?.getD 0) :
    rootBlock (dropLast (.cons a hs rest)) = rootBlock (.cons a hs rest) := by
  cases rest with
  | nil => cases index <;> simp [drop] at shape
  | cons c js more =>
    rw [dropLast, rootBlock, rootBlock,
      takeAbove_dropLast_of_boundary index (a[0]?.getD 0) shape after (Nat.le_of_eq same)]

end BTnSSBMS.Source
