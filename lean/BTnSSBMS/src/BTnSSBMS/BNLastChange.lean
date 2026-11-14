import BTnSSBMS.BNDeletion

/-! BN under a nonincreasing change to the last attachment list.
Actual numerical labels and scoped zero-parents are unchanged. The
earlier sibling block closes before the later one and stays identical. -/
namespace BTnSSBMS.Source

theorem modifyLast_forests_le
    (f : List Nat → Forests (List Nat) → Forests (List Nat)) (e : NumericalExpr)
    (lower : ∀ a hs, last? e = some (a, hs) → (f a hs).compare (listCompare Ord.compare) hs ≠ .gt) :
    ExprLE (modifyLast (fun x => (x.1, f x.1 x.2)) e) e := by
  cases e with
  | nil => rw [modifyLast]; exact .refl _
  | cons a hs rest =>
    cases rest with
    | nil =>
      have atLast := lower a hs (by rw [last?])
      rw [modifyLast]
      simp only [ExprLE, Expr.compare, columnCompare_self]
      cases order : (f a hs).compare (listCompare Ord.compare) hs <;> simp_all
    | cons b ks tail =>
      rw [modifyLast]
      exact (modifyLast_forests_le f (.cons b ks tail)
        (fun c js selected => lower c js (by simpa only [last?] using selected))).cons a hs

theorem drop_modifyLast_forests
    (f : List Nat → Forests (List Nat) → Forests (List Nat)) (index : Nat) (e : NumericalExpr) :
    drop index (modifyLast (fun x => (x.1, f x.1 x.2)) e) =
      modifyLast (fun x => (x.1, f x.1 x.2)) (drop index e) := by
  induction index generalizing e with
  | zero => rfl
  | succ index ih =>
    cases e with
    | nil => simp only [modifyLast, drop]
    | cons a hs rest =>
      cases rest with
      | nil => cases index <;> simp only [modifyLast, drop]
      | cons b ks tail => simpa only [modifyLast, drop] using ih (.cons b ks tail)

theorem dropContext_modifyLast_forests
    (f : List Nat → Forests (List Nat) → Forests (List Nat)) (d : Nat)
    (context : ParentContext) (index : Nat) (e : NumericalExpr) :
    dropContext d context index (modifyLast (fun x => (x.1, f x.1 x.2)) e) =
      dropContext d context index e := by
  induction index generalizing context e with
  | zero => rfl
  | succ index ih =>
    cases e with
    | nil => simp only [modifyLast, dropContext]
    | cons a hs rest =>
      cases rest with
      | nil => simp only [modifyLast, dropContext]
      | cons b ks tail => simpa only [modifyLast, dropContext] using ih _ (.cons b ks tail)

theorem modifyLast_forests_cons_inv
    (f : List Nat → Forests (List Nat) → Forests (List Nat))
    {e : NumericalExpr} {a : List Nat} {hs : Forests (List Nat)} {tail : NumericalExpr}
    (shape : modifyLast (fun x => (x.1, f x.1 x.2)) e = .cons a hs tail) :
    ∃ ks rest, e = .cons a ks rest := by
  cases e with
  | nil => simp [modifyLast] at shape
  | cons b ks rest =>
    cases rest with
    | nil =>
      simp only [modifyLast, Expr.cons.injEq] at shape
      exact ⟨ks, .nil, by rw [shape.1]⟩
    | cons c js after =>
      simp only [modifyLast, Expr.cons.injEq] at shape
      exact ⟨ks, .cons c js after, by rw [shape.1]⟩

theorem last_of_drop (index : Nat) (e : Expr α) {a : α} {hs : Forests α}
    (found : last? (drop index e) = some (a, hs)) : last? e = some (a, hs) := by
  induction index generalizing e with
  | zero => exact found
  | succ index ih =>
    cases e with
    | nil => simp [drop, last?] at found
    | cons b ks rest =>
      cases rest with
      | nil => cases index <;> simp [drop, last?] at found
      | cons c js tail => simpa only [last?] using ih (.cons c js tail) found

theorem takeAbove_modifyLast_of_boundary
    (f : List Nat → Forests (List Nat) → Forests (List Nat))
    {e : NumericalExpr} {a : List Nat} {hs : Forests (List Nat)} {tail : NumericalExpr}
    (index floor : Nat) (shape : drop index e = .cons a hs tail)
    (low : a[0]?.getD 0 ≤ floor) :
    takeAbove floor (modifyLast (fun x => (x.1, f x.1 x.2)) e) = takeAbove floor e := by
  induction index generalizing e with
  | zero =>
    change e = .cons a hs tail at shape
    subst e
    cases tail <;> simp only [modifyLast, takeAbove, show ¬ floor < a[0]?.getD 0 by omega, if_false]
  | succ index ih =>
    cases e with
    | nil => simp [drop] at shape
    | cons b ks rest =>
      cases rest with
      | nil => cases index <;> simp [drop] at shape
      | cons c js more =>
        have same := ih (e := .cons c js more) shape
        simp only [modifyLast, takeAbove]
        split
        · exact congrArg (Expr.cons b ks) same
        · rfl

theorem rootBlock_modifyLast_of_sibling
    (f : List Nat → Forests (List Nat) → Forests (List Nat))
    {a b : List Nat} {hs ks : Forests (List Nat)} {rest tail : NumericalExpr} (index : Nat)
    (shape : drop index rest = .cons b ks tail) (same : b[0]?.getD 0 = a[0]?.getD 0) :
    rootBlock (modifyLast (fun x => (x.1, f x.1 x.2)) (.cons a hs rest)) = rootBlock (.cons a hs rest) := by
  cases rest with
  | nil => cases index <;> simp [drop] at shape
  | cons c js more =>
    rw [modifyLast, rootBlock, rootBlock,
      takeAbove_modifyLast_of_boundary f index (a[0]?.getD 0) shape (Nat.le_of_eq same)]

theorem BN.modifyLastForests {d : Nat} {context : ParentContext} {e : NumericalExpr}
    (ordered : BN d context e) (positive : 0 < d) (legal : FiniteLegal d context e)
    (f : List Nat → Forests (List Nat) → Forests (List Nat))
    (preserves : ∀ ctx a hs, last? e = some (a, hs) → FiniteLegal d ctx (.cons a hs .nil) →
      BNForests d (ctx ++ [Parents.label d ctx a]) hs →
      BNForests d (ctx ++ [Parents.label d ctx a]) (f a hs))
    (lower : ∀ a hs, last? e = some (a, hs) → (f a hs).compare (listCompare Ord.compare) hs ≠ .gt) :
    BN d context (modifyLast (fun x => (x.1, f x.1 x.2)) e) := by
  cases e with
  | nil => rw [modifyLast]; trivial
  | cons a hs rest =>
    cases rest with
    | nil =>
      rw [modifyLast]
      exact BN.singleton a (preserves context a hs (by rw [last?]) legal ordered.2.1)
    | cons c js more =>
      rw [modifyLast]
      refine ⟨?_, ordered.2.1, ordered.2.2.modifyLastForests positive legal.2.2.2.2 f
        (fun ctx b ks found finite good => preserves ctx b ks (by simpa only [last?] using found) finite good)
        (fun b ks found => lower b ks (by simpa only [last?] using found))⟩
      intro index b ks tail shape same
      rw [drop_modifyLast_forests] at shape
      obtain ⟨oldForests, after, original⟩ := modifyLast_forests_cons_inv f shape
      rw [dropContext_modifyLast_forests] at same
      have prior := ordered.1 index b oldForests after original same
      have laterLegal := legal.2.2.2.2.drop index
      rw [original] at laterLegal
      have sharedValue := same_zero_parent_value positive
        ((List.prefix_append context _).trans (dropContext_prefix d _ index (.cons c js more)))
        a b legal.2.1 laterLegal.2.1 same
      have unchanged := rootBlock_modifyLast_of_sibling f (a := a) (hs := hs) index original sharedValue
      simp only [modifyLast] at unchanged
      rw [unchanged]
      have decrease := rootBlock_mono (modifyLast_forests_le f (Source.drop index (.cons c js more)) (by
        intro v forests found
        exact lower v forests (by simpa only [last?] using last_of_drop index (.cons c js more) found)))
      rw [shape, original] at decrease
      exact decrease.trans prior

end BTnSSBMS.Source
