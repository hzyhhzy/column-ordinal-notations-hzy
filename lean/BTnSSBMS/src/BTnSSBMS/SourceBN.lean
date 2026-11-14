import BTnSSBMS.SourceSiblingGeometry

/-!
BN for the original scoped source syntax. The head is compared against
each later column in the SAME forest whose computed zero-parent is the
same (including the parentless case). Both comparison terms are complete
zero-blocks. Recursion separately checks attachments and the outer tail.
No part of this condition is included in Source.Standard.
-/
namespace BTnSSBMS.Source

def HeadBN (d : Nat) (context : ParentContext) (a : List Nat)
    (hs : Forests (List Nat)) (rest : NumericalExpr) : Prop :=
  ∀ index b ks tail, drop index rest = .cons b ks tail →
    (Parents.label d (dropContext d (context ++ [Parents.label d context a]) index rest) b).parents[0]?.join =
      (Parents.label d context a).parents[0]?.join →
    ExprLE (rootBlock (.cons b ks tail)) (rootBlock (.cons a hs rest))

mutual
  def BN (d : Nat) (context : ParentContext) : NumericalExpr → Prop
    | .nil => True
    | .cons a hs rest => HeadBN d context a hs rest ∧
        BNForests d (context ++ [Parents.label d context a]) hs ∧
        BN d (context ++ [Parents.label d context a]) rest
  def BNForests (d : Nat) (context : ParentContext) : Forests (List Nat) → Prop
    | .nil => True
    | .cons h rest => BN d context h ∧ BNForests d context rest
end

theorem headBN_nil (d : Nat) (context : ParentContext) (a : List Nat) (hs : Forests (List Nat)) :
    HeadBN d context a hs .nil := by
  intro index b ks tail impossible
  cases index <;> simp [drop] at impossible

theorem BN.singleton {d : Nat} {context : ParentContext} (a : List Nat) {hs : Forests (List Nat)}
    (inside : BNForests d (context ++ [Parents.label d context a]) hs) : BN d context (.cons a hs .nil) :=
  ⟨headBN_nil d context a hs, inside, trivial⟩

theorem BN.drop {d : Nat} {context : ParentContext} {e : NumericalExpr}
    (ordered : BN d context e) (index : Nat) :
    BN d (dropContext d context index e) (Source.drop index e) := by
  induction index generalizing context e with
  | zero => exact ordered
  | succ index ih =>
    cases e with
    | nil => trivial
    | cons a hs rest => exact ih ordered.2.2

theorem BNForests.append {d : Nat} {context : ParentContext} {hs ks : Forests (List Nat)}
    (left : BNForests d context hs) (right : BNForests d context ks) :
    BNForests d context (appendForests hs ks) := by
  cases hs with
  | nil => exact right
  | cons h rest => exact ⟨left.1, left.2.append right⟩

theorem BNForests.dropLast {d : Nat} {context : ParentContext} {hs : Forests (List Nat)}
    (ordered : BNForests d context hs) : BNForests d context (dropLastForest hs) := by
  cases hs with
  | nil => rw [dropLastForest]; trivial
  | cons h rest =>
    cases rest with
    | nil => rw [dropLastForest]; trivial
    | cons k ks => rw [dropLastForest]; exact ⟨ordered.1, ordered.2.dropLast⟩

theorem BNForests.last {d : Nat} {context : ParentContext} {hs : Forests (List Nat)}
    (ordered : BNForests d context hs) {h : NumericalExpr} (found : lastForest? hs = some h) :
    BN d context h := by
  cases hs with
  | nil => simp [lastForest?] at found
  | cons k rest =>
    cases rest with
    | nil =>
      have same : k = h := by simpa only [lastForest?, Option.some.injEq] using found
      simpa only [same] using ordered.1
    | cons k ks => exact ordered.2.last (by simpa only [lastForest?] using found)

theorem repeatForest_BN {d : Nat} {context : ParentContext} {h : NumericalExpr}
    (ordered : BN d context h) (count : Nat) : BNForests d context (repeatForest h count) := by
  induction count with
  | zero => trivial
  | succ count ih => exact ⟨ordered, ih⟩

theorem headBN_singleton_distinct {d : Nat} {context : ParentContext} {a b : List Nat}
    {hs ks : Forests (List Nat)} (positive : 0 < d)
    (legal : FiniteLegal d context (.cons a hs (.cons b ks .nil)))
    (different : b[0]?.getD 0 ≠ a[0]?.getD 0) : HeadBN d context a hs (.cons b ks .nil) := by
  intro index c js tail found parents
  cases index with
  | zero =>
    have same : b = c ∧ ks = js ∧ Expr.nil = tail := by simpa only [drop, Expr.cons.injEq] using found
    obtain ⟨rfl, rfl, rfl⟩ := same
    exact False.elim (different (same_zero_parent_value positive (List.prefix_append _ _) _ _
      legal.2.1 legal.2.2.2.2.2.1 parents))
  | succ index => cases index <;> simp [drop] at found

theorem diagonalTail_BN (d depth value : Nat) (context : ParentContext) :
    BN d context (diagonalTail d depth value) := by
  induction depth generalizing context value with
  | zero => trivial
  | succ depth ih =>
    rw [diagonalTail]
    exact BN.singleton _ ⟨ih (value + 1) _, trivial⟩

theorem seed_BN (d depth : Nat) (positive : 0 < d) : BN d [] (seed d depth) := by
  cases depth with
  | zero => exact BN.singleton _ trivial
  | succ depth =>
    have legal := seed_finiteLegal d (depth + 1) positive
    refine ⟨headBN_singleton_distinct positive legal ?_, trivial, diagonalTail_BN d (depth + 1) 1 _⟩
    simp only [List.getElem?_replicate, if_pos positive, Option.getD_some]
    omega

end BTnSSBMS.Source
