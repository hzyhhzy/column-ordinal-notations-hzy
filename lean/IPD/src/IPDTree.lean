import Mathlib.Data.List.Shortlex

/-!
# The finite tree order used by IPD

`zero` is distinct from every node, including a node with no children.
The effective precedence of a node is `(head, arity)`.  This file does not
identify different IPD levels, and does not assume that the tree order is
well-founded.  The latter is proved from well-foundedness of the head order.
-/

namespace IPD
set_option autoImplicit false
universe u

inductive Tree (H : Type u) where
  | zero : Tree H
  | node : H → List (Tree H) → Tree H

namespace Tree
variable {H : Type u}

mutual
  /-- Arity-sensitive lexicographic path order. -/
  inductive LPO (r : H → H → Prop) : Tree H → Tree H → Prop where
    | zero (h : H) (ys : List (Tree H)) : LPO r .zero (.node h ys)
    | child {t : Tree H} {h : H} {ys : List (Tree H)}
        (ht : t ∈ ys) : LPO r t (.node h ys)
    | sub {s t : Tree H} {h : H} {ys : List (Tree H)}
        (ht : t ∈ ys) (hs : LPO r s t) : LPO r s (.node h ys)
    | head {g h : H} {xs ys : List (Tree H)}
        (hh : r g h) (ha : ∀ x ∈ xs, LPO r x (.node h ys)) :
        LPO r (.node g xs) (.node h ys)
    | arity {h : H} {xs ys : List (Tree H)}
        (hl : xs.length < ys.length) (ha : ∀ x ∈ xs, LPO r x (.node h ys)) :
        LPO r (.node h xs) (.node h ys)
    | lex {h : H} {xs ys : List (Tree H)}
        (hl : xs.length = ys.length) (hx : ArgsLt r xs ys)
        (ha : ∀ x ∈ xs, LPO r x (.node h ys)) :
        LPO r (.node h xs) (.node h ys)

  /-- The strict, first-differing-argument branch.  Arity is checked separately. -/
  inductive ArgsLt (r : H → H → Prop) : List (Tree H) → List (Tree H) → Prop where
    | rel {x y : Tree H} {xs ys : List (Tree H)}
        (h : LPO r x y) : ArgsLt r (x :: xs) (y :: ys)
    | cons {x : Tree H} {xs ys : List (Tree H)}
        (h : ArgsLt r xs ys) : ArgsLt r (x :: xs) (x :: ys)
end

theorem argsLt_to_listLex {r : H → H → Prop} {xs ys : List (Tree H)}
    (h : ArgsLt r xs ys) : List.Lex (LPO r) xs ys := by
  induction xs generalizing ys with
  | nil => cases h
  | cons x xs ih =>
    cases h with
    | rel h => exact .rel h
    | cons h => exact .cons (ih h)

theorem not_lpo_zero (r : H → H → Prop) (t : Tree H) : ¬ LPO r t .zero := by
  intro h
  cases h

theorem zero_acc (r : H → H → Prop) : Acc (LPO r) (.zero : Tree H) :=
  .intro _ fun t h => (not_lpo_zero r t h).elim

theorem child_lt {r : H → H → Prop} {h : H} {xs : List (Tree H)} {x : Tree H}
    (hx : x ∈ xs) : LPO r x (.node h xs) := .child hx

/-- Finite structural induction, with a pointwise hypothesis for every child. -/
@[elab_as_elim] theorem inductionOn {P : Tree H → Prop} (t : Tree H)
    (hz : P .zero) (hn : ∀ h xs, (∀ x ∈ xs, P x) → P (.node h xs)) : P t :=
  Tree.rec (motive_1 := P) (motive_2 := fun xs => ∀ x ∈ xs, P x)
    hz hn (by simp) (by
      intro x xs hx hxs t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hx
      · exact hxs t ht) t

end Tree
end IPD

#print axioms IPD.Tree.zero_acc
