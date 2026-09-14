import IPDTreeLinearOrder
import Mathlib.Order.Compare

/-!
# Correspondence with the tree comparator in ipd.py

`nodeRule` is the literal branch sequence: equality, a left child at least
the right tree, a right child at least the left tree, head, arity, arguments.
`cmp_node_rule` proves the mathematical order satisfies this recursion equation.
All recursive calls concern proper children (or the lower-layer head), so the
equation determines the same finite comparison as the reference program.
-/

namespace IPD.Tree
set_option autoImplicit false
set_option maxHeartbeats 800000
universe u
variable {H : Type u} [LinearOrder H] [WellFoundedLT H]

noncomputable def nodeRule (g h : H) (xs ys : List (Tree H)) : Ordering := by
  classical
  exact
    if (.node g xs : Tree H) = .node h ys then .eq
    else if ∃ x ∈ xs, cmp x (.node h ys) ≠ .lt then .gt
    else if ∃ y ∈ ys, cmp y (.node g xs) ≠ .lt then .lt
    else if g ≠ h then cmp g h
    else if xs.length ≠ ys.length then cmp xs.length ys.length
    else if List.Lex ((· < ·) : Tree H → Tree H → Prop) xs ys then .lt
    else if xs = ys then .eq else .gt

theorem nodeRule_compares (g h : H) (xs ys : List (Tree H)) :
    (nodeRule g h xs ys).Compares (Tree.node g xs) (Tree.node h ys) := by
  classical
  unfold nodeRule
  split
  · rename_i heq
    exact heq
  · rename_i hne
    split
    · rename_i hx
      obtain ⟨x, hx, hc⟩ := hx
      exact lt_of_le_of_lt ((cmp_compares _ _).ne_lt.mp hc) (child_lt hx)
    · rename_i hx
      split
      · rename_i hy
        obtain ⟨y, hy, hc⟩ := hy
        exact lt_of_le_of_lt ((cmp_compares _ _).ne_lt.mp hc) (child_lt hy)
      · rename_i hy
        have hxs : ∀ x ∈ xs, x < (.node h ys : Tree H) := by
          intro x hm
          by_contra hn
          have hc : cmp x (.node h ys) ≠ .lt := (cmp_compares _ _).ne_lt.mpr (not_lt.mp hn)
          exact hx ⟨x, hm, hc⟩
        have hys : ∀ y ∈ ys, y < (.node g xs : Tree H) := by
          intro y hm
          by_contra hn
          have hc : cmp y (.node g xs) ≠ .lt := (cmp_compares _ _).ne_lt.mpr (not_lt.mp hn)
          exact hy ⟨y, hm, hc⟩
        rcases lt_trichotomy g h with hgh | heq | hhg
        · rw [if_pos (ne_of_lt hgh), (cmp_compares g h).eq_lt.mpr hgh]
          exact LPO.head hgh hxs
        · subst h
          rw [if_neg (not_not.mpr rfl)]
          rcases lt_trichotomy xs.length ys.length with hlen | hlen | hlen
          · rw [if_pos (ne_of_lt hlen), (cmp_compares xs.length ys.length).eq_lt.mpr hlen]
            exact LPO.arity hlen hxs
          · rw [if_neg (not_not.mpr hlen)]
            rcases lt_trichotomy xs ys with hargs | heq | hargs
            · rw [if_pos (show List.Lex ((· < ·) : Tree H → Tree H → Prop) xs ys from hargs)]
              exact LPO.lex hlen (argsLt_of_listLex hlen hargs) hxs
            · exact (hne (congrArg (Tree.node g) heq)).elim
            · rw [if_neg (show ¬ List.Lex ((· < ·) : Tree H → Tree H → Prop) xs ys from
                not_lt_of_gt hargs), if_neg (ne_of_gt hargs)]
              exact LPO.lex hlen.symm (argsLt_of_listLex hlen.symm hargs) hys
          · rw [if_pos (ne_of_gt hlen), (cmp_compares xs.length ys.length).eq_gt.mpr hlen]
            exact LPO.arity hlen hys
        · rw [if_pos (ne_of_gt hhg), (cmp_compares g h).eq_gt.mpr hhg]
          exact LPO.head hhg hys

theorem cmp_node_rule (g h : H) (xs ys : List (Tree H)) :
    cmp (.node g xs : Tree H) (.node h ys) = nodeRule g h xs ys :=
  (cmp_compares _ _).inj (nodeRule_compares g h xs ys)

@[simp] theorem cmp_zero_node (h : H) (xs : List (Tree H)) :
    cmp (.zero : Tree H) (.node h xs) = .lt :=
  (cmp_compares _ _).eq_lt.mpr (LPO.zero h xs)

@[simp] theorem cmp_node_zero (h : H) (xs : List (Tree H)) :
    cmp (.node h xs : Tree H) .zero = .gt :=
  (cmp_compares _ _).eq_gt.mpr (LPO.zero h xs)

end IPD.Tree

#print axioms IPD.Tree.cmp_node_rule
#print axioms IPD.Tree.cmp_zero_node
#print axioms IPD.Tree.cmp_node_zero
