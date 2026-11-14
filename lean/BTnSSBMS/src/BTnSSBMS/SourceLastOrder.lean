import BTnSSBMS.SourceTotality
import BTnSSBMS.KeyOrder
import BTnSSBMS.BMSDescent

/-!
Strict comparison at the real last-hole position. These facts concern the
frozen raw recursive order; they do not assert that this order is well-founded.
The replacement may have arbitrary finite length and arbitrary attachments.
-/
namespace BTnSSBMS.Source

theorem expr_compare_self (e : NumericalExpr) :
    e.compare (listCompare Ord.compare) e = .eq :=
  Ordering.eq_eq_of_eq_swap (Expr.compare_oriented _
    (listCompare_oriented _ (fun _ _ => Std.OrientedOrd.eq_swap)) e e)

theorem forests_compare_self (hs : Forests (List Nat)) :
    hs.compare (listCompare Ord.compare) hs = .eq :=
  Ordering.eq_eq_of_eq_swap (Forests.compare_oriented _
    (listCompare_oriented _ (fun _ _ => Std.OrientedOrd.eq_swap)) hs hs)

theorem dropLast_lt {e : NumericalExpr} (nonempty : e ≠ .nil) :
    (dropLast e).compare (listCompare Ord.compare) e = .lt := by
  cases e with
  | nil => exact False.elim (nonempty rfl)
  | cons a hs t =>
    cases t with
    | nil => simp only [dropLast, Expr.compare]
    | cons b ks u =>
      simp only [dropLast, Expr.compare, columnCompare_self, forests_compare_self]
      exact dropLast_lt (by intro impossible; cases impossible)

theorem dropLastForest_lt {hs : Forests (List Nat)} (nonempty : hs ≠ .nil) :
    (dropLastForest hs).compare (listCompare Ord.compare) hs = .lt := by
  cases hs with
  | nil => exact False.elim (nonempty rfl)
  | cons h rest =>
    cases rest with
    | nil => simp only [dropLastForest, Forests.compare]
    | cons k ks =>
      simp only [dropLastForest, Forests.compare, expr_compare_self]
      exact dropLastForest_lt (by intro impossible; cases impossible)

theorem modifyLast_lt (e : NumericalExpr)
    (f : List Nat × Forests (List Nat) → List Nat × Forests (List Nat))
    {a : List Nat} {hs : Forests (List Nat)} (selected : last? e = some (a, hs))
    (lower : (Expr.cons (f (a, hs)).1 (f (a, hs)).2 .nil).compare (listCompare Ord.compare)
      (.cons a hs .nil) = .lt) :
    (modifyLast f e).compare (listCompare Ord.compare) e = .lt := by
  cases e with
  | nil => simp [last?] at selected
  | cons b ks t =>
    cases t with
    | nil =>
      have same : (b, ks) = (a, hs) := by simpa only [last?, Option.some.injEq] using selected
      cases same
      simpa only [modifyLast] using lower
    | cons c js u =>
      simp only [modifyLast, Expr.compare, columnCompare_self, forests_compare_self]
      exact modifyLast_lt (.cons c js u) f (by simpa only [last?] using selected) lower

theorem modifyLastForest_lt (hs : Forests (List Nat)) (f : NumericalExpr → NumericalExpr)
    {h : NumericalExpr} (selected : lastForest? hs = some h)
    (lower : (f h).compare (listCompare Ord.compare) h = .lt) :
    (modifyLastForest f hs).compare (listCompare Ord.compare) hs = .lt := by
  cases hs with
  | nil => simp [lastForest?] at selected
  | cons k rest =>
    cases rest with
    | nil =>
      have same : k = h := by simpa only [lastForest?, Option.some.injEq] using selected
      subst h
      simp only [modifyLastForest, Forests.compare, lower]
    | cons u us =>
      simp only [modifyLastForest, Forests.compare, expr_compare_self]
      exact modifyLastForest_lt (.cons u us) f (by simpa only [lastForest?] using selected) lower

theorem replicate_pruned_last_lt (hs : Forests (List Nat)) {h : NumericalExpr}
    (selected : lastForest? hs = some h) (nonempty : h ≠ .nil) (count : Nat) :
    (appendForests (dropLastForest hs) (repeatForest (dropLast h) count)).compare
      (listCompare Ord.compare) hs = .lt := by
  cases hs with
  | nil => simp [lastForest?] at selected
  | cons k rest =>
    cases rest with
    | nil =>
      have same : k = h := by simpa only [lastForest?, Option.some.injEq] using selected
      subst h
      cases count with
      | zero => simp only [dropLastForest, repeatForest, appendForests, Forests.compare]
      | succ count =>
        simp only [dropLastForest, appendForests, repeatForest, Forests.compare, dropLast_lt nonempty]
    | cons u us =>
      simp only [dropLastForest, appendForests, Forests.compare, expr_compare_self]
      exact replicate_pruned_last_lt (.cons u us) (by simpa only [lastForest?] using selected) nonempty count

theorem special_spine_lt (count depth : Nat) {e stop : NumericalExpr}
    (selected : (spine e)[depth]? = some stop) {a : List Nat} {hs : Forests (List Nat)}
    (last : last? stop = some (a, hs)) {h : NumericalExpr}
    (child : lastForest? hs = some h) (nonempty : h ≠ .nil) :
    (special count depth e).compare (listCompare Ord.compare) e = .lt := by
  induction depth generalizing e with
  | zero =>
    have same : e = stop := by simpa only [spine, List.getElem?_cons_zero, Option.some.injEq] using selected
    subst e
    apply modifyLast_lt stop _ last
    simp only [child, Option.getD_some, Expr.compare, columnCompare_self,
      replicate_pruned_last_lt hs child nonempty count]
  | succ depth ih =>
    rw [spine_get_succ] at selected
    obtain ⟨next, atChild, below⟩ := Option.bind_eq_some_iff.mp selected
    obtain ⟨⟨b, ks⟩, atLast, forest⟩ := Option.bind_eq_some_iff.mp atChild
    have smaller := modifyLastForest_lt ks (special count depth) forest (ih below)
    apply modifyLast_lt e _ atLast
    simp only [Expr.compare, columnCompare_self, smaller]

theorem specialColumn_last_nonempty {a : List Nat} {hs : Forests (List Nat)}
    (special : specialColumn (a, hs) = true) :
    ∃ h, lastForest? hs = some h ∧ h ≠ .nil := by
  cases child : lastForest? hs with
  | none => simp [specialColumn, child] at special
  | some h =>
    refine ⟨h, rfl, ?_⟩
    intro empty
    simp [specialColumn, child, empty, last?] at special

mutual
  theorem splice_lt {d : Nat} {context : ParentContext} {owner : Option Nat}
      (depth : Nat) (e replacement : NumericalExpr) {site : HoleSite}
      (found : holeSite d context owner depth e = some site)
      (lower : replacement.compare (listCompare Ord.compare) (.cons site.terminal site.attached .nil) = .lt) :
      (splice depth replacement e).compare (listCompare Ord.compare) e = .lt := by
    cases e with
    | nil => simp [holeSite] at found
    | cons a hs rest =>
      cases rest with
      | nil =>
        cases depth with
        | zero =>
          have same : site = ⟨context, owner, a, hs⟩ := by simpa only [holeSite, Option.some.injEq] using found.symm
          subst site
          simpa only [splice] using lower
        | succ depth =>
          rw [holeSite] at found
          have small := spliceForests_lt depth hs replacement found lower
          simp only [splice, Expr.compare, columnCompare_self, small]
      | cons b ks tail =>
        rw [holeSite] at found
        have small := splice_lt depth (.cons b ks tail) replacement found lower
        simp only [splice, Expr.compare, columnCompare_self, forests_compare_self, small]
  theorem spliceForests_lt {d : Nat} {context : ParentContext} {owner : Nat}
      (depth : Nat) (hs : Forests (List Nat)) (replacement : NumericalExpr) {site : HoleSite}
      (found : holeSiteForests d context owner depth hs = some site)
      (lower : replacement.compare (listCompare Ord.compare) (.cons site.terminal site.attached .nil) = .lt) :
      (spliceForests depth replacement hs).compare (listCompare Ord.compare) hs = .lt := by
    cases hs with
    | nil => simp [holeSiteForests] at found
    | cons h rest =>
      cases rest with
      | nil =>
        rw [holeSiteForests] at found
        have small := splice_lt depth h replacement found lower
        simp only [spliceForests, Forests.compare, small]
      | cons k ks =>
        rw [holeSiteForests] at found
        have small := spliceForests_lt depth (.cons k ks) replacement found lower
        simp only [spliceForests, Forests.compare, expr_compare_self, small]
end

theorem marked_splice_lt {d : Nat} (cap root depth : Nat) (delta : List Nat)
    (e replacement : NumericalExpr) {site : HoleSite}
    (found : holeSite d [] none depth e = some site)
    (lower : replacement.compare (listCompare Ord.compare) (.cons site.terminal site.attached .nil) = .lt) :
    (ascendReplace (mark cap root [] (parents d e)) replacement (some depth) delta 0).compare
      (listCompare Ord.compare) e = .lt := by
  rw [ascendReplace_splice]
  have unchanged : (mark cap root [] (parents d e)).map (fun a => shift a.1 a.2 delta 0) = e := by
    simp only [shift_zero, mark_erase, parents_erase]
  rw [unchanged]
  exact splice_lt depth e replacement found lower

end BTnSSBMS.Source
