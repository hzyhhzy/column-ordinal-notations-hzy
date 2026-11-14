import BTnSSBMS.KeyOrder
import BTnSSBMS.SourceFS

/-! Appending one empty forest is an immediate lexical successor of a
complete key. Node counts alone do not order keys: the final strict
comparison also requires the stated upper comparison. -/
namespace BTnSSBMS.Keys

theorem append_empty_nodes (key : Key) :
    (Source.appendForests key (.cons .nil .nil)).nodes = key.nodes := by
  cases key with
  | nil => rfl
  | cons h rest => simp only [Source.appendForests, Forests.nodes, append_empty_nodes]

theorem below_empty_extension {a b : Key}
    (bounded : compare a (Source.appendForests b (.cons .nil .nil)) ≠ .gt)
    (different : a ≠ Source.appendForests b (.cons .nil .nil)) : compare a b ≠ .gt := by
  cases b with
  | nil =>
    cases a with
    | nil => decide
    | cons h rest =>
      cases h with
      | nil =>
        cases rest with
        | nil => exact False.elim (different rfl)
        | cons k tail => simp [compare, Source.appendForests, Forests.compare, Expr.compare] at bounded
      | cons c hs tail => simp [compare, Source.appendForests, Forests.compare, Expr.compare] at bounded
  | cons h rest =>
    cases a with
    | nil => simp only [compare, Forests.compare, ne_eq, reduceCtorEq, not_false_eq_true]
    | cons k tail =>
      cases first : k.compare (listCompare atomCompare) h with
      | lt => simp only [compare, Forests.compare, first, ne_eq, reduceCtorEq, not_false_eq_true]
      | gt =>
        simp only [compare, Source.appendForests, Forests.compare, first] at bounded
        exact False.elim (bounded rfl)
      | eq =>
        have head := Expr.compare_eq_imp _ (listCompare_eq_imp atomCompare atomCompare_eq_imp) k h first
        subst k
        have remaining : compare tail (Source.appendForests rest (.cons .nil .nil)) ≠ .gt := by
          simpa only [compare, Source.appendForests, Forests.compare, first] using bounded
        have notEqual : tail ≠ Source.appendForests rest (.cons .nil .nil) := by
          intro same
          exact different (congrArg (Forests.cons h) same)
        simpa only [compare, Forests.compare, first] using below_empty_extension remaining notEqual

theorem smaller_nodes_below_empty_extension {a b : Key}
    (smaller : a.nodes < b.nodes)
    (bounded : compare a (Source.appendForests b (.cons .nil .nil)) ≠ .gt) : compare a b = .lt := by
  have different : a ≠ Source.appendForests b (.cons .nil .nil) := by
    intro same
    have nodes := congrArg Forests.nodes same
    rw [append_empty_nodes] at nodes
    omega
  have weak := below_empty_extension bounded different
  cases order : compare a b with
  | lt => rfl
  | gt => exact False.elim (weak order)
  | eq =>
    have same := compare_eq_imp a b order
    subst a
    exact False.elim (Nat.lt_irrefl _ smaller)

mutual
  theorem forest_nodes (d owner : Nat) (base history : List Nat) (e : ParentExpr) :
      (forest d owner base history e).nodes = e.nodes := by
    cases e with
    | nil => rfl
    | cons a hs tail => simp only [forest, Expr.nodes, forests_nodes, forest_nodes]

  theorem forests_nodes (d owner : Nat) (base history : List Nat) (hs : Forests ParentLabel) :
      (forests d owner base history hs).nodes = hs.nodes := by
    cases hs with
    | nil => rfl
    | cons h rest => simp only [forests, Forests.nodes, forest_nodes, forests_nodes]
end

theorem source_key_nodes (d : Nat) (context : ParentContext) (position : List Nat)
    (hs : Forests (List Nat)) :
    (ofColumn d context.length (Parents.label d context position)
      (Parents.annotateForests d (context ++ [Parents.label d context position]) hs)).nodes = hs.nodes := by
  rw [ofColumn, forests_nodes, ← Forests.map_nodes ParentLabel.coordinates, Parents.annotateForests_erase]

theorem forests_append (d owner : Nat) (base history : List Nat) (hs ks : Forests ParentLabel) :
    forests d owner base history (Source.appendForests hs ks) =
      Source.appendForests (forests d owner base history hs) (forests d owner base history ks) := by
  cases hs with
  | nil => rfl
  | cons h rest => simp only [Source.appendForests, forests, forests_append]

end BTnSSBMS.Keys

namespace BTnSSBMS.Parents

theorem annotateForests_append (d : Nat) (context : ParentContext)
    (hs ks : Forests (List Nat)) :
    annotateForests d context (Source.appendForests hs ks) =
      Source.appendForests (annotateForests d context hs) (annotateForests d context ks) := by
  cases hs with
  | nil => rfl
  | cons h rest => simp only [Source.appendForests, annotateForests, annotateForests_append]

end BTnSSBMS.Parents

namespace BTnSSBMS.Keys

theorem source_key_append_empty (d : Nat) (context : ParentContext) (position : List Nat)
    (hs : Forests (List Nat)) :
    ofColumn d context.length (Parents.label d context position)
      (Parents.annotateForests d (context ++ [Parents.label d context position])
        (Source.appendForests hs (.cons .nil .nil))) =
      Source.appendForests (ofColumn d context.length (Parents.label d context position)
        (Parents.annotateForests d (context ++ [Parents.label d context position]) hs)) (.cons .nil .nil) := by
  rw [ofColumn, Parents.annotateForests_append, forests_append]
  rfl

end BTnSSBMS.Keys
