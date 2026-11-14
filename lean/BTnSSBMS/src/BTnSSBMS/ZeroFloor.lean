import BTnSSBMS.TerminalSplice

/-! A replacement fenced below by its first row-zero value cannot
create a new external zero-parent above that floor. Parent searches
are the actual scoped searches, including the parentless case. -/
namespace BTnSSBMS.Parents

theorem label_zero_append_ge {d : Nat} (positive : 0 < d)
    (context : ParentContext) (a query : List Nat)
    (high : query[0]?.getD 0 ≤ a[0]?.getD 0) :
    (label d (context ++ [label d context a]) query).parents[0]?.join =
      (label d context query).parents[0]?.join := by
  rw [label_zero d _ query positive, label_zero d context query positive]
  simp only [List.length_append, List.length_cons, List.length_nil]
  rw [search, List.getElem?_concat_length]
  simp only [label, show ¬ a[0]?.getD 0 < query[0]?.getD 0 by omega, if_false]
  exact (search_prefix (List.prefix_append _ _) 0 (query[0]?.getD 0) context.length (Nat.le_refl _)).symm

end BTnSSBMS.Parents

namespace BTnSSBMS.Source

theorem label_zero_dropContext_ge {d : Nat} (positive : 0 < d)
    (context : ParentContext) (index : Nat) (e : NumericalExpr) (query : List Nat)
    (high : ∀ a ∈ labels e, query[0]?.getD 0 ≤ a[0]?.getD 0) :
    (Parents.label d (dropContext d context index e) query).parents[0]?.join =
      (Parents.label d context query).parents[0]?.join := by
  induction index generalizing context e with
  | zero => rfl
  | succ index ih =>
    cases e with
    | nil => rfl
    | cons a hs rest =>
      rw [dropContext, ih _ rest (fun b member => high b (List.mem_cons_of_mem a member))]
      exact Parents.label_zero_append_ge positive context a query (high a (by simp [labels]))

/-- Any head in a floor-fenced replacement whose zero-parent is still
external has the floor value itself, rather than a larger value. -/
theorem external_suffix_floor {d : Nat} (positive : 0 < d)
    (context : ParentContext) (a : List Nat) (hs : Forests (List Nat)) (rest : NumericalExpr)
    (index : Nat) {b : List Nat} {ks : Forests (List Nat)} {tail : NumericalExpr}
    (found : drop index (.cons a hs rest) = .cons b ks tail)
    (high : ∀ c ∈ labels (.cons a hs rest), a[0]?.getD 0 ≤ c[0]?.getD 0)
    (external : ∀ p,
      (Parents.label d (dropContext d context index (.cons a hs rest)) b).parents[0]?.join = some p →
      p < context.length) : b[0]?.getD 0 = a[0]?.getD 0 := by
  have lower := high b (List.mem_of_getElem? (labels_drop_head index (.cons a hs rest) found))
  apply Nat.le_antisymm _ lower
  apply Nat.le_of_not_gt
  intro higher
  cases index with
  | zero =>
    have same : a = b := (Expr.cons.inj (by simpa only [drop] using found)).1
    rw [same] at higher
    omega
  | succ index =>
    let entry := context ++ [Parents.label d context a]
    let later := dropContext d entry index rest
    have initial : entry <+: later := dropContext_prefix d entry index rest
    have inside : context.length < entry.length := by simp [entry]
    have before : context.length < later.length := Nat.lt_of_lt_of_le inside initial.length_le
    have reading : Parents.reading later 0 context.length = a[0]?.getD 0 := by
      rw [← Parents.reading_prefix initial 0 context.length inside]
      exact Parents.reading_append_label d context a 0
    obtain ⟨p, after, hit⟩ := Parents.search_zero_exists_above later (b[0]?.getD 0)
      later.length context.length (Nat.le_refl _) before (by rw [reading]; exact higher)
    have bound := external p (by
      change (Parents.label d later b).parents[0]?.join = some p
      rw [Parents.label_zero d later b positive]
      exact hit)
    omega

theorem external_suffix_parent {d : Nat} (positive : 0 < d)
    (context : ParentContext) (a : List Nat) (hs : Forests (List Nat)) (rest : NumericalExpr)
    (index : Nat) {b : List Nat} {ks : Forests (List Nat)} {tail : NumericalExpr}
    (found : drop index (.cons a hs rest) = .cons b ks tail)
    (high : ∀ c ∈ labels (.cons a hs rest), a[0]?.getD 0 ≤ c[0]?.getD 0)
    (external : ∀ p,
      (Parents.label d (dropContext d context index (.cons a hs rest)) b).parents[0]?.join = some p →
      p < context.length) :
    (Parents.label d (dropContext d context index (.cons a hs rest)) b).parents[0]?.join =
      (Parents.label d context a).parents[0]?.join := by
  have same := external_suffix_floor positive context a hs rest index found high external
  rw [label_zero_dropContext_ge positive context index (.cons a hs rest) b
    (by intro c member; rw [same]; exact high c member),
    Parents.label_zero d context b positive, Parents.label_zero d context a positive, same]

theorem BN.external_block_le {d : Nat} {context : ParentContext}
    {a : List Nat} {hs : Forests (List Nat)} {rest : NumericalExpr}
    (ordered : BN d context (.cons a hs rest)) (positive : 0 < d)
    (index : Nat) {b : List Nat} {ks : Forests (List Nat)} {tail : NumericalExpr}
    (found : Source.drop index (.cons a hs rest) = .cons b ks tail)
    (high : ∀ c ∈ labels (.cons a hs rest), a[0]?.getD 0 ≤ c[0]?.getD 0)
    (external : ∀ p,
      (Parents.label d (dropContext d context index (.cons a hs rest)) b).parents[0]?.join = some p →
      p < context.length) :
    ExprLE (rootBlock (.cons b ks tail)) (rootBlock (.cons a hs rest)) := by
  have parents := external_suffix_parent positive context a hs rest index found high external
  cases index with
  | zero =>
    change Expr.cons a hs rest = .cons b ks tail at found
    rw [found]
    exact .refl _
  | succ index => exact ordered.1 index b ks tail found parents

end BTnSSBMS.Source
