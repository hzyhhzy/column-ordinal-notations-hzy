import BTnSSBMS.SourceBlockOrder

/-! Scoped row-zero sibling facts used by BN. Actual parent identity,
not equality of coordinate labels, defines a sibling comparison. -/
namespace BTnSSBMS.Source

theorem dropContext_prefix (d : Nat) (context : ParentContext) (index : Nat) (e : NumericalExpr) :
    context <+: dropContext d context index e := by
  induction index generalizing context e with
  | zero => exact List.prefix_refl _
  | succ index ih =>
    cases e with
    | nil => exact List.prefix_refl _
    | cons a hs rest => exact (List.prefix_append _ _).trans (ih (context ++ [Parents.label d context a]) rest)

theorem dropContext_dropLast (d : Nat) (context : ParentContext) (index : Nat) (e : NumericalExpr)
    (inside : index < length e) :
    dropContext d context index (dropLast e) = dropContext d context index e := by
  induction index generalizing context e with
  | zero => rfl
  | succ index ih =>
    cases e with
    | nil => simp [length] at inside
    | cons a hs rest =>
      cases rest with
      | nil => simp only [length] at inside; omega
      | cons b ks tail =>
        simp only [dropLast, dropContext]
        exact ih _ (.cons b ks tail) (by simp only [length] at inside ⊢; omega)

theorem FiniteLegal.drop {d : Nat} {context : ParentContext} {e : NumericalExpr}
    (legal : FiniteLegal d context e) (index : Nat) :
    FiniteLegal d (dropContext d context index e) (Source.drop index e) := by
  induction index generalizing context e with
  | zero => exact legal
  | succ index ih =>
    cases e with
    | nil => trivial
    | cons a hs rest => exact ih legal.2.2.2.2

theorem same_zero_parent_value {d : Nat} (positive : 0 < d)
    {context target : ParentContext} (initial : context <+: target)
    (a b : List Nat)
    (left : Parents.UnitSteps d (context ++ [Parents.label d context a]))
    (right : Parents.UnitSteps d (target ++ [Parents.label d target b]))
    (same : (Parents.label d target b).parents[0]?.join = (Parents.label d context a).parents[0]?.join) :
    b[0]?.getD 0 = a[0]?.getD 0 := by
  have av := Parents.label_unit_value a left positive
  have bv := Parents.label_unit_value b right positive
  rw [same] at bv
  cases selected : (Parents.label d context a).parents[0]?.join with
  | none =>
    simp only [selected, Option.map_none, Option.getD_none] at av bv
    exact bv.trans av.symm
  | some p =>
    simp only [selected, Option.map_some, Option.getD_some] at av bv
    rw [← Parents.reading_prefix initial 0 p (Parents.label_parent_bound d context a 0 p selected)] at bv
    exact bv.trans av.symm

end BTnSSBMS.Source
