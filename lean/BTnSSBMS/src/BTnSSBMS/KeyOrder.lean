import BTnSSBMS.KeyEquality
import Init.Data.Order.Ord

namespace BTnSSBMS

theorem listCompare_oriented (cmp : α → α → Ordering)
    (flip : ∀ a b, cmp a b = (cmp b a).swap) (xs ys : List α) :
    listCompare cmp xs ys = (listCompare cmp ys xs).swap := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      have first := flip x y
      cases h : cmp y x <;> simp only [h, Ordering.swap] at first <;>
        simp only [listCompare, h, first, Ordering.swap, ih]

mutual
  theorem Expr.compare_oriented (cmp : α → α → Ordering)
      (flip : ∀ a b, cmp a b = (cmp b a).swap) (e f : Expr α) :
      e.compare cmp f = (f.compare cmp e).swap := by
    cases e with
    | nil => cases f <;> rfl
    | cons a hs t =>
      cases f with
      | nil => rfl
      | cons b ks u =>
        have first := flip a b
        have forests := Forests.compare_oriented cmp flip hs ks
        have tail := Expr.compare_oriented cmp flip t u
        cases h : cmp b a <;> cases k : ks.compare cmp hs <;>
          simp only [h, k, Ordering.swap] at first forests <;>
          simp only [Expr.compare, h, k, first, forests, Ordering.swap, tail]
  theorem Forests.compare_oriented (cmp : α → α → Ordering)
      (flip : ∀ a b, cmp a b = (cmp b a).swap) (hs ks : Forests α) :
      hs.compare cmp ks = (ks.compare cmp hs).swap := by
    cases hs with
    | nil => cases ks <;> rfl
    | cons h hs =>
      cases ks with
      | nil => rfl
      | cons k ks =>
        have first := Expr.compare_oriented cmp flip h k
        have tail := Forests.compare_oriented cmp flip hs ks
        cases hk : k.compare cmp h <;> simp only [hk, Ordering.swap] at first <;>
          simp only [Forests.compare, hk, first, Ordering.swap, tail]
end

private theorem then_lt_trans (cmp : α → α → Ordering)
    (faithful : ∀ a b, cmp a b = .eq → a = b) (a b c : α)
    (firstTrans : cmp a b = .lt → cmp b c = .lt → cmp a c = .lt)
    (ab bc ac : Ordering) (tailTrans : ab = .lt → bc = .lt → ac = .lt)
    (left : (cmp a b).then ab = .lt) (right : (cmp b c).then bc = .lt) :
    (cmp a c).then ac = .lt := by
  cases hab : cmp a b with
  | gt => simp [hab] at left
  | lt =>
    cases hbc : cmp b c with
    | gt => simp [hbc] at right
    | lt => simp [firstTrans hab hbc]
    | eq => have same := faithful b c hbc; subst c; simp [hab]
  | eq =>
    have same := faithful a b hab
    subst b
    cases hac : cmp a c with
    | gt => simp [hac] at right
    | lt => simp
    | eq => simp [tailTrans (by simpa [hab] using left) (by simpa [hac] using right)]

theorem listCompare_lt_trans (cmp : α → α → Ordering)
    (faithful : ∀ a b, cmp a b = .eq → a = b)
    (trans : ∀ a b c, cmp a b = .lt → cmp b c = .lt → cmp a c = .lt)
    (xs ys zs : List α) (left : listCompare cmp xs ys = .lt)
    (right : listCompare cmp ys zs = .lt) : listCompare cmp xs zs = .lt := by
  induction xs generalizing ys zs with
  | nil => cases zs <;> cases ys <;> simp_all [listCompare]
  | cons x xs ih =>
    cases ys with
    | nil => simp [listCompare] at left
    | cons y ys =>
      cases zs with
      | nil => simp [listCompare] at right
      | cons z zs =>
        exact then_lt_trans cmp faithful x y z (trans x y z)
          _ _ _ (ih ys zs) left right

mutual
  theorem Expr.compare_lt_trans (cmp : α → α → Ordering)
      (faithful : ∀ a b, cmp a b = .eq → a = b)
      (trans : ∀ a b c, cmp a b = .lt → cmp b c = .lt → cmp a c = .lt)
      (e f g : Expr α) (left : e.compare cmp f = .lt) (right : f.compare cmp g = .lt) :
      e.compare cmp g = .lt := by
    cases e with
    | nil => cases g <;> cases f <;> simp_all [Expr.compare]
    | cons a hs t =>
      cases f with
      | nil => simp [Expr.compare] at left
      | cons b ks u =>
        cases g with
        | nil => simp [Expr.compare] at right
        | cons c ls v =>
          apply then_lt_trans cmp faithful a b c (trans a b c) _ _ _ _ left right
          exact then_lt_trans (Forests.compare cmp) (Forests.compare_eq_imp cmp faithful)
            hs ks ls (Forests.compare_lt_trans cmp faithful trans hs ks ls) _ _ _
            (Expr.compare_lt_trans cmp faithful trans t u v)
  theorem Forests.compare_lt_trans (cmp : α → α → Ordering)
      (faithful : ∀ a b, cmp a b = .eq → a = b)
      (trans : ∀ a b c, cmp a b = .lt → cmp b c = .lt → cmp a c = .lt)
      (hs ks ls : Forests α) (left : hs.compare cmp ks = .lt)
      (right : ks.compare cmp ls = .lt) : hs.compare cmp ls = .lt := by
    cases hs with
    | nil => cases ls <;> cases ks <;> simp_all [Forests.compare]
    | cons h hs =>
      cases ks with
      | nil => simp [Forests.compare] at left
      | cons k ks =>
        cases ls with
        | nil => simp [Forests.compare] at right
        | cons l ls =>
          exact then_lt_trans (Expr.compare cmp) (Expr.compare_eq_imp cmp faithful)
            h k l (Expr.compare_lt_trans cmp faithful trans h k l) _ _ _
            (Forests.compare_lt_trans cmp faithful trans hs ks ls) left right
end

namespace Keys

theorem atomCompare_oriented (a b : KeyAtom) :
    atomCompare a b = (atomCompare b a).swap := by
  obtain ⟨a, x⟩ := a
  obtain ⟨b, y⟩ := b
  have ints := Std.OrientedOrd.eq_swap (a := x) (b := y)
  cases a <;> cases b <;> simp [atomCompare]
  all_goals exact ints

theorem compare_oriented (a b : Key) : compare a b = (compare b a).swap :=
  Forests.compare_oriented _ (listCompare_oriented _ atomCompare_oriented) a b

theorem compare_self (key : Key) : compare key key = .eq :=
  Ordering.eq_eq_of_eq_swap (compare_oriented key key)

theorem compare_asymmetric (a b : Key) (h : compare a b = .lt) :
    compare b a ≠ .lt := by
  intro back
  have flip := compare_oriented a b
  simp [h, back] at flip

theorem atomCompare_lt_trans (a b c : KeyAtom)
    (left : atomCompare a b = .lt) (right : atomCompare b c = .lt) :
    atomCompare a c = .lt := by
  obtain ⟨a, x⟩ := a
  obtain ⟨b, y⟩ := b
  obtain ⟨c, z⟩ := c
  cases a <;> cases b <;> cases c <;>
    simp_all [atomCompare, Int.compare_eq_lt] <;> omega

theorem compare_lt_trans (a b c : Key) (left : compare a b = .lt)
    (right : compare b c = .lt) : compare a c = .lt :=
  Forests.compare_lt_trans _ (listCompare_eq_imp _ atomCompare_eq_imp)
    (listCompare_lt_trans _ atomCompare_eq_imp atomCompare_lt_trans) a b c left right

end Keys
end BTnSSBMS
