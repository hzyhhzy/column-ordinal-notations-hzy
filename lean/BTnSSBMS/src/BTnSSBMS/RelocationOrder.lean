import BTnSSBMS.RelocationComposition

/-! Exact comparison for the canonical transport, with a constructed
view at each recursive entry and restored scopes at forest exits. -/
namespace BTnSSBMS.Source

theorem relocationHead_lt {d : Nat} {source target : ParentContext} {visible : List Nat}
    (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
    (targetCoherent : Parents.Coherent d target) (view : Parents.NumericalView d source target visible)
    (a b : List Nat) (ha : a.length = d) (hb : b.length = d)
    (leftUnit : Parents.UnitSteps d (source ++ [Parents.label d source a]))
    (rightUnit : Parents.UnitSteps d (source ++ [Parents.label d source b]))
    (lower : listCompare Ord.compare a b = .lt) :
    listCompare Ord.compare (relocationHead d source target visible a)
      (relocationHead d source target visible b) = .lt := by
  obtain ⟨j, inside, common, strict⟩ := columnCompare_lt_exists_difference a b (ha.trans hb.symm) lower
  have room : j < d := by omega
  apply columnCompare_lt_at _ _ j (by rw [relocationHead_width]; exact room)
    (by rw [relocationHead_width]; exact room)
  · intro i before
    rw [relocationHead_value d source target visible a (by omega),
      relocationHead_value d source target visible b (by omega)]
    simp only [Parents.representedValue,
      Parents.label_parents_congr_through d source a b i (by omega) (fun k bound => common k (by omega))]
  · rw [relocationHead_value d source target visible a room, relocationHead_value d source target visible b room]
    exact Parents.representedValue_strict_at_difference sourceCoherent sourceValid targetCoherent view
      a b leftUnit rightUnit room common strict

theorem relocationHead_compare {d : Nat} {source target : ParentContext} {visible : List Nat}
    (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
    (targetCoherent : Parents.Coherent d target) (view : Parents.NumericalView d source target visible)
    (a b : List Nat) (ha : a.length = d) (hb : b.length = d)
    (leftUnit : Parents.UnitSteps d (source ++ [Parents.label d source a]))
    (rightUnit : Parents.UnitSteps d (source ++ [Parents.label d source b])) :
    listCompare Ord.compare (relocationHead d source target visible a)
      (relocationHead d source target visible b) = listCompare Ord.compare a b := by
  have oriented := listCompare_oriented Ord.compare
    (fun a b : Nat => Std.OrientedOrd.eq_swap (a := a) (b := b))
  cases order : listCompare Ord.compare a b with
  | lt => exact relocationHead_lt sourceCoherent sourceValid targetCoherent view a b ha hb leftUnit rightUnit order
  | eq =>
    have same := listCompare_eq_imp Ord.compare (fun _ _ h => Nat.compare_eq_eq.mp h) a b order
    subst b
    exact listCompare_self Ord.compare (fun a : Nat => Nat.compare_eq_eq.mpr rfl) _
  | gt =>
    have opposite := oriented b a
    simp only [order, Ordering.swap] at opposite
    have reverse := relocationHead_lt sourceCoherent sourceValid targetCoherent view b a hb ha rightUnit leftUnit opposite
    rw [oriented, reverse]
    rfl

mutual
  theorem relocate_compare (d : Nat) (e f : NumericalExpr) (source target : ParentContext) (visible : List Nat)
      (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
      (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
      (view : Parents.NumericalView d source target visible)
      (leftLegal : FiniteLegal d source e) (rightLegal : FiniteLegal d source f) :
      (relocate d source target visible e).compare (listCompare Ord.compare)
        (relocate d source target visible f) = e.compare (listCompare Ord.compare) f := by
    cases e with
    | nil => cases f <;> rfl
    | cons a hs tail =>
      cases f with
      | nil => rfl
      | cons b ks rest =>
        have heads := relocationHead_compare sourceCoherent sourceValid targetCoherent view
          a b leftLegal.1 rightLegal.1 leftLegal.2.1 rightLegal.2.1
        cases order : listCompare Ord.compare a b with
        | lt => simp only [relocate, Expr.compare, heads, order]
        | gt => simp only [relocate, Expr.compare, heads, order]
        | eq =>
          have same := listCompare_eq_imp Ord.compare (fun _ _ h => Nat.compare_eq_eq.mp h) a b order
          subst b
          have next := relocation_view_append sourceCoherent sourceValid targetCoherent targetValid view a
          have inside := relocateForests_compare d hs ks
            (source ++ [Parents.label d source a])
            (target ++ [Parents.label d target (relocationHead d source target visible a)])
            (visible ++ [target.length])
            (Parents.coherent_append_label sourceCoherent a) (Parents.context_valid_append_label d source sourceValid a)
            (Parents.coherent_append_label targetCoherent _) (Parents.context_valid_append_label d target targetValid _)
            next (a[0]?.getD 0) leftLegal.2.2.2.1 rightLegal.2.2.2.1
          have after := relocate_compare d tail rest
            (source ++ [Parents.label d source a])
            (target ++ [Parents.label d target (relocationHead d source target visible a)])
            (visible ++ [target.length])
            (Parents.coherent_append_label sourceCoherent a) (Parents.context_valid_append_label d source sourceValid a)
            (Parents.coherent_append_label targetCoherent _) (Parents.context_valid_append_label d target targetValid _)
            next leftLegal.2.2.2.2 rightLegal.2.2.2.2
          simp only [relocate, Expr.compare, heads, order, inside, after]

  theorem relocateForests_compare (d : Nat) (hs ks : Forests (List Nat))
      (source target : ParentContext) (visible : List Nat)
      (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
      (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
      (view : Parents.NumericalView d source target visible) (owner : Nat)
      (leftLegal : FiniteLegalForests d source owner hs) (rightLegal : FiniteLegalForests d source owner ks) :
      (relocateForests d source target visible hs).compare (listCompare Ord.compare)
        (relocateForests d source target visible ks) = hs.compare (listCompare Ord.compare) ks := by
    cases hs with
    | nil => cases ks <;> rfl
    | cons h hs =>
      cases ks with
      | nil => rfl
      | cons k ks =>
        simp only [relocateForests, Forests.compare,
          relocate_compare d h k source target visible sourceCoherent sourceValid targetCoherent targetValid view
            leftLegal.2.1 rightLegal.2.1,
          relocateForests_compare d hs ks source target visible sourceCoherent sourceValid targetCoherent targetValid view
            owner leftLegal.2.2 rightLegal.2.2]
end

end BTnSSBMS.Source
