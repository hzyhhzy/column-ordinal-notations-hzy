import BTnSSBMS.SourceDescent

/-!
The actual hereditary forest-list order condition HW. It is a finite
syntactic predicate, not well-foundedness and not a definition of standardness.
All forests in one attached list use the same source entry context.
-/
namespace BTnSSBMS.Source

def ExprLE (e f : NumericalExpr) : Prop := e.compare (listCompare Ord.compare) f ≠ .gt

theorem ExprLE.refl (e : NumericalExpr) : ExprLE e e := by
  simp only [ExprLE, expr_compare_self, ne_eq, reduceCtorEq, not_false_eq_true]

theorem ExprLE.of_lt {e f : NumericalExpr}
    (less : e.compare (listCompare Ord.compare) f = .lt) : ExprLE e f := by
  simp only [ExprLE, less, ne_eq, reduceCtorEq, not_false_eq_true]

theorem ExprLE.trans {e f g : NumericalExpr} (first : ExprLE e f) (second : ExprLE f g) : ExprLE e g := by
  cases ef : e.compare (listCompare Ord.compare) f with
  | gt => exact False.elim (first ef)
  | eq =>
    have same := Expr.compare_eq_imp _
      (fun _ _ h => listCompare_eq_imp _ (fun _ _ k => Nat.compare_eq_eq.mp k) _ _ h) e f ef
    subst f
    exact second
  | lt =>
    cases fg : f.compare (listCompare Ord.compare) g with
    | gt => exact False.elim (second fg)
    | eq =>
      have same := Expr.compare_eq_imp _
        (fun _ _ h => listCompare_eq_imp _ (fun _ _ k => Nat.compare_eq_eq.mp k) _ _ h) f g fg
      subst g
      exact first
    | lt => exact .of_lt (expr_compare_lt_trans e f g ef fg)

def ForestsLE : Forests (List Nat) → NumericalExpr → Prop
  | .nil, _ => True
  | .cons h hs, bound => ExprLE h bound ∧ ForestsLE hs bound

mutual
  def HW : NumericalExpr → Prop
    | .nil => True
    | .cons _ hs rest => HWForests hs ∧ HW rest
  def HWForests : Forests (List Nat) → Prop
    | .nil => True
    | .cons h hs => HW h ∧ ForestsLE hs h ∧ HWForests hs
end

theorem ForestsLE.mono {hs : Forests (List Nat)} {a b : NumericalExpr}
    (bounded : ForestsLE hs a) (larger : ExprLE a b) : ForestsLE hs b := by
  cases hs with
  | nil => trivial
  | cons h rest => exact ⟨bounded.1.trans larger, bounded.2.mono larger⟩

theorem ForestsLE.last {hs : Forests (List Nat)} {bound h : NumericalExpr}
    (bounded : ForestsLE hs bound) (selected : lastForest? hs = some h) : ExprLE h bound := by
  cases hs with
  | nil => simp [lastForest?] at selected
  | cons k rest =>
    cases rest with
    | nil =>
      have same : k = h := by simpa only [lastForest?, Option.some.injEq] using selected
      simpa only [same] using bounded.1
    | cons k ks => exact bounded.2.last (by simpa only [lastForest?] using selected)

theorem ForestsLE.dropLast {hs : Forests (List Nat)} {bound : NumericalExpr}
    (bounded : ForestsLE hs bound) : ForestsLE (dropLastForest hs) bound := by
  cases hs with
  | nil => simp only [dropLastForest, ForestsLE]
  | cons h rest =>
    cases rest with
    | nil => simp only [dropLastForest, ForestsLE]
    | cons k ks => rw [dropLastForest]; exact ⟨bounded.1, bounded.2.dropLast⟩

theorem ForestsLE.append {hs ks : Forests (List Nat)} {bound : NumericalExpr}
    (left : ForestsLE hs bound) (right : ForestsLE ks bound) : ForestsLE (appendForests hs ks) bound := by
  cases hs with
  | nil => exact right
  | cons h rest => exact ⟨left.1, left.2.append right⟩

theorem repeatForest_bounded {h bound : NumericalExpr} (bounded : ExprLE h bound) (count : Nat) :
    ForestsLE (repeatForest h count) bound := by
  induction count with
  | zero => trivial
  | succ count ih => exact ⟨bounded, ih⟩

theorem HW.dropLast {e : NumericalExpr} (ordered : HW e) : HW (Source.dropLast e) := by
  cases e with
  | nil => simp only [Source.dropLast, HW]
  | cons a hs rest =>
    cases rest with
    | nil => simp only [Source.dropLast, HW]
    | cons b ks t => rw [Source.dropLast]; exact ⟨ordered.1, ordered.2.dropLast⟩

theorem dropLast_le (e : NumericalExpr) : ExprLE (dropLast e) e := by
  cases e with
  | nil => rw [dropLast]; exact .refl _
  | cons a hs rest => exact .of_lt (dropLast_lt (by intro impossible; cases impossible))

theorem HWForests.dropLast {hs : Forests (List Nat)} (ordered : HWForests hs) :
    HWForests (dropLastForest hs) := by
  cases hs with
  | nil => simp only [dropLastForest, HWForests]
  | cons h rest =>
    cases rest with
    | nil => simp only [dropLastForest, HWForests]
    | cons k ks => rw [dropLastForest]; exact ⟨ordered.1, ordered.2.1.dropLast, ordered.2.2.dropLast⟩

theorem HWForests.last {hs : Forests (List Nat)} {h : NumericalExpr}
    (ordered : HWForests hs) (selected : lastForest? hs = some h) : HW h := by
  cases hs with
  | nil => simp [lastForest?] at selected
  | cons k rest =>
    cases rest with
    | nil =>
      have same : k = h := by simpa only [lastForest?, Option.some.injEq] using selected
      simpa only [same] using ordered.1
    | cons k ks => exact ordered.2.2.last (by simpa only [lastForest?] using selected)

theorem HW.last {e : NumericalExpr} {a : List Nat} {hs : Forests (List Nat)}
    (ordered : HW e) (selected : last? e = some (a, hs)) : HWForests hs := by
  cases e with
  | nil => simp [last?] at selected
  | cons b ks rest =>
    cases rest with
    | nil =>
      have same : (b, ks) = (a, hs) := by simpa only [last?, Option.some.injEq] using selected
      cases same
      exact ordered.1
    | cons b ks t => exact ordered.2.last (by simpa only [last?] using selected)

theorem HW.drop (count : Nat) {e : NumericalExpr} (ordered : HW e) : HW (Source.drop count e) := by
  induction count generalizing e with
  | zero => exact ordered
  | succ count ih =>
    cases e with
    | nil => trivial
    | cons a hs rest => exact ih ordered.2

theorem HW.spine {e stop : NumericalExpr} (ordered : HW e) (depth : Nat)
    (selected : (Source.spine e)[depth]? = some stop) : HW stop := by
  induction depth generalizing e with
  | zero =>
    have same : e = stop := by simpa only [Source.spine, List.getElem?_cons_zero, Option.some.injEq] using selected
    simpa only [same] using ordered
  | succ depth ih =>
    rw [spine_get_succ] at selected
    obtain ⟨h, child, below⟩ := Option.bind_eq_some_iff.mp selected
    obtain ⟨⟨a, hs⟩, last, forest⟩ := Option.bind_eq_some_iff.mp child
    exact ih ((ordered.last last).last forest) below

theorem repeatForest_HW {h : NumericalExpr} (ordered : HW h) (count : Nat) : HWForests (repeatForest h count) := by
  induction count with
  | zero => trivial
  | succ count ih => exact ⟨ordered, repeatForest_bounded (.refl h) count, ih⟩

theorem pruneRepeat_HW {hs : Forests (List Nat)} (ordered : HWForests hs)
    {h : NumericalExpr} (selected : lastForest? hs = some h) (count : Nat) :
    HWForests (appendForests (dropLastForest hs) (repeatForest (dropLast h) count)) := by
  cases hs with
  | nil => simp [lastForest?] at selected
  | cons k rest =>
    cases rest with
    | nil =>
      have same : k = h := by simpa only [lastForest?, Option.some.injEq] using selected
      subst h
      rw [dropLastForest, appendForests]
      exact repeatForest_HW ordered.1.dropLast count
    | cons k ks =>
      have selected' : lastForest? (.cons k ks) = some h := by simpa only [lastForest?] using selected
      rw [dropLastForest, appendForests]
      exact ⟨ordered.1, ordered.2.1.dropLast.append
        (repeatForest_bounded ((dropLast_le h).trans (ordered.2.1.last selected')) count),
        pruneRepeat_HW ordered.2.2 selected' count⟩

theorem HW.modifyLast {e : NumericalExpr} (ordered : HW e)
    (f : List Nat × Forests (List Nat) → List Nat × Forests (List Nat))
    (preserves : ∀ a hs, last? e = some (a, hs) → HWForests hs → HWForests (f (a, hs)).2) :
    HW (Source.modifyLast f e) := by
  cases e with
  | nil => simp only [Source.modifyLast, HW]
  | cons a hs rest =>
    cases rest with
    | nil => rw [Source.modifyLast]; exact ⟨preserves a hs (by rw [last?]) ordered.1, trivial⟩
    | cons b ks t => rw [Source.modifyLast]; exact ⟨ordered.1, ordered.2.modifyLast f
        (fun a hs atLast h => preserves a hs (by simpa only [last?] using atLast) h)⟩

theorem ForestsLE.modifyLast {hs : Forests (List Nat)} {bound : NumericalExpr}
    (bounded : ForestsLE hs bound) (f : NumericalExpr → NumericalExpr)
    (lower : ∀ h, lastForest? hs = some h → ExprLE (f h) h) :
    ForestsLE (modifyLastForest f hs) bound := by
  cases hs with
  | nil => simp only [modifyLastForest, ForestsLE]
  | cons h rest =>
    cases rest with
    | nil => rw [modifyLastForest]; exact ⟨(lower h (by rw [lastForest?])).trans bounded.1, trivial⟩
    | cons k ks => rw [modifyLastForest]; exact ⟨bounded.1, bounded.2.modifyLast f
        (fun h found => lower h (by simpa only [lastForest?] using found))⟩

theorem HWForests.modifyLast {hs : Forests (List Nat)} (ordered : HWForests hs)
    (f : NumericalExpr → NumericalExpr)
    (preserves : ∀ h, lastForest? hs = some h → HW h → HW (f h))
    (lower : ∀ h, lastForest? hs = some h → ExprLE (f h) h) :
    HWForests (modifyLastForest f hs) := by
  cases hs with
  | nil => simp only [modifyLastForest, HWForests]
  | cons h rest =>
    cases rest with
    | nil => rw [modifyLastForest]; exact ⟨preserves h (by rw [lastForest?]) ordered.1, trivial, trivial⟩
    | cons k ks => rw [modifyLastForest]; exact ⟨ordered.1,
        ordered.2.1.modifyLast f (fun h found => lower h (by simpa only [lastForest?] using found)),
        ordered.2.2.modifyLast f
          (fun h found good => preserves h (by simpa only [lastForest?] using found) good)
          (fun h found => lower h (by simpa only [lastForest?] using found))⟩

theorem special_spine_HW (count depth : Nat) {e stop : NumericalExpr} (ordered : HW e)
    (selected : (spine e)[depth]? = some stop) {a : List Nat} {hs : Forests (List Nat)}
    (last : last? stop = some (a, hs)) {h : NumericalExpr}
    (child : lastForest? hs = some h) (nonempty : h ≠ .nil) : HW (special count depth e) := by
  induction depth generalizing e with
  | zero =>
    have same : e = stop := by simpa only [spine, List.getElem?_cons_zero, Option.some.injEq] using selected
    subst e
    apply ordered.modifyLast
    intro b ks atLast good
    have equal : (b, ks) = (a, hs) := Option.some.inj (atLast.symm.trans last)
    cases equal
    simpa only [child, Option.getD_some] using pruneRepeat_HW good child count
  | succ depth ih =>
    rw [spine_get_succ] at selected
    obtain ⟨next, childNext, below⟩ := Option.bind_eq_some_iff.mp selected
    obtain ⟨⟨b, ks⟩, atLast, forest⟩ := Option.bind_eq_some_iff.mp childNext
    apply ordered.modifyLast
    intro c js found good
    have same : (c, js) = (b, ks) := Option.some.inj (found.symm.trans atLast)
    cases same
    apply good.modifyLast (special count depth)
    · intro x selectedX xGood
      have same : x = next := Option.some.inj (selectedX.symm.trans forest)
      subst x
      exact ih xGood below
    · intro x selectedX
      have same : x = next := Option.some.inj (selectedX.symm.trans forest)
      subst x
      exact .of_lt (special_spine_lt count depth below last child nonempty)

end BTnSSBMS.Source
