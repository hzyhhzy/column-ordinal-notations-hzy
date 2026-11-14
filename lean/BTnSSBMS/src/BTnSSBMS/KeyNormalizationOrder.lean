import BTnSSBMS.NumericalOrder
import BTnSSBMS.CopyEntry
import BTnSSBMS.KeyOrder

/-!
Complete normalized keys preserve comparison in a common source context.
The activation flag is not frozen arbitrarily: its monotonicity at the
first numerical difference follows from computed record-chain ancestry.
-/
namespace BTnSSBMS.Keys

theorem threshold_agrees_through {d : Nat} {source : ParentContext} {history : List Nat} {root : Nat}
    (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
    (correct : BMS.HistoryCorrect source root d history) (length : history.length = source.length)
    (afterRoot : root < source.length) (a b : List Nat) {j : Nat} (room : j < d)
    (same : ∀ k, k ≤ j → a[k]?.getD 0 = b[k]?.getD 0) :
    (j < threshold d root history (Parents.label d source a)) ↔
      j < threshold d root history (Parents.label d source b) := by
  have parents := Parents.label_parents_congr_through d source a b j room same
  cases edge : (Parents.label d source a).parents[j]?.join with
  | none =>
    have other := parents.symm.trans edge
    exact iff_of_false (threshold_at_missing coherent valid correct length afterRoot (Nat.le_refl d) a edge)
      (threshold_at_missing coherent valid correct length afterRoot (Nat.le_refl d) b other)
  | some p =>
    have other := parents.symm.trans edge
    exact (threshold_at_parent coherent valid correct length afterRoot (Nat.le_refl d) a edge).trans
      (threshold_at_parent coherent valid correct length afterRoot (Nat.le_refl d) b other).symm

theorem threshold_monotone_at_difference {d : Nat} {source : ParentContext} {history : List Nat} {root : Nat}
    (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
    (correct : BMS.HistoryCorrect source root d history) (length : history.length = source.length)
    (afterRoot : root < source.length) (a b : List Nat)
    (leftUnit : Parents.UnitSteps d (source ++ [Parents.label d source a]))
    (rightUnit : Parents.UnitSteps d (source ++ [Parents.label d source b]))
    {j : Nat} (room : j < d)
    (common : ∀ k, k < j → a[k]?.getD 0 = b[k]?.getD 0)
    (strict : a[j]?.getD 0 < b[j]?.getD 0)
    (active : j < threshold d root history (Parents.label d source a)) :
    j < threshold d root history (Parents.label d source b) := by
  cases left : (Parents.label d source a).parents[j]?.join with
  | none => exact False.elim ((threshold_at_missing coherent valid correct length afterRoot (Nat.le_refl d) a left) active)
  | some p =>
    cases right : (Parents.label d source b).parents[j]?.join with
    | none =>
      have zero := Parents.label_unit_value b rightUnit room
      simp only [right, Option.map_none, Option.getD_none] at zero
      omega
    | some q =>
      have pBound := Parents.label_parent_bound d source a j p left
      have qBound := Parents.label_parent_bound d source b j q right
      have path := (Parents.label_parents_strict_at_difference coherent valid a b
        leftUnit rightUnit room common strict left right).1
      have old := (threshold_at_parent coherent valid correct length afterRoot (Nat.le_refl d) a left).mp active
      have rootPath := ((correct p (by omega) j).mp old).2
      apply (threshold_at_parent coherent valid correct length afterRoot (Nat.le_refl d) b right).mpr
      exact (correct q (by omega) j).mpr ⟨room, rootPath.trans path⟩

theorem atomCompare_self (a : KeyAtom) : atomCompare a a = .eq := by
  simp [atomCompare]

theorem atomCompare_lt_of_monotone_flag (base a b : Nat) (left right : Bool)
    (strict : a < b) (flags : left = true → right = true) :
    atomCompare (atom base a left) (atom base b right) = .lt := by
  cases left <;> cases right <;> simp_all [atom, atomCompare, Int.compare_eq_lt] <;> omega

theorem normalize_reading (d t : Nat) (base a : List Nat) (j : Nat) (room : j < d) :
    (normalize d t base a)[j]?.getD (false, 0) =
      atom (base[j]?.getD 0) (a[j]?.getD 0) (decide (j < t)) := by
  simp only [normalize, List.getElem?_map, List.getElem?_range room, Option.map_some, Option.getD_some]

theorem keyVectorCompare_lt_at (a b : List KeyAtom) (j : Nat)
    (left : j < a.length) (right : j < b.length)
    (common : ∀ k, k < j → a[k]?.getD (false, 0) = b[k]?.getD (false, 0))
    (strict : atomCompare (a[j]?.getD (false, 0)) (b[j]?.getD (false, 0)) = .lt) :
    listCompare atomCompare a b = .lt := by
  induction j generalizing a b with
  | zero =>
    cases a with
    | nil => simp at left
    | cons x xs =>
      cases b with
      | nil => simp at right
      | cons y ys =>
        have smaller : atomCompare x y = .lt := by simpa only [List.getElem?_cons_zero, Option.getD_some] using strict
        simp only [listCompare, smaller]
  | succ j ih =>
    cases a with
    | nil => simp at left
    | cons x xs =>
      cases b with
      | nil => simp at right
      | cons y ys =>
        have same : x = y := by simpa using common 0 (by omega)
        subst y
        simp only [listCompare, atomCompare_self]
        apply ih xs ys (by simpa using left) (by simpa using right)
        · intro k before
          simpa only [List.getElem?_cons_succ] using common (k + 1) (by omega)
        · simpa only [List.getElem?_cons_succ] using strict

theorem normalized_label_lt {d : Nat} {source : ParentContext} {history : List Nat} {root : Nat}
    (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
    (correct : BMS.HistoryCorrect source root d history) (length : history.length = source.length)
    (afterRoot : root < source.length) (base a b : List Nat) (ha : a.length = d) (hb : b.length = d)
    (leftUnit : Parents.UnitSteps d (source ++ [Parents.label d source a]))
    (rightUnit : Parents.UnitSteps d (source ++ [Parents.label d source b]))
    (lower : listCompare Ord.compare a b = .lt) :
    listCompare atomCompare
      (normalize d (threshold d root history (Parents.label d source a)) base a)
      (normalize d (threshold d root history (Parents.label d source b)) base b) = .lt := by
  obtain ⟨j, inside, common, strict⟩ := columnCompare_lt_exists_difference a b (ha.trans hb.symm) lower
  have room : j < d := by omega
  apply keyVectorCompare_lt_at _ _ j (by rw [normalize_length]; exact room) (by rw [normalize_length]; exact room)
  · intro k before
    rw [normalize_reading d _ base a k (by omega), normalize_reading d _ base b k (by omega)]
    have flags := threshold_agrees_through coherent valid correct length afterRoot a b (by omega : k < d)
      (fun i hi => common i (by omega))
    simp only [common k before, flags]
  · rw [normalize_reading d _ base a j room, normalize_reading d _ base b j room]
    apply atomCompare_lt_of_monotone_flag _ _ _ _ _ strict
    intro active
    have on : j < threshold d root history (Parents.label d source a) := of_decide_eq_true active
    exact decide_eq_true (threshold_monotone_at_difference coherent valid correct length afterRoot
      a b leftUnit rightUnit room common strict on)

theorem normalized_label_compare {d : Nat} {source : ParentContext} {history : List Nat} {root : Nat}
    (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
    (correct : BMS.HistoryCorrect source root d history) (length : history.length = source.length)
    (afterRoot : root < source.length) (base a b : List Nat) (ha : a.length = d) (hb : b.length = d)
    (leftUnit : Parents.UnitSteps d (source ++ [Parents.label d source a]))
    (rightUnit : Parents.UnitSteps d (source ++ [Parents.label d source b])) :
    listCompare atomCompare
      (normalize d (threshold d root history (Parents.label d source a)) base a)
      (normalize d (threshold d root history (Parents.label d source b)) base b) =
      listCompare Ord.compare a b := by
  cases order : listCompare Ord.compare a b with
  | lt => exact normalized_label_lt coherent valid correct length afterRoot base a b ha hb leftUnit rightUnit order
  | eq =>
    have same : a = b := listCompare_eq_imp Ord.compare (fun _ _ h => Nat.compare_eq_eq.mp h) a b order
    subst b
    exact listCompare_self atomCompare atomCompare_self _
  | gt =>
    have opposite := listCompare_oriented Ord.compare
      (fun a b : Nat => Std.OrientedOrd.eq_swap (a := a) (b := b)) a b
    have reversed : listCompare Ord.compare b a = .lt := by
      cases reverse : listCompare Ord.compare b a <;> simp_all [Ordering.swap]
    have keyOrder := normalized_label_lt coherent valid correct length afterRoot base b a hb ha rightUnit leftUnit reversed
    rw [listCompare_oriented atomCompare atomCompare_oriented, keyOrder]
    rfl

private theorem label_coordinates (d : Nat) (source : ParentContext) (a : List Nat) :
    (Parents.label d source a).coordinates = a := rfl

mutual
  theorem forest_compare (d : Nat) (e f : NumericalExpr) (source : ParentContext)
      (root : Nat) (base : List Nat) (history : List Nat)
      (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
      (correct : BMS.HistoryCorrect source root d history) (length : history.length = source.length)
      (afterRoot : root < source.length)
      (leftLegal : Source.FiniteLegal d source e) (rightLegal : Source.FiniteLegal d source f) :
      (forest d root base history (Parents.annotate d source e)).compare (listCompare atomCompare)
        (forest d root base history (Parents.annotate d source f)) =
        e.compare (listCompare Ord.compare) f := by
    cases e with
    | nil => cases f <;> rfl
    | cons a hs tail =>
      cases f with
      | nil => rfl
      | cons b ks rest =>
        have headCompare := normalized_label_compare coherent valid correct length afterRoot
          base a b leftLegal.1 rightLegal.1 leftLegal.2.1 rightLegal.2.1
        cases order : listCompare Ord.compare a b with
        | lt => simp only [Parents.annotate, forest, Expr.compare, label_coordinates, headCompare, order]
        | gt => simp only [Parents.annotate, forest, Expr.compare, label_coordinates, headCompare, order]
        | eq =>
          have same : a = b := listCompare_eq_imp Ord.compare (fun _ _ h => Nat.compare_eq_eq.mp h) a b order
          subst b
          have nextCorrect := history_append_threshold coherent valid correct length afterRoot (Nat.le_refl d) a
          have nextLength : (history ++ [threshold d root history (Parents.label d source a)]).length =
              (source ++ [Parents.label d source a]).length := by simp only [List.length_append, List.length_cons, List.length_nil, length]
          have nextRoot : root < (source ++ [Parents.label d source a]).length := by simp only [List.length_append, List.length_cons, List.length_nil]; omega
          have attachedCompare := forests_compare d hs ks (source ++ [Parents.label d source a])
            root base (history ++ [threshold d root history (Parents.label d source a)])
            (Parents.coherent_append_label coherent a) (Parents.context_valid_append_label d source valid a)
            nextCorrect nextLength nextRoot (a[0]?.getD 0) leftLegal.2.2.2.1 rightLegal.2.2.2.1
          have tailCompare := forest_compare d tail rest (source ++ [Parents.label d source a])
            root base (history ++ [threshold d root history (Parents.label d source a)])
            (Parents.coherent_append_label coherent a) (Parents.context_valid_append_label d source valid a)
            nextCorrect nextLength nextRoot leftLegal.2.2.2.2 rightLegal.2.2.2.2
          simp only [Parents.annotate, forest, Expr.compare, label_coordinates, headCompare, order, attachedCompare, tailCompare]

  theorem forests_compare (d : Nat) (hs ks : Forests (List Nat)) (source : ParentContext)
      (root : Nat) (base : List Nat) (history : List Nat)
      (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
      (correct : BMS.HistoryCorrect source root d history) (length : history.length = source.length)
      (afterRoot : root < source.length) (owner : Nat)
      (leftLegal : Source.FiniteLegalForests d source owner hs)
      (rightLegal : Source.FiniteLegalForests d source owner ks) :
      (forests d root base history (Parents.annotateForests d source hs)).compare (listCompare atomCompare)
        (forests d root base history (Parents.annotateForests d source ks)) =
        hs.compare (listCompare Ord.compare) ks := by
    cases hs with
    | nil => cases ks <;> rfl
    | cons h hs =>
      cases ks with
      | nil => rfl
      | cons k ks =>
        have first := forest_compare d h k source root base history coherent valid correct length afterRoot
          leftLegal.2.1 rightLegal.2.1
        have rest := forests_compare d hs ks source root base history coherent valid correct length afterRoot owner
          leftLegal.2.2 rightLegal.2.2
        simp only [Parents.annotateForests, forests, Forests.compare, first, rest]
end

/-- In the actual same-owner entry, complete key comparison agrees
exactly with source attachment comparison, at arbitrary nesting depth.
Only the already-established finite source legality is needed. -/
theorem ofColumn_annotate_compare {d : Nat} {source : ParentContext}
    (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
    (a : List Nat) (hs ks : Forests (List Nat))
    (leftLegal : Source.FiniteLegalForests d (source ++ [Parents.label d source a]) (a[0]?.getD 0) hs)
    (rightLegal : Source.FiniteLegalForests d (source ++ [Parents.label d source a]) (a[0]?.getD 0) ks) :
    compare
      (ofColumn d source.length (Parents.label d source a)
        (Parents.annotateForests d (source ++ [Parents.label d source a]) hs))
      (ofColumn d source.length (Parents.label d source a)
        (Parents.annotateForests d (source ++ [Parents.label d source a]) ks)) =
      hs.compare (listCompare Ord.compare) ks := by
  exact forests_compare d hs ks (source ++ [Parents.label d source a]) source.length a
    (List.replicate source.length 0 ++ [d])
    (Parents.coherent_append_label coherent a) (Parents.context_valid_append_label d source valid a)
    (BMS.HistoryCorrect.at_root (Parents.context_valid_append_label d source valid a) source.length d)
    (by simp) (by simp) (a[0]?.getD 0) leftLegal rightLegal

end BTnSSBMS.Keys
