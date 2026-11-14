import BTnSSBMS.CopyIteration

/-!
The highest-class donated list is a fixed marked piece of the original
terminal, not a freshly evaluated list from a changed owner. Its marking
history is uniquely determined by actual source ancestry.
-/
namespace BTnSSBMS.BMS

theorem HistoryCorrect.unique {context : ParentContext} {root cap : Nat} {left right : List Nat}
    (first : HistoryCorrect context root cap left) (second : HistoryCorrect context root cap right)
    (length : left.length = right.length) : left = right := by
  apply List.ext_getElem length
  intro i inLeft inRight
  have atLeft := (first i inLeft (left[i]?.getD 0)).trans (second i inRight (left[i]?.getD 0)).symm
  have atRight := (first i inLeft (right[i]?.getD 0)).trans (second i inRight (right[i]?.getD 0)).symm
  have same : left[i]?.getD 0 = right[i]?.getD 0 := by omega
  simpa only [List.getElem?_eq_getElem inLeft, List.getElem?_eq_getElem inRight, Option.getD_some] using same

end BTnSSBMS.BMS

namespace BTnSSBMS.Source

/-- A notation for the frozen `dropLastForest` donation at a computed
terminal. The canonical history is later identified with the actual one. -/
def donationAt (d root : Nat) (site : HoleSite) : Forests (List Nat × Nat) :=
  markForests d root (BMS.thresholdPrefix site.context root d site.context.length ++ [d])
    (Parents.annotateForests d (site.context ++ [Parents.label d site.context site.terminal])
      (dropLastForest site.attached))

theorem donationAt_zero (d root : Nat) (site : HoleSite) (delta : List Nat) :
    ascendForests (donationAt d root site) .nil none delta 0 = dropLastForest site.attached := by
  rw [ascendForests_nohole_zero, donationAt, markForests_erase, Parents.annotateForests_erase]

theorem markForests_dropLast (cap root : Nat) (history : List Nat) (hs : Forests ParentLabel) :
    markForests cap root history (dropLastForest hs) = dropLastForest (markForests cap root history hs) := by
  cases hs with
  | nil => simp only [dropLastForest, markForests]
  | cons h rest =>
    cases rest with
    | nil => simp only [dropLastForest, markForests]
    | cons k ks =>
      simp only [dropLastForest, markForests, markForests_dropLast]

theorem annotateForests_dropLast (d : Nat) (context : ParentContext) (hs : Forests (List Nat)) :
    Parents.annotateForests d context (dropLastForest hs) =
      dropLastForest (Parents.annotateForests d context hs) := by
  cases hs with
  | nil => simp only [dropLastForest, Parents.annotateForests]
  | cons h rest =>
    cases rest with
    | nil => simp only [dropLastForest, Parents.annotateForests]
    | cons k ks =>
      simp only [dropLastForest, Parents.annotateForests, annotateForests_dropLast]

theorem donationAt_actual_history {d root : Nat} {site : HoleSite} {history : List Nat}
    (coherent : Parents.Coherent d site.context) (valid : Parents.ContextValid site.context)
    (correct : BMS.HistoryCorrect site.context root d history) (length : history.length = site.context.length) :
    donationAt d root site = dropLastForest
      (markForests d root (history ++ [d])
        (Parents.annotateForests d (site.context ++ [Parents.label d site.context site.terminal]) site.attached)) := by
  have canonical := BMS.thresholdPrefix_correct valid coherent root d (Nat.le_refl d) site.context.length
  have same := correct.unique canonical (length.trans (BMS.thresholdPrefix_length ..).symm)
  rw [donationAt, ← same, annotateForests_dropLast, markForests_dropLast]

theorem donationAt_shift {d root : Nat} {site : HoleSite} {history : List Nat}
    (coherent : Parents.Coherent d site.context) (valid : Parents.ContextValid site.context)
    (correct : BMS.HistoryCorrect site.context root d history) (length : history.length = site.context.length)
    (delta : List Nat) (phase : Nat) :
    ascendForests (donationAt d root site) .nil none delta phase =
      copiedForests d root d delta phase (site.context ++ [Parents.label d site.context site.terminal])
        (history ++ [d]) (dropLastForest site.attached) := by
  have canonical := BMS.thresholdPrefix_correct valid coherent root d (Nat.le_refl d) site.context.length
  have same := correct.unique canonical (length.trans (BMS.thresholdPrefix_length ..).symm)
  rw [ascendForests_nohole, donationAt, ← same]
  rfl

theorem ShiftView.donationAt_finiteLegal {d root : Nat} {site : HoleSite} {target : ParentContext}
    {visible history : List Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d site.context target visible history root d delta phase) (positive : 0 < d)
    (legal : FiniteLegal d site.context (.cons site.terminal site.attached .nil))
    (rootWidth : (site.context[root]?.getD default).coordinates.length = d)
    (path : Parents.Ancestor (site.context ++ [Parents.label d site.context site.terminal]) (d - 1) root site.context.length)
    (difference : ∀ j, j < d → site.terminal[j]?.getD 0 = Parents.reading site.context j root + delta[j]?.getD 0) :
    let nextHead := shift (site.context[root]?.getD default).coordinates d delta (phase + 1)
    FiniteLegalForests d (target ++ [Parents.label d target nextHead]) (nextHead[0]?.getD 0)
      (ascendForests (donationAt d root site) .nil none delta phase) := by
  dsimp only
  rw [donationAt_shift scope.sourceCoherent scope.sourceValid scope.historyCorrect scope.historyLength]
  exact scope.donation_finiteLegal positive site.terminal legal.1 legal.2.1 rootWidth path difference
    (dropLastForest site.attached) legal.2.2.2.1.dropLast

theorem labels_setFirstForests (hs : Forests (List Nat)) (e : NumericalExpr) :
    labels (setFirstForests hs e) = labels e := by
  cases e <;> rfl

theorem setFirstForests_finiteLegal {d : Nat} {context : ParentContext} {a : List Nat}
    {hs replacement : Forests (List Nat)} {rest : NumericalExpr}
    (legal : FiniteLegal d context (.cons a hs rest))
    (positive : ∀ j, j < d → 0 < a[j]?.getD 0)
    (donation : FiniteLegalForests d (context ++ [Parents.label d context a]) (a[0]?.getD 0) replacement) :
    FiniteLegal d context (setFirstForests replacement (.cons a hs rest)) := by
  exact ⟨legal.1, legal.2.1, fun _ => positive, donation, legal.2.2.2.2⟩

theorem splice_cons_tail (depth : Nat) (replacement : Expr α) (a : α) (hs : Forests α)
    (rest : Expr α) (nonempty : rest ≠ .nil) :
    splice depth replacement (.cons a hs rest) = .cons a hs (splice depth replacement rest) := by
  cases rest with
  | nil => exact False.elim (nonempty rfl)
  | cons b ks t => rw [splice]

end BTnSSBMS.Source
