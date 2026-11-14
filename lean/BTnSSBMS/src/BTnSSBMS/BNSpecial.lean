import BTnSSBMS.BNLastChange

/-! Complete-block BN for the actual special branch. Sibling forests
restart from the same owner context; they are never concatenated into
one numerical forest. No whole-standard-domain BN hypothesis is hidden
in the source definition. Ordinary copying is a separate obligation. -/
namespace BTnSSBMS.Source

theorem BNForests.modifyLast {d : Nat} {context : ParentContext} {owner : Nat}
    {hs : Forests (List Nat)} (ordered : BNForests d context hs)
    (legal : FiniteLegalForests d context owner hs) (f : NumericalExpr → NumericalExpr)
    (preserves : ∀ h, lastForest? hs = some h → FiniteLegal d context h →
      BN d context h → BN d context (f h)) :
    BNForests d context (modifyLastForest f hs) := by
  cases hs with
  | nil => rw [modifyLastForest]; trivial
  | cons h rest =>
    cases rest with
    | nil => rw [modifyLastForest]; exact ⟨preserves h (by rw [lastForest?]) legal.2.1 ordered.1, trivial⟩
    | cons k ks =>
      rw [modifyLastForest]
      exact ⟨ordered.1, ordered.2.modifyLast legal.2.2 f
        (fun x found finite good => preserves x (by simpa only [lastForest?] using found) finite good)⟩

theorem pruneRepeat_BN {d : Nat} {context : ParentContext} {owner : Nat}
    {hs : Forests (List Nat)} (ordered : BNForests d context hs)
    (positive : 0 < d) (legal : FiniteLegalForests d context owner hs)
    {h : NumericalExpr} (selected : lastForest? hs = some h) (count : Nat) :
    BNForests d context (appendForests (dropLastForest hs) (repeatForest (dropLast h) count)) := by
  exact ordered.dropLast.append (repeatForest_BN
    ((ordered.last selected).dropLast positive (legal.last selected).2) count)

theorem special_spine_BN (count depth : Nat) {d : Nat} {context : ParentContext}
    {e stop : NumericalExpr} (ordered : BN d context e) (positive : 0 < d)
    (legal : FiniteLegal d context e)
    (selected : (spine e)[depth]? = some stop) {a : List Nat} {hs : Forests (List Nat)}
    (last : last? stop = some (a, hs)) {h : NumericalExpr}
    (child : lastForest? hs = some h) (nonempty : h ≠ .nil) :
    BN d context (special count depth e) := by
  induction depth generalizing context e with
  | zero =>
    have same : e = stop := by simpa only [spine, List.getElem?_cons_zero, Option.some.injEq] using selected
    subst e
    rw [special]
    apply ordered.modifyLastForests positive legal
      (fun _ fs => appendForests (dropLastForest fs) (repeatForest (dropLast (lastForest? fs |>.getD .nil)) count))
    · intro ctx b ks found finite good
      have equal : (b, ks) = (a, hs) := Option.some.inj (found.symm.trans last)
      cases equal
      simpa only [child, Option.getD_some] using pruneRepeat_BN good positive finite.2.2.2.1 child count
    · intro b ks found
      have equal : (b, ks) = (a, hs) := Option.some.inj (found.symm.trans last)
      cases equal
      simp only [child, Option.getD_some, replicate_pruned_last_lt hs child nonempty count]
      decide
  | succ depth ih =>
    rw [spine_get_succ] at selected
    obtain ⟨next, childNext, below⟩ := Option.bind_eq_some_iff.mp selected
    obtain ⟨⟨b, ks⟩, atLast, forest⟩ := Option.bind_eq_some_iff.mp childNext
    rw [special]
    apply ordered.modifyLastForests positive legal (fun _ fs => modifyLastForest (special count depth) fs)
    · intro ctx c js found finite good
      have same : (c, js) = (b, ks) := Option.some.inj (found.symm.trans atLast)
      cases same
      apply good.modifyLast finite.2.2.2.1 (special count depth)
      intro x selectedX xLegal xGood
      have same : x = next := Option.some.inj (selectedX.symm.trans forest)
      subst x
      exact ih xGood xLegal below
    · intro c js found
      have same : (c, js) = (b, ks) := Option.some.inj (found.symm.trans atLast)
      cases same
      have smaller := modifyLastForest_lt ks (special count depth) forest
        (special_spine_lt count depth below last child nonempty)
      rw [smaller]
      decide

theorem expand_zero_BN {d index : Nat} {context : ParentContext} {e : NumericalExpr}
    (ordered : BN d context e) (positive : 0 < d) (legal : FiniteLegal d context e)
    {c : List Nat × Forests (List Nat)} (atLast : last? e = some c) (zero : zeroColumn c = true) :
    expand? d e index = some (dropLast e) ∧ BN d context (dropLast e) :=
  ⟨by simp [expand?, atLast, zero], ordered.dropLast positive legal⟩

/-- The stopping depth is the one found by the frozen algorithm. This
does not assert BN closure for an ordinary-copying stopping column. -/
theorem expand_special_BN {d index : Nat} {context : ParentContext} {e stop : NumericalExpr}
    (ordered : BN d context e) (positive : 0 < d) (legal : FiniteLegal d context e)
    (selected : (spine e)[(spine e).findIdx stopping]? = some stop)
    {c : List Nat × Forests (List Nat)} (atStop : last? stop = some c)
    (specialCase : specialColumn c = true) :
    ∃ f, expand? d e index = some f ∧ BN d context f := by
  cases atLast : last? e with
  | none => exact ⟨.nil, by simp [expand?, atLast], trivial⟩
  | some terminal =>
    by_cases zero : zeroColumn terminal = true
    · exact ⟨dropLast e, expand_zero_BN ordered positive legal atLast zero⟩
    · obtain ⟨h, child, nonempty⟩ := specialColumn_last_nonempty specialCase
      refine ⟨special index ((spine e).findIdx stopping) e, ?_,
        special_spine_BN index _ ordered positive legal selected atStop child nonempty⟩
      simp [expand?, atLast, zero, selected, atStop, specialCase]

end BTnSSBMS.Source
