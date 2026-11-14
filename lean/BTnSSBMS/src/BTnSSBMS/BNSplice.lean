import BTnSSBMS.BNSpliceZero
import BTnSSBMS.BNSpecial

/-! The positive-class BN splice at arbitrary forest depth. The
replacement is checked only at the actual, computed hole context. -/
namespace BTnSSBMS.Source

theorem BN.last_context {d : Nat} {context : ParentContext} {e : NumericalExpr}
    (ordered : BN d context e) {a : List Nat} {hs : Forests (List Nat)}
    (last : last? e = some (a, hs)) :
    BN d (outerContext d context (Source.dropLast e)) (.cons a hs .nil) := by
  have result := ordered.drop (length e - 1)
  rw [drop_last_singleton e last, dropContext_last] at result
  exact result

theorem BN.modifyLastForests_at {d : Nat} {context : ParentContext} {e : NumericalExpr}
    (ordered : BN d context e) (positive : 0 < d) (legal : FiniteLegal d context e)
    (f : List Nat → Forests (List Nat) → Forests (List Nat))
    (good : ∀ a hs, last? e = some (a, hs) → BNForests d (outerContext d context e) (f a hs))
    (lower : ∀ a hs, last? e = some (a, hs) → (f a hs).compare (listCompare Ord.compare) hs ≠ .gt) :
    BN d context (modifyLast (fun x => (x.1, f x.1 x.2)) e) := by
  cases e with
  | nil => rw [modifyLast]; trivial
  | cons a hs rest =>
    cases rest with
    | nil =>
      rw [modifyLast]
      exact BN.singleton a (by simpa only [outerContext] using good a hs (by rw [last?]))
    | cons c js more =>
      rw [modifyLast]
      refine ⟨?_, ordered.2.1, ordered.2.2.modifyLastForests_at positive legal.2.2.2.2 f
        (fun b ks found => by simpa only [outerContext] using good b ks (by simpa only [last?] using found))
        (fun b ks found => lower b ks (by simpa only [last?] using found))⟩
      intro index b ks tail shape same
      rw [drop_modifyLast_forests] at shape
      obtain ⟨oldForests, after, original⟩ := modifyLast_forests_cons_inv f shape
      rw [dropContext_modifyLast_forests] at same
      have prior := ordered.1 index b oldForests after original same
      have laterLegal := legal.2.2.2.2.drop index
      rw [original] at laterLegal
      have sharedValue := same_zero_parent_value positive
        ((List.prefix_append context _).trans (dropContext_prefix d _ index (.cons c js more)))
        a b legal.2.1 laterLegal.2.1 same
      have unchanged := rootBlock_modifyLast_of_sibling f (a := a) (hs := hs) index original sharedValue
      simp only [modifyLast] at unchanged
      rw [unchanged]
      have decrease := rootBlock_mono (modifyLast_forests_le f (Source.drop index (.cons c js more)) (by
        intro v forests found
        exact lower v forests (by simpa only [last?] using last_of_drop index (.cons c js more) found)))
      rw [shape, original] at decrease
      exact decrease.trans prior

theorem splice_succ_modifyLast (depth : Nat) (replacement e : Expr α) :
    splice (depth + 1) replacement e = modifyLast (fun x => (x.1, spliceForests depth replacement x.2)) e := by
  cases e with
  | nil => simp only [splice, modifyLast]
  | cons a hs rest =>
    cases rest with
    | nil => simp only [splice, modifyLast]
    | cons b ks tail =>
      simp only [splice, modifyLast, splice_succ_modifyLast depth replacement (.cons b ks tail)]

theorem spliceForests_modifyLast (depth : Nat) (replacement : Expr α) (hs : Forests α) :
    spliceForests depth replacement hs = modifyLastForest (splice depth replacement) hs := by
  cases hs with
  | nil => simp only [spliceForests, modifyLastForest]
  | cons h rest =>
    cases rest with
    | nil => simp only [spliceForests, modifyLastForest]
    | cons k ks =>
      simp only [spliceForests, modifyLastForest, spliceForests_modifyLast depth replacement (.cons k ks)]

theorem splice_BN {d : Nat} {context : ParentContext} {owner : Option Nat}
    (depth : Nat) (e replacement : NumericalExpr) (ordered : BN d context e)
    (positive : 0 < d) (legal : FiniteLegal d context e) {site : HoleSite}
    (found : holeSite d context owner depth e = some site)
    (good : BN d site.context replacement) (finite : FiniteLegal d site.context replacement)
    (lower : replacement.compare (listCompare Ord.compare) (.cons site.terminal site.attached .nil) = .lt)
    (floor : TerminalFloor site.terminal replacement) : BN d context (splice depth replacement e) := by
  induction depth generalizing context owner e site with
  | zero =>
    cases last : last? e with
    | none =>
      have empty := (last_none_iff e).mp last
      rw [empty, holeSite] at found
      contradiction
    | some column =>
      obtain ⟨a, hs⟩ := column
      rw [holeSite_zero_last d context owner e last] at found
      cases Option.some.inj found
      exact ordered.splice_zero positive legal last good finite (.of_lt lower) floor
  | succ depth ih =>
    rw [splice_succ_modifyLast]
    apply ordered.modifyLastForests_at positive legal (fun _ hs => spliceForests depth replacement hs)
    · intro a hs last
      have siteFound : holeSiteForests d (outerContext d context e) (a[0]?.getD 0) depth hs = some site := by
        rw [← holeSite_succ_last d context owner depth e last]
        exact found
      have old := (ordered.last_context last).2.1
      have oldLegal := (legal.last_context last).2.2.2.1
      rw [← outerContext_last context e last] at old oldLegal
      rw [spliceForests_modifyLast]
      apply old.modifyLast oldLegal (splice depth replacement)
      intro h child childLegal childBN
      rw [holeSiteForests_last d (outerContext d context e) (a[0]?.getD 0) depth hs,
        child, Option.bind_some] at siteFound
      exact ih h childBN childLegal siteFound good finite lower floor
    · intro a hs last
      have siteFound : holeSiteForests d (outerContext d context e) (a[0]?.getD 0) depth hs = some site := by
        rw [← holeSite_succ_last d context owner depth e last]
        exact found
      rw [spliceForests_lt depth hs replacement siteFound lower]
      decide

end BTnSSBMS.Source
