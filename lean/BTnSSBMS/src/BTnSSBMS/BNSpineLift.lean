import BTnSSBMS.SourceBNPositive

/-! A BN proof for the actual stopping forest lifts through all its
outer owners. The finite replacement must still decrease at the real
terminal, so attached-list comparisons are not assumed away. -/
namespace BTnSSBMS.Source

theorem splice_BN_at_layer {d : Nat} {context : ParentContext} {owner : Option Nat} {owners : List Nat}
    (depth : Nat) (e replacement : NumericalExpr) (ordered : BN d context e)
    (positive : 0 < d) (legal : FiniteLegal d context e) {layer : SpineLayer}
    (atLayer : layerAt d context owner owners depth e = some layer) {site : HoleSite}
    (found : holeSite d context owner depth e = some site)
    (good : BN d layer.context (splice 0 replacement layer.term))
    (lower : replacement.compare (listCompare Ord.compare) (.cons site.terminal site.attached .nil) = .lt) :
    BN d context (splice depth replacement e) := by
  induction depth generalizing context owner owners e site layer with
  | zero =>
    have same : layer = ⟨context, owner, owners, e⟩ := by
      simpa only [layerAt, Option.some.injEq] using atLayer.symm
    subst layer
    exact good
  | succ depth ih =>
    simp only [layerAt, Option.bind_eq_some_iff] at atLayer
    obtain ⟨⟨a, hs⟩, last, h, child, next⟩ := atLayer
    rw [← outerContext_last context e last] at next
    rw [splice_succ_modifyLast]
    apply ordered.modifyLastForests_at positive legal (fun _ forests => spliceForests depth replacement forests)
    · intro b forests atLast
      have same : (b, forests) = (a, hs) := Option.some.inj (atLast.symm.trans last)
      cases same
      have siteFound : holeSiteForests d (outerContext d context e) (a[0]?.getD 0) depth hs = some site := by
        rw [← holeSite_succ_last d context owner depth e atLast]
        exact found
      have old := (ordered.last_context atLast).2.1
      have oldLegal := (legal.last_context atLast).2.2.2.1
      rw [← outerContext_last context e atLast] at old oldLegal
      rw [spliceForests_modifyLast]
      apply old.modifyLast oldLegal (splice depth replacement)
      intro k selected childLegal childBN
      have sameChild : k = h := Option.some.inj (selected.symm.trans child)
      subst k
      rw [holeSiteForests_last d (outerContext d context e) (a[0]?.getD 0) depth hs,
        child, Option.bind_some] at siteFound
      exact ih h childBN childLegal next siteFound good lower
    · intro b forests atLast
      have siteFound : holeSiteForests d (outerContext d context e) (b[0]?.getD 0) depth forests = some site := by
        rw [← holeSite_succ_last d context owner depth e atLast]
        exact found
      rw [spliceForests_lt depth forests replacement siteFound lower]
      decide

end BTnSSBMS.Source
