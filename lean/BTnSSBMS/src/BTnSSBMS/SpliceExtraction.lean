import BTnSSBMS.CopySplice

/-! Recover the entering legality and owner fence of a replacement from
the legality of the actual spliced result. This inverse direction lets
copy-run theorems use their already-proved complete legality rather than
postulate a new hole invariant. -/
namespace BTnSSBMS.Source

mutual
  theorem splice_replacement_finiteLegal {d : Nat} {context : ParentContext} {owner : Option Nat}
      (depth : Nat) (e replacement : NumericalExpr) {site : HoleSite}
      (found : holeSite d context owner depth e = some site)
      (legal : FiniteLegal d context (splice depth replacement e))
      (above : FitsOwner owner (splice depth replacement e)) :
      FiniteLegal d site.context replacement ∧ FitsOwner site.owner replacement := by
    cases e with
    | nil => simp only [holeSite] at found; cases found
    | cons a hs rest =>
      cases rest with
      | nil =>
        cases depth with
        | zero =>
          have same : site = ⟨context, owner, a, hs⟩ := by
            simpa only [holeSite, Option.some.injEq] using found.symm
          subst site
          simpa only [splice] using And.intro legal above
        | succ depth =>
          rw [holeSite] at found
          simp only [splice, FiniteLegal] at legal
          exact spliceForests_replacement_finiteLegal depth hs replacement found legal.2.2.2.1
      | cons b ks tail =>
        rw [holeSite] at found
        simp only [splice, FiniteLegal] at legal
        have tailAbove : FitsOwner owner (splice depth replacement (.cons b ks tail)) := by
          have shaped : FitsOwner owner (.cons a hs (splice depth replacement (.cons b ks tail))) := by
            simpa only [splice] using above
          exact shaped.tail
        exact splice_replacement_finiteLegal depth (.cons b ks tail) replacement found legal.2.2.2.2 tailAbove

  theorem spliceForests_replacement_finiteLegal {d : Nat} {context : ParentContext} {owner : Nat}
      (depth : Nat) (hs : Forests (List Nat)) (replacement : NumericalExpr) {site : HoleSite}
      (found : holeSiteForests d context owner depth hs = some site)
      (legal : FiniteLegalForests d context owner (spliceForests depth replacement hs)) :
      FiniteLegal d site.context replacement ∧ FitsOwner site.owner replacement := by
    cases hs with
    | nil => simp only [holeSiteForests] at found; cases found
    | cons h rest =>
      cases rest with
      | nil =>
        rw [holeSiteForests] at found
        simp only [spliceForests, FiniteLegalForests] at legal
        apply splice_replacement_finiteLegal depth h replacement found legal.2.1
        intro bound same col member
        have equal : owner = bound := Option.some.inj same
        subst bound
        exact legal.1 col member
      | cons k ks =>
        rw [holeSiteForests] at found
        simp only [spliceForests, FiniteLegalForests] at legal
        exact spliceForests_replacement_finiteLegal depth (.cons k ks) replacement found legal.2.2
end

end BTnSSBMS.Source
