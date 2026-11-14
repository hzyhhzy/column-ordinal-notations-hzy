import BTnSSBMS.BNSplice
import BTnSSBMS.HWHighCopies

/-! BN of the actual terminal attachment, its previous-phase donation,
and a change to a root with no later zero-parent sibling. -/
namespace BTnSSBMS.Source

mutual
  theorem BN.holeSite {d : Nat} {context : ParentContext} {owner : Option Nat}
      (depth : Nat) (e : NumericalExpr) (ordered : BN d context e) {site : HoleSite}
      (found : Source.holeSite d context owner depth e = some site) :
      BNForests d (site.context ++ [Parents.label d site.context site.terminal]) site.attached := by
    cases e with
    | nil => simp [Source.holeSite] at found
    | cons a hs rest =>
      cases rest with
      | nil =>
        cases depth with
        | zero =>
          have same : site = ⟨context, owner, a, hs⟩ := by
            simpa only [Source.holeSite, Option.some.injEq] using found.symm
          subst site
          exact ordered.2.1
        | succ depth =>
          rw [Source.holeSite] at found
          exact ordered.2.1.holeSite depth hs found
      | cons b ks t =>
        rw [Source.holeSite] at found
        exact ordered.2.2.holeSite depth (.cons b ks t) found
  theorem BNForests.holeSite {d : Nat} {context : ParentContext} {owner : Nat}
      (depth : Nat) (hs : Forests (List Nat)) (ordered : BNForests d context hs) {site : HoleSite}
      (found : Source.holeSiteForests d context owner depth hs = some site) :
      BNForests d (site.context ++ [Parents.label d site.context site.terminal]) site.attached := by
    cases hs with
    | nil => simp [Source.holeSiteForests] at found
    | cons h rest =>
      cases rest with
      | nil =>
        rw [Source.holeSiteForests] at found
        exact ordered.1.holeSite depth h found
      | cons k ks =>
        rw [Source.holeSiteForests] at found
        exact ordered.2.holeSite depth (.cons k ks) found
end

theorem ShiftView.donationAt_BN {d root : Nat} {site : HoleSite} {target : ParentContext}
    {visible history : List Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d site.context target visible history root d delta phase)
    (positive : 0 < d)
    (legal : FiniteLegal d site.context (.cons site.terminal site.attached .nil))
    (ordered : BNForests d (site.context ++ [Parents.label d site.context site.terminal]) site.attached)
    (threshold : Keys.threshold d root history (Parents.label d site.context site.terminal) = d) :
    BNForests d (target ++ [Parents.label d target (shift site.terminal d delta phase)])
      (ascendForests (donationAt d root site) .nil none delta phase) := by
  rw [donationAt_shift scope.sourceCoherent scope.sourceValid scope.historyCorrect scope.historyLength]
  have next := scope.append site.terminal legal.1 legal.2.1
  rw [threshold] at next
  exact copiedForests_BN next positive (site.terminal[0]?.getD 0) _ legal.2.2.2.1.dropLast ordered.dropLast

theorem BN.setFirstForests_above {d : Nat} {context : ParentContext} {a : List Nat}
    {hs : Forests (List Nat)} {rest : NumericalExpr}
    (ordered : BN d context (.cons a hs rest)) (positive : 0 < d)
    (legal : FiniteLegal d context (.cons a hs rest))
    (above : ∀ col ∈ labels rest, a[0]?.getD 0 < col[0]?.getD 0)
    (donated : Forests (List Nat))
    (good : BNForests d (context ++ [Parents.label d context a]) donated) :
    BN d context (setFirstForests donated (.cons a hs rest)) := by
  rw [setFirstForests]
  refine ⟨?_, good, ordered.2.2⟩
  intro index b ks tail selected same
  have laterLegal := legal.2.2.2.2.drop index
  rw [selected] at laterLegal
  have initial := (List.prefix_append context [Parents.label d context a]).trans (dropContext_prefix d _ index rest)
  have equal := same_zero_parent_value positive initial a b legal.2.1 laterLegal.2.1 same
  have strict := above b (List.mem_of_getElem? (labels_drop_head index rest selected))
  omega

end BTnSSBMS.Source
