import BTnSSBMS.SourceHW

/-! Hereditary forest order under a strict replacement at the actual last
hole. No order assumption is imposed on outer consecutive columns. -/
namespace BTnSSBMS.Source

theorem ForestsLE.splice {d : Nat} {context : ParentContext} {owner : Nat}
    (depth : Nat) (hs : Forests (List Nat)) (replacement bound : NumericalExpr)
    (bounded : ForestsLE hs bound) {site : HoleSite}
    (found : holeSiteForests d context owner depth hs = some site)
    (lower : replacement.compare (listCompare Ord.compare) (.cons site.terminal site.attached .nil) = .lt) :
    ForestsLE (spliceForests depth replacement hs) bound := by
  cases hs with
  | nil => simp [holeSiteForests] at found
  | cons h rest =>
    cases rest with
    | nil =>
      rw [holeSiteForests] at found
      rw [spliceForests]
      exact ⟨(ExprLE.of_lt (splice_lt depth h replacement found lower)).trans bounded.1, trivial⟩
    | cons k ks =>
      rw [holeSiteForests] at found
      rw [spliceForests]
      exact ⟨bounded.1, bounded.2.splice depth (.cons k ks) replacement bound found lower⟩

mutual
  theorem splice_HW {d : Nat} {context : ParentContext} {owner : Option Nat}
      (depth : Nat) (e replacement : NumericalExpr) (ordered : HW e)
      (replacementOrdered : HW replacement) {site : HoleSite}
      (found : holeSite d context owner depth e = some site)
      (lower : replacement.compare (listCompare Ord.compare) (.cons site.terminal site.attached .nil) = .lt) :
      HW (splice depth replacement e) := by
    cases e with
    | nil => simp [holeSite] at found
    | cons a hs rest =>
      cases rest with
      | nil =>
        cases depth with
        | zero => rw [splice]; exact replacementOrdered
        | succ depth =>
          rw [holeSite] at found
          rw [splice]
          exact ⟨spliceForests_HW depth hs replacement ordered.1 replacementOrdered found lower, trivial⟩
      | cons b ks t =>
        rw [holeSite] at found
        rw [splice]
        exact ⟨ordered.1, splice_HW depth (.cons b ks t) replacement ordered.2 replacementOrdered found lower⟩
  theorem spliceForests_HW {d : Nat} {context : ParentContext} {owner : Nat}
      (depth : Nat) (hs : Forests (List Nat)) (replacement : NumericalExpr)
      (ordered : HWForests hs) (replacementOrdered : HW replacement) {site : HoleSite}
      (found : holeSiteForests d context owner depth hs = some site)
      (lower : replacement.compare (listCompare Ord.compare) (.cons site.terminal site.attached .nil) = .lt) :
      HWForests (spliceForests depth replacement hs) := by
    cases hs with
    | nil => simp [holeSiteForests] at found
    | cons h rest =>
      cases rest with
      | nil =>
        rw [holeSiteForests] at found
        rw [spliceForests]
        exact ⟨splice_HW depth h replacement ordered.1 replacementOrdered found lower, trivial, trivial⟩
      | cons k ks =>
        rw [holeSiteForests] at found
        rw [spliceForests]
        exact ⟨ordered.1, ordered.2.1.splice depth (.cons k ks) replacement h found lower,
          spliceForests_HW depth (.cons k ks) replacement ordered.2.2 replacementOrdered found lower⟩
end

mutual
  theorem HW.holeSite {d : Nat} {context : ParentContext} {owner : Option Nat}
      (depth : Nat) (e : NumericalExpr) (ordered : HW e) {site : HoleSite}
      (found : Source.holeSite d context owner depth e = some site) : HWForests site.attached := by
    cases e with
    | nil => simp [Source.holeSite] at found
    | cons a hs rest =>
      cases rest with
      | nil =>
        cases depth with
        | zero =>
          have same : site = ⟨context, owner, a, hs⟩ := by simpa only [Source.holeSite, Option.some.injEq] using found.symm
          subst site
          exact ordered.1
        | succ depth =>
          rw [Source.holeSite] at found
          exact ordered.1.holeSite depth hs found
      | cons b ks t =>
        rw [Source.holeSite] at found
        exact ordered.2.holeSite depth (.cons b ks t) found
  theorem HWForests.holeSite {d : Nat} {context : ParentContext} {owner : Nat}
      (depth : Nat) (hs : Forests (List Nat)) (ordered : HWForests hs) {site : HoleSite}
      (found : holeSiteForests d context owner depth hs = some site) : HWForests site.attached := by
    cases hs with
    | nil => simp [holeSiteForests] at found
    | cons h rest =>
      cases rest with
      | nil =>
        rw [holeSiteForests] at found
        exact ordered.1.holeSite depth h found
      | cons k ks =>
        rw [holeSiteForests] at found
        exact ordered.2.2.holeSite depth (.cons k ks) found
end

theorem setFirstForests_HW {hs : Forests (List Nat)} {e : NumericalExpr}
    (ordered : HW e) (attached : HWForests hs) : HW (setFirstForests hs e) := by
  cases e with
  | nil => rw [setFirstForests]; trivial
  | cons a ks rest => rw [setFirstForests]; exact ⟨attached, ordered.2⟩

theorem diagonalTail_HW (d depth value : Nat) : HW (diagonalTail d depth value) := by
  induction depth generalizing value with
  | zero => simp only [diagonalTail, HW]
  | succ depth ih =>
    simp only [diagonalTail, HW, HWForests, ForestsLE]
    exact ⟨⟨ih (value + 1), trivial, trivial⟩, trivial⟩

theorem seed_HW (d depth : Nat) : HW (seed d depth) := by
  rw [seed]
  exact ⟨trivial, diagonalTail_HW d depth 1⟩

end BTnSSBMS.Source
