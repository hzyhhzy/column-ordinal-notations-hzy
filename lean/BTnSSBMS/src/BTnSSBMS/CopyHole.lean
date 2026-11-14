import BTnSSBMS.CopySplice

/-!
Locating the terminal hole through the real copied template. This carries
the scoped numerical view all the way to the computed hole context; it
does not postulate a view at the place where the next replica is inserted.
-/
namespace BTnSSBMS.Source

theorem copied_nil_iff (d root cap : Nat) (delta : List Nat) (phase : Nat)
    (context : ParentContext) (history : List Nat) (e : NumericalExpr) :
    copied d root cap delta phase context history e = .nil ↔ e = .nil := by
  cases e with
  | nil => rfl
  | cons a hs t =>
    simp only [copied, Parents.annotate, mark, Expr.map]
    constructor <;> intro impossible <;> cases impossible

theorem copiedForests_nil_iff (d root cap : Nat) (delta : List Nat) (phase : Nat)
    (context : ParentContext) (history : List Nat) (hs : Forests (List Nat)) :
    copiedForests d root cap delta phase context history hs = .nil ↔ hs = .nil := by
  cases hs with
  | nil => rfl
  | cons h t =>
    rw [copiedForests_cons]
    constructor <;> intro impossible <;> cases impossible

theorem holeSite_cons_tail (d : Nat) (context : ParentContext) (owner : Option Nat)
    (depth : Nat) (a : List Nat) (hs : Forests (List Nat)) (t : NumericalExpr) (nonempty : t ≠ .nil) :
    holeSite d context owner depth (.cons a hs t) =
      holeSite d (context ++ [Parents.label d context a]) owner depth t := by
  cases t with
  | nil => exact False.elim (nonempty rfl)
  | cons b ks u => rw [holeSite]

theorem holeSiteForests_cons_tail (d : Nat) (context : ParentContext) (owner depth : Nat)
    (h : NumericalExpr) (hs : Forests (List Nat)) (nonempty : hs ≠ .nil) :
    holeSiteForests d context owner depth (.cons h hs) = holeSiteForests d context owner depth hs := by
  cases hs with
  | nil => exact False.elim (nonempty rfl)
  | cons k ks => rw [holeSiteForests]

mutual
  theorem holeSite_extends (d : Nat) (context : ParentContext) (owner : Option Nat)
      (depth : Nat) (e : NumericalExpr) {site : HoleSite}
      (found : holeSite d context owner depth e = some site) : context <+: site.context := by
    cases e with
    | nil => simp [holeSite] at found
    | cons a hs t =>
      cases t with
      | nil =>
        cases depth with
        | zero =>
          have same : site = ⟨context, owner, a, hs⟩ := by simpa only [holeSite, Option.some.injEq] using found.symm
          subst site
          exact List.prefix_refl _
        | succ k =>
          rw [holeSite] at found
          exact (List.prefix_append context [Parents.label d context a]).trans
            (holeSiteForests_extends d _ _ k hs found)
      | cons b ks u =>
        rw [holeSite] at found
        exact (List.prefix_append context [Parents.label d context a]).trans
          (holeSite_extends d _ owner depth (.cons b ks u) found)
  theorem holeSiteForests_extends (d : Nat) (context : ParentContext) (owner depth : Nat)
      (hs : Forests (List Nat)) {site : HoleSite}
      (found : holeSiteForests d context owner depth hs = some site) : context <+: site.context := by
    cases hs with
    | nil => simp [holeSiteForests] at found
    | cons h rest =>
      cases rest with
      | nil =>
        rw [holeSiteForests] at found
        exact holeSite_extends d context (some owner) depth h found
      | cons k ks =>
        rw [holeSiteForests] at found
        exact holeSiteForests_extends d context owner depth (.cons k ks) found
end

def ShiftedHole (d root cap : Nat) (delta : List Nat) (phase : Nat)
    (source target : HoleSite) : Prop :=
  ∃ visible history,
    ShiftView d source.context target.context visible history root cap delta phase ∧
    let label := Parents.label d source.context source.terminal
    let threshold := Keys.threshold cap root history label
    target.terminal = shift source.terminal threshold delta phase ∧
    target.attached = copiedForests d root cap delta phase (source.context ++ [label])
      (history ++ [threshold]) source.attached

mutual
  theorem copied_holeSite {d : Nat} {source target : ParentContext} {visible history : List Nat}
      {root cap : Nat} {delta : List Nat} {phase : Nat}
      (scope : ShiftView d source target visible history root cap delta phase)
      (sourceOwner targetOwner : Option Nat) (depth : Nat) (e : NumericalExpr)
      (legal : FiniteLegal d source e) {site : HoleSite}
      (found : holeSite d source sourceOwner depth e = some site) :
      ∃ targetSite, holeSite d target targetOwner depth (copied d root cap delta phase source history e) = some targetSite ∧
        ShiftedHole d root cap delta phase site targetSite := by
    cases e with
    | nil => simp [holeSite] at found
    | cons a hs rest =>
      have next := scope.append a legal.1 legal.2.1
      let label := Parents.label d source a
      let threshold := Keys.threshold cap root history label
      let head := shift a threshold delta phase
      have after : root < history.length := by rw [scope.historyLength]; exact scope.afterRoot
      rw [copied_cons d root cap delta phase source history after]
      cases rest with
      | nil =>
        change ∃ targetSite, holeSite d target targetOwner depth
          (.cons head (copiedForests d root cap delta phase (source ++ [label]) (history ++ [threshold]) hs) .nil) =
            some targetSite ∧ ShiftedHole d root cap delta phase site targetSite
        cases depth with
        | zero =>
          have same : site = ⟨source, sourceOwner, a, hs⟩ := by simpa only [holeSite, Option.some.injEq] using found.symm
          subst site
          refine ⟨⟨target, targetOwner, head,
            copiedForests d root cap delta phase (source ++ [label]) (history ++ [threshold]) hs⟩, ?_, ?_⟩
          · rw [holeSite]
          · exact ⟨visible, history, scope, rfl, rfl⟩
        | succ k =>
          rw [holeSite] at found ⊢
          exact copiedForests_holeSite next (a[0]?.getD 0) (head[0]?.getD 0) k hs legal.2.2.2.1 found
      | cons b ks t =>
        rw [holeSite] at found
        have nonempty : copied d root cap delta phase (source ++ [label]) (history ++ [threshold]) (.cons b ks t) ≠ .nil := by
          intro impossible
          have empty := (copied_nil_iff ..).mp impossible
          cases empty
        rw [holeSite_cons_tail d target targetOwner depth _ _ _ nonempty]
        exact copied_holeSite next sourceOwner targetOwner depth (.cons b ks t) legal.2.2.2.2 found
  theorem copiedForests_holeSite {d : Nat} {source target : ParentContext} {visible history : List Nat}
      {root cap : Nat} {delta : List Nat} {phase : Nat}
      (scope : ShiftView d source target visible history root cap delta phase)
      (sourceOwner targetOwner depth : Nat) (hs : Forests (List Nat))
      (legal : FiniteLegalForests d source sourceOwner hs) {site : HoleSite}
      (found : holeSiteForests d source sourceOwner depth hs = some site) :
      ∃ targetSite, holeSiteForests d target targetOwner depth
        (copiedForests d root cap delta phase source history hs) = some targetSite ∧
        ShiftedHole d root cap delta phase site targetSite := by
    cases hs with
    | nil => simp [holeSiteForests] at found
    | cons h rest =>
      rw [copiedForests_cons]
      cases rest with
      | nil =>
        change ∃ targetSite, holeSiteForests d target targetOwner depth
          (.cons (copied d root cap delta phase source history h) .nil) = some targetSite ∧
            ShiftedHole d root cap delta phase site targetSite
        rw [holeSiteForests] at found ⊢
        exact copied_holeSite scope (some sourceOwner) (some targetOwner) depth h legal.2.1 found
      | cons k ks =>
        rw [holeSiteForests] at found
        have nonempty : copiedForests d root cap delta phase source history (.cons k ks) ≠ .nil := by
          intro impossible
          have empty := (copiedForests_nil_iff ..).mp impossible
          cases empty
        rw [holeSiteForests_cons_tail d target targetOwner depth _ _ nonempty]
        exact copiedForests_holeSite scope sourceOwner targetOwner depth (.cons k ks) legal.2.2 found
end

end BTnSSBMS.Source
