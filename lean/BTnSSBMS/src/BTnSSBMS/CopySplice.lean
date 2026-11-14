import BTnSSBMS.CopyDonation

/-!
Structural last-hole splicing and its actual numerical entering context.
The splice is proved equal to the frozen ascendReplace operation after
the ordinary shifts. Legality needs the replacement only at the one
computed hole site, including its immediate owner's row-zero fence.
-/
namespace BTnSSBMS.Source

structure HoleSite where
  context : ParentContext
  owner : Option Nat
  terminal : List Nat
  attached : Forests (List Nat)

mutual
  def holeSite (d : Nat) (context : ParentContext) (owner : Option Nat)
      (depth : Nat) : NumericalExpr → Option HoleSite
    | .nil => none
    | .cons a hs .nil => match depth with
      | 0 => some ⟨context, owner, a, hs⟩
      | k + 1 => holeSiteForests d (context ++ [Parents.label d context a]) (a[0]?.getD 0) k hs
    | .cons a _ rest@(.cons ..) =>
      holeSite d (context ++ [Parents.label d context a]) owner depth rest
  def holeSiteForests (d : Nat) (context : ParentContext) (owner depth : Nat) :
      Forests (List Nat) → Option HoleSite
    | .nil => none
    | .cons h .nil => holeSite d context (some owner) depth h
    | .cons _ rest@(.cons ..) => holeSiteForests d context owner depth rest
end

mutual
  def splice (depth : Nat) (replacement : Expr α) : Expr α → Expr α
    | .nil => .nil
    | .cons a hs .nil => match depth with
      | 0 => replacement
      | k + 1 => .cons a (spliceForests k replacement hs) .nil
    | .cons a hs rest@(.cons ..) => .cons a hs (splice depth replacement rest)
  def spliceForests (depth : Nat) (replacement : Expr α) : Forests α → Forests α
    | .nil => .nil
    | .cons h .nil => .cons (splice depth replacement h) .nil
    | .cons h rest@(.cons ..) => .cons h (spliceForests depth replacement rest)
end

mutual
  theorem ascendReplace_splice (e : MarkedExpr) (replacement : NumericalExpr)
      (depth : Nat) (delta : List Nat) (phase : Nat) :
      ascendReplace e replacement (some depth) delta phase =
        splice depth replacement (e.map (fun a => shift a.1 a.2 delta phase)) := by
    cases e with
    | nil => simp only [ascendReplace, Expr.map, splice]
    | cons a hs rest =>
      cases rest with
      | nil =>
        cases depth with
        | zero => simp only [ascendReplace, BEq.rfl, Bool.and_self, if_true, Expr.map, splice]
        | succ k =>
          unfold ascendReplace
          simp only [Option.some_beq_some, show (k + 1 == 0) = false by simp, Bool.and_false, Bool.false_eq_true,
            if_false, if_true, Option.map_some, Nat.add_sub_cancel,
            ascendForests_splice, Expr.map, splice]
          rfl
      | cons b ks t =>
        unfold ascendReplace
        simp only [Bool.false_and, Bool.false_eq_true, if_false, ascendForests_nohole,
          ascendReplace_splice, Expr.map, splice]
  theorem ascendForests_splice (hs : Forests (List Nat × Nat)) (replacement : NumericalExpr)
      (depth : Nat) (delta : List Nat) (phase : Nat) :
      ascendForests hs replacement (some depth) delta phase =
        spliceForests depth replacement (hs.map (fun a => shift a.1 a.2 delta phase)) := by
    cases hs with
    | nil => simp only [ascendForests, Forests.map, spliceForests]
    | cons h rest =>
      cases rest with
      | nil =>
        unfold ascendForests
        simp only [if_true, ascendReplace_splice, Forests.map, spliceForests]
        rfl
      | cons k ks =>
        unfold ascendForests
        simp only [Bool.false_eq_true, if_false, ascendReplace_nohole, ascendForests_splice, Forests.map, spliceForests]
end

def FitsOwner (owner : Option Nat) (e : NumericalExpr) : Prop :=
  ∀ bound, owner = some bound → ∀ a ∈ labels e, bound < a[0]?.getD 0

theorem FitsOwner.head {owner : Option Nat} {a : List Nat} {hs : Forests (List Nat)} {t : NumericalExpr}
    (above : FitsOwner owner (.cons a hs t)) :
    ∀ bound, owner = some bound → bound < a[0]?.getD 0 := by
  intro bound same
  exact above bound same a (by simp [labels])

theorem FitsOwner.tail {owner : Option Nat} {a : List Nat} {hs : Forests (List Nat)} {t : NumericalExpr}
    (above : FitsOwner owner (.cons a hs t)) : FitsOwner owner t := by
  intro bound same col member
  exact above bound same col (by simp only [labels, List.mem_cons]; exact Or.inr member)

theorem FitsOwner.cons {owner : Option Nat} {a : List Nat} {hs : Forests (List Nat)} {t : NumericalExpr}
    (head : ∀ bound, owner = some bound → bound < a[0]?.getD 0)
    (tail : FitsOwner owner t) : FitsOwner owner (.cons a hs t) := by
  intro bound same col member
  simp only [labels, List.mem_cons] at member
  rcases member with rfl | later
  · exact head bound same
  · exact tail bound same col later

mutual
  theorem holeSite_finiteLegal {d : Nat} {context : ParentContext} {owner : Option Nat}
      (depth : Nat) (e : NumericalExpr) (legal : FiniteLegal d context e)
      (above : FitsOwner owner e) {site : HoleSite}
      (found : holeSite d context owner depth e = some site) :
      FiniteLegal d site.context (.cons site.terminal site.attached .nil) ∧
        FitsOwner site.owner (.cons site.terminal site.attached .nil) := by
    cases e with
    | nil => simp [holeSite] at found
    | cons a hs rest =>
      cases rest with
      | nil =>
        cases depth with
        | zero =>
          have same : site = ⟨context, owner, a, hs⟩ := by simpa only [holeSite, Option.some.injEq] using found.symm
          subst site
          exact ⟨legal, above⟩
        | succ k =>
          rw [holeSite] at found
          exact holeSiteForests_finiteLegal k hs legal.2.2.2.1 found
      | cons b ks t =>
        rw [holeSite] at found
        exact holeSite_finiteLegal depth (.cons b ks t) legal.2.2.2.2 above.tail found
  theorem holeSiteForests_finiteLegal {d : Nat} {context : ParentContext} {owner : Nat}
      (depth : Nat) (hs : Forests (List Nat)) (legal : FiniteLegalForests d context owner hs)
      {site : HoleSite} (found : holeSiteForests d context owner depth hs = some site) :
      FiniteLegal d site.context (.cons site.terminal site.attached .nil) ∧
        FitsOwner site.owner (.cons site.terminal site.attached .nil) := by
    cases hs with
    | nil => simp [holeSiteForests] at found
    | cons h rest =>
      cases rest with
      | nil =>
        rw [holeSiteForests] at found
        apply holeSite_finiteLegal (owner := some owner) depth h legal.2.1 ?_ found
        intro bound same
        have equal : owner = bound := Option.some.inj same
        subst bound
        exact legal.1
      | cons k ks =>
        rw [holeSiteForests] at found
        exact holeSiteForests_finiteLegal depth (.cons k ks) legal.2.2 found
end

mutual
  theorem splice_finiteLegal {d : Nat} {context : ParentContext} {owner : Option Nat}
      (depth : Nat) (e replacement : NumericalExpr) (legal : FiniteLegal d context e)
      (above : FitsOwner owner e) {site : HoleSite}
      (found : holeSite d context owner depth e = some site)
      (replacementLegal : FiniteLegal d site.context replacement)
      (replacementAbove : FitsOwner site.owner replacement) :
      FiniteLegal d context (splice depth replacement e) ∧ FitsOwner owner (splice depth replacement e) := by
    cases e with
    | nil => simp [holeSite] at found
    | cons a hs rest =>
      cases rest with
      | nil =>
        cases depth with
        | zero =>
          have same : site = ⟨context, owner, a, hs⟩ := by simpa only [holeSite, Option.some.injEq] using found.symm
          subst site
          rw [splice]
          exact ⟨replacementLegal, replacementAbove⟩
        | succ k =>
          rw [holeSite] at found
          rw [splice]
          have forests := spliceForests_finiteLegal k hs replacement legal.2.2.2.1 found replacementLegal replacementAbove
          refine ⟨⟨legal.1, legal.2.1, ?_, forests, trivial⟩, ?_⟩
          · intro nonempty
            have oldNonempty : hs ≠ .nil := by intro empty; subst hs; exact nonempty (by rw [spliceForests])
            exact legal.2.2.1 oldNonempty
          · apply FitsOwner.cons above.head
            intro bound same col member
            simp [labels] at member
      | cons b ks t =>
        rw [holeSite] at found
        rw [splice]
        have tail := splice_finiteLegal depth (.cons b ks t) replacement legal.2.2.2.2 above.tail
          found replacementLegal replacementAbove
        exact ⟨⟨legal.1, legal.2.1, legal.2.2.1, legal.2.2.2.1, tail.1⟩, FitsOwner.cons above.head tail.2⟩
  theorem spliceForests_finiteLegal {d : Nat} {context : ParentContext} {owner : Nat}
      (depth : Nat) (hs : Forests (List Nat)) (replacement : NumericalExpr)
      (legal : FiniteLegalForests d context owner hs) {site : HoleSite}
      (found : holeSiteForests d context owner depth hs = some site)
      (replacementLegal : FiniteLegal d site.context replacement)
      (replacementAbove : FitsOwner site.owner replacement) :
      FiniteLegalForests d context owner (spliceForests depth replacement hs) := by
    cases hs with
    | nil => simp [holeSiteForests] at found
    | cons h rest =>
      cases rest with
      | nil =>
        rw [holeSiteForests] at found
        rw [spliceForests]
        have above : FitsOwner (some owner) h := by
          intro bound same
          have equal : owner = bound := Option.some.inj same
          subst bound
          exact legal.1
        have inner := splice_finiteLegal depth h replacement legal.2.1 above found replacementLegal replacementAbove
        exact ⟨inner.2 owner rfl, inner.1, trivial⟩
      | cons k ks =>
        rw [holeSiteForests] at found
        rw [spliceForests]
        exact ⟨legal.1, legal.2.1,
          spliceForests_finiteLegal depth (.cons k ks) replacement legal.2.2 found replacementLegal replacementAbove⟩
end

/-- The concrete shifted source template can be spliced at arbitrary
depth once the replacement fits its uniquely computed hole context. -/
theorem copied_splice_finiteLegal {d : Nat} {source target : ParentContext} {visible history : List Nat}
    {root cap : Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d source target visible history root cap delta phase) (positive : 0 < d)
    (e replacement : NumericalExpr) (legal : FiniteLegal d source e) (depth : Nat)
    {site : HoleSite} (found : holeSite d target none depth (copied d root cap delta phase source history e) = some site)
    (replacementLegal : FiniteLegal d site.context replacement) (replacementAbove : FitsOwner site.owner replacement) :
    FiniteLegal d target
      (ascendReplace (mark cap root history (Parents.annotate d source e)) replacement (some depth) delta phase) := by
  rw [ascendReplace_splice]
  exact (splice_finiteLegal depth (copied d root cap delta phase source history e) replacement
    (copied_finiteLegal scope positive e legal) (by intro bound impossible; cases impossible)
    found replacementLegal replacementAbove).1

end BTnSSBMS.Source
