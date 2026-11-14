import BTnSSBMS.RelocationLegality
import BTnSSBMS.CopyHole

/-! Canonical numerical transport commutes with replacement at an actual
terminal hole. Both entering contexts and the map at that hole are
constructed by the same traversal, including nested forests. Replacement
is transported at this computed entry, never at the outer starting one. -/
namespace BTnSSBMS.Source

mutual
  theorem relocate_splice_at_hole {d : Nat} {source target : ParentContext} {visible : List Nat}
      (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
      (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
      (view : Parents.NumericalView d source target visible)
      (sourceOwner targetOwner : Option Nat) (depth : Nat) (e : NumericalExpr) {site : HoleSite}
      (found : holeSite d source sourceOwner depth e = some site) :
      ∃ targetSite moved,
        holeSite d target targetOwner depth (relocate d source target visible e) = some targetSite ∧
        visible <+: moved ∧
        Parents.Coherent d site.context ∧ Parents.ContextValid site.context ∧
        Parents.Coherent d targetSite.context ∧ Parents.ContextValid targetSite.context ∧
        Parents.NumericalView d site.context targetSite.context moved ∧
        ∀ replacement,
          relocate d source target visible (splice depth replacement e) =
            splice depth (relocate d site.context targetSite.context moved replacement)
              (relocate d source target visible e) := by
    cases e with
    | nil => simp only [holeSite] at found; cases found
    | cons a hs rest =>
      let head := relocationHead d source target visible a
      have nextView := relocation_view_append sourceCoherent sourceValid targetCoherent targetValid view a
      have nextSource := Parents.coherent_append_label sourceCoherent a
      have nextSourceValid := Parents.context_valid_append_label d source sourceValid a
      have nextTarget := Parents.coherent_append_label targetCoherent head
      have nextTargetValid := Parents.context_valid_append_label d target targetValid head
      cases rest with
      | nil =>
        cases depth with
        | zero =>
          have same : site = ⟨source, sourceOwner, a, hs⟩ := by
            simpa only [holeSite, Option.some.injEq] using found.symm
          subst site
          refine ⟨⟨target, targetOwner, head,
            relocateForests d (source ++ [Parents.label d source a])
              (target ++ [Parents.label d target head]) (visible ++ [target.length]) hs⟩,
            visible, by simp only [relocate, holeSite, head], List.prefix_refl _,
            sourceCoherent, sourceValid, targetCoherent, targetValid, view, ?_⟩
          intro replacement
          simp only [splice, relocate]
        | succ depth =>
          rw [holeSite] at found
          obtain ⟨targetSite, moved, targetFound, extended, sc, sv, tc, tv, holeView, equation⟩ :=
            relocateForests_splice_at_hole nextSource nextSourceValid nextTarget nextTargetValid nextView
              (a[0]?.getD 0) (head[0]?.getD 0) depth hs found
          refine ⟨targetSite, moved, ?_, (List.prefix_append _ _).trans extended, sc, sv, tc, tv, holeView, ?_⟩
          · simpa only [relocate, holeSite, head] using targetFound
          · intro replacement
            simpa only [splice, relocate, head] using congrArg (fun forests => Expr.cons head forests .nil)
              (equation replacement)
      | cons b ks tail =>
        rw [holeSite] at found
        obtain ⟨targetSite, moved, targetFound, extended, sc, sv, tc, tv, holeView, equation⟩ :=
          relocate_splice_at_hole nextSource nextSourceValid nextTarget nextTargetValid nextView
            sourceOwner targetOwner depth (.cons b ks tail) found
        refine ⟨targetSite, moved, ?_, (List.prefix_append _ _).trans extended, sc, sv, tc, tv, holeView, ?_⟩
        · simpa only [relocate, holeSite, head] using targetFound
        · intro replacement
          simpa only [splice, relocate, head] using congrArg
            (Expr.cons head (relocateForests d (source ++ [Parents.label d source a])
              (target ++ [Parents.label d target head]) (visible ++ [target.length]) hs)) (equation replacement)

  theorem relocateForests_splice_at_hole {d : Nat} {source target : ParentContext} {visible : List Nat}
      (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
      (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
      (view : Parents.NumericalView d source target visible)
      (sourceOwner targetOwner depth : Nat) (hs : Forests (List Nat)) {site : HoleSite}
      (found : holeSiteForests d source sourceOwner depth hs = some site) :
      ∃ targetSite moved,
        holeSiteForests d target targetOwner depth (relocateForests d source target visible hs) = some targetSite ∧
        visible <+: moved ∧
        Parents.Coherent d site.context ∧ Parents.ContextValid site.context ∧
        Parents.Coherent d targetSite.context ∧ Parents.ContextValid targetSite.context ∧
        Parents.NumericalView d site.context targetSite.context moved ∧
        ∀ replacement,
          relocateForests d source target visible (spliceForests depth replacement hs) =
            spliceForests depth (relocate d site.context targetSite.context moved replacement)
              (relocateForests d source target visible hs) := by
    cases hs with
    | nil => simp only [holeSiteForests] at found; cases found
    | cons h rest =>
      cases rest with
      | nil =>
        rw [holeSiteForests] at found
        obtain ⟨targetSite, moved, targetFound, extended, sc, sv, tc, tv, holeView, equation⟩ :=
          relocate_splice_at_hole sourceCoherent sourceValid targetCoherent targetValid view
            (some sourceOwner) (some targetOwner) depth h found
        refine ⟨targetSite, moved, ?_, extended, sc, sv, tc, tv, holeView, ?_⟩
        · simpa only [relocateForests, holeSiteForests] using targetFound
        · intro replacement
          simpa only [spliceForests, relocateForests] using congrArg (fun e => Forests.cons e .nil) (equation replacement)
      | cons k ks =>
        rw [holeSiteForests] at found
        obtain ⟨targetSite, moved, targetFound, extended, sc, sv, tc, tv, holeView, equation⟩ :=
          relocateForests_splice_at_hole sourceCoherent sourceValid targetCoherent targetValid view
            sourceOwner targetOwner depth (.cons k ks) found
        refine ⟨targetSite, moved, ?_, extended, sc, sv, tc, tv, holeView, ?_⟩
        · simpa only [relocateForests, holeSiteForests] using targetFound
        · intro replacement
          simpa only [spliceForests, relocateForests] using congrArg
            (Forests.cons (relocate d source target visible h)) (equation replacement)
end

end BTnSSBMS.Source
