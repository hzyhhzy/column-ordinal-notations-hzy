import BTnSSBMS.RelocationSplice
import BTnSSBMS.RootCopyBlock

/-! A proof-side description of transport after an already installed root.
The head is specified, while every descendant is transported by the existing
canonical operation. It commutes with the actual last-hole splice, at the
computed entering context, and with complete root-block truncation. This is
not a new expansion rule or a claim of block-order preservation. -/
namespace BTnSSBMS.Source

def rootedRelocate (d : Nat) (source target : ParentContext) (visible head : List Nat) :
    NumericalExpr → NumericalExpr
  | .nil => .nil
  | .cons a hs rest =>
      .cons head
        (relocateForests d (source ++ [Parents.label d source a])
          (target ++ [Parents.label d target head]) visible hs)
        (relocate d (source ++ [Parents.label d source a])
          (target ++ [Parents.label d target head]) visible rest)

theorem splice_after_head_shape {d : Nat} {context : ParentContext} {owner : Option Nat}
    {depth : Nat} {a : List Nat} {hs : Forests (List Nat)} {rest : NumericalExpr} {site : HoleSite}
    (found : holeSite d context owner depth (.cons a hs rest) = some site)
    (later : context.length < site.context.length) (replacement : NumericalExpr) :
    ∃ forests tail, splice depth replacement (.cons a hs rest) = .cons a forests tail := by
  cases rest with
  | nil =>
    cases depth with
    | zero =>
      have same : site = ⟨context, owner, a, hs⟩ := by
        simpa only [holeSite, Option.some.injEq] using found.symm
      subst site
      exact False.elim (Nat.lt_irrefl _ later)
    | succ depth => exact ⟨spliceForests depth replacement hs, .nil, by simp only [splice]⟩
  | cons b ks tail => exact ⟨hs, splice depth replacement (.cons b ks tail), by simp only [splice]⟩

theorem rootedRelocate_rootBlock {d : Nat} {source target : ParentContext}
    {visible a head : List Nat}
    (sourceCoherent : Parents.Coherent d (source ++ [Parents.label d source a]))
    (sourceValid : Parents.ContextValid (source ++ [Parents.label d source a]))
    (targetCoherent : Parents.Coherent d (target ++ [Parents.label d target head]))
    (targetValid : Parents.ContextValid (target ++ [Parents.label d target head]))
    (view : Parents.NumericalView d (source ++ [Parents.label d source a])
      (target ++ [Parents.label d target head]) visible)
    (positive : 0 < d) (hs : Forests (List Nat)) (rest : NumericalExpr)
    (legal : FiniteLegal d source (.cons a hs rest)) :
    rootedRelocate d source target visible head (rootBlock (.cons a hs rest)) =
      rootBlock (rootedRelocate d source target visible head (.cons a hs rest)) := by
  have point : Parents.point visible source.length = target.length := by
    have last := view.frontier (by simp)
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_sub_cancel] at last
    omega
  have cutoff := relocate_takeAbove d rest _ _ visible sourceCoherent sourceValid targetCoherent
    targetValid view positive source.length (by simp)
    (by simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_sub_cancel]; exact .refl _)
    legal.2.2.2.2
  rw [Parents.reading_append_label, point, Parents.reading_append_label] at cutoff
  simpa only [rootBlock, rootedRelocate] using congrArg (Expr.cons head
    (relocateForests d (source ++ [Parents.label d source a])
      (target ++ [Parents.label d target head]) visible hs)) cutoff

theorem rootedRelocate_splice_at_hole {d : Nat} {source target : ParentContext}
    {visible a head : List Nat}
    (sourceCoherent : Parents.Coherent d (source ++ [Parents.label d source a]))
    (sourceValid : Parents.ContextValid (source ++ [Parents.label d source a]))
    (targetCoherent : Parents.Coherent d (target ++ [Parents.label d target head]))
    (targetValid : Parents.ContextValid (target ++ [Parents.label d target head]))
    (view : Parents.NumericalView d (source ++ [Parents.label d source a])
      (target ++ [Parents.label d target head]) visible)
    (hs : Forests (List Nat)) (rest : NumericalExpr) (depth : Nat) {site : HoleSite}
    (found : holeSite d source none depth (.cons a hs rest) = some site)
    (later : source.length < site.context.length) :
    ∃ targetSite moved,
      holeSite d target none depth (rootedRelocate d source target visible head (.cons a hs rest)) = some targetSite ∧
      visible <+: moved ∧
      Parents.Coherent d site.context ∧ Parents.ContextValid site.context ∧
      Parents.Coherent d targetSite.context ∧ Parents.ContextValid targetSite.context ∧
      Parents.NumericalView d site.context targetSite.context moved ∧
      ∀ replacement,
        rootedRelocate d source target visible head (splice depth replacement (.cons a hs rest)) =
          splice depth (relocate d site.context targetSite.context moved replacement)
            (rootedRelocate d source target visible head (.cons a hs rest)) := by
  cases rest with
  | nil =>
    cases depth with
    | zero =>
      have same : site = ⟨source, none, a, hs⟩ := by
        simpa only [holeSite, Option.some.injEq] using found.symm
      subst site
      exact False.elim (Nat.lt_irrefl _ later)
    | succ depth =>
      rw [holeSite] at found
      obtain ⟨targetSite, moved, targetFound, extended, sc, sv, tc, tv, holeView, equation⟩ :=
        relocateForests_splice_at_hole sourceCoherent sourceValid targetCoherent targetValid view
          (a[0]?.getD 0) (head[0]?.getD 0) depth hs found
      refine ⟨targetSite, moved, ?_, extended, sc, sv, tc, tv, holeView, ?_⟩
      · simpa only [rootedRelocate, relocate, holeSite] using targetFound
      · intro replacement
        simpa only [splice, rootedRelocate, relocate] using
          congrArg (fun forests => Expr.cons head forests .nil) (equation replacement)
  | cons b ks tail =>
    rw [holeSite] at found
    obtain ⟨targetSite, moved, targetFound, extended, sc, sv, tc, tv, holeView, equation⟩ :=
      relocate_splice_at_hole sourceCoherent sourceValid targetCoherent targetValid view
        none none depth (.cons b ks tail) found
    refine ⟨targetSite, moved, ?_, extended, sc, sv, tc, tv, holeView, ?_⟩
    · simpa only [rootedRelocate, relocate, holeSite] using targetFound
    · intro replacement
      simpa only [splice, rootedRelocate, relocate] using congrArg
        (Expr.cons head (relocateForests d (source ++ [Parents.label d source a])
          (target ++ [Parents.label d target head]) visible hs)) (equation replacement)

theorem rebaseBlock_eq_rootedRelocate {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    (unit : Parents.UnitSteps d context) (position : List Nat)
    (positionUnit : Parents.UnitSteps d (context ++ [Parents.label d context position]))
    {cut root : Nat} (positive : 0 < cut) (room : cut < d) (inside : root < context.length)
    (path : Parents.Ancestor (context ++ [Parents.label d context position]) (cut - 1) root context.length)
    (same : (Parents.label d context position).parents[cut]?.join = Parents.parent context cut root)
    (hs : Forests (List Nat)) (rest : NumericalExpr)
    (legal : FiniteLegal d (context.take root)
      (.cons (context[root]?.getD default).coordinates hs rest)) :
    rebaseBlock d cut context root position (.cons (context[root]?.getD default).coordinates hs rest) =
      rootBlock (rootedRelocate d (context.take root) context
        (List.range root ++ [context.length]) (partialHead context root cut position)
        (.cons (context[root]?.getD default).coordinates hs rest)) := by
  have divided := coherent.take_succ_label inside
  have scope := partial_rebase_shiftView coherent valid unit position positionUnit
    positive room inside path same legal.1
  have cutoff := rootedRelocate_rootBlock (a := (context[root]?.getD default).coordinates)
    (source := context.take root) (target := context)
    (visible := List.range root ++ [context.length]) (head := partialHead context root cut position)
    (by rw [← divided]; exact scope.sourceCoherent)
    (by rw [← divided]; exact scope.sourceValid)
    scope.targetCoherent scope.targetValid (by rw [← divided]; exact scope.view)
    (by omega) hs rest legal
  have material := partialMaterial_eq_copied coherent valid unit position positionUnit positive room inside
    path same hs (takeAbove ((context[root]?.getD default).coordinates[0]?.getD 0) rest)
    (rootBlock_finiteLegal legal)
  rw [rebaseBlock, rootBlock, ← material]
  exact (show partialMaterial d context root cut position hs
      (takeAbove ((context[root]?.getD default).coordinates[0]?.getD 0) rest) =
      rootedRelocate d (context.take root) context (List.range root ++ [context.length])
        (partialHead context root cut position)
        (rootBlock (.cons (context[root]?.getD default).coordinates hs rest)) by
    simp only [partialMaterial, rootedRelocate, rootBlock, ← divided]).trans cutoff

end BTnSSBMS.Source
