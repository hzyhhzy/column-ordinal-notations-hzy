import BTnSSBMS.RootedRelocation

/-! Complete SB rebasing after an actual terminal-hole replacement. The
replacement may contain arbitrarily many further copies and nested forests.
Its transport uses the computed hole context, not the root entry. Legality
and the owner's fence are explicit finite requirements; no comparison of
the replacement with a later block is asserted here. -/
namespace BTnSSBMS.Source

theorem rebaseBlock_splice_at_hole {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    (unit : Parents.UnitSteps d context) (position : List Nat)
    (positionUnit : Parents.UnitSteps d (context ++ [Parents.label d context position]))
    {cut root : Nat} (positive : 0 < cut) (room : cut < d) (inside : root < context.length)
    (path : Parents.Ancestor (context ++ [Parents.label d context position]) (cut - 1) root context.length)
    (same : (Parents.label d context position).parents[cut]?.join = Parents.parent context cut root)
    (hs : Forests (List Nat)) (rest : NumericalExpr)
    (legal : FiniteLegal d (context.take root)
      (.cons (context[root]?.getD default).coordinates hs rest))
    (depth : Nat) {site : HoleSite}
    (found : holeSite d (context.take root) none depth
      (.cons (context[root]?.getD default).coordinates hs rest) = some site)
    (later : root < site.context.length) :
    ∃ targetSite moved,
      holeSite d context none depth
        (partialMaterial d context root cut position hs rest) = some targetSite ∧
      (List.range root ++ [context.length]) <+: moved ∧
      Parents.Coherent d site.context ∧ Parents.ContextValid site.context ∧
      Parents.Coherent d targetSite.context ∧ Parents.ContextValid targetSite.context ∧
      Parents.NumericalView d site.context targetSite.context moved ∧
      ∀ replacement, FiniteLegal d site.context replacement → FitsOwner site.owner replacement →
        rebaseBlock d cut context root position
          (splice depth replacement (.cons (context[root]?.getD default).coordinates hs rest)) =
        rootBlock (splice depth (relocate d site.context targetSite.context moved replacement)
          (partialMaterial d context root cut position hs rest)) := by
  have divided := coherent.take_succ_label inside
  have sourceLength : (context.take root).length = root := by simp only [List.length_take]; omega
  have scope := partial_rebase_shiftView coherent valid unit position positionUnit
    positive room inside path same legal.1
  have description : rootedRelocate d (context.take root) context
      (List.range root ++ [context.length]) (partialHead context root cut position)
      (.cons (context[root]?.getD default).coordinates hs rest) =
      partialMaterial d context root cut position hs rest := by
    simp only [rootedRelocate, partialMaterial, ← divided]
  obtain ⟨targetSite, moved, targetFound, extended, sc, sv, tc, tv, view, equation⟩ :=
    rootedRelocate_splice_at_hole (source := context.take root) (target := context)
      (a := (context[root]?.getD default).coordinates)
      (visible := List.range root ++ [context.length]) (head := partialHead context root cut position)
      (by rw [← divided]; exact scope.sourceCoherent)
      (by rw [← divided]; exact scope.sourceValid)
      scope.targetCoherent scope.targetValid (by rw [← divided]; exact scope.view)
      hs rest depth found (by rw [sourceLength]; exact later)
  rw [description] at targetFound equation
  refine ⟨targetSite, moved, targetFound, extended, sc, sv, tc, tv, view, ?_⟩
  intro replacement replacementLegal replacementAbove
  have splicedLegal := (splice_finiteLegal depth _ replacement legal
    (by intro bound impossible; cases impossible) found replacementLegal replacementAbove).1
  obtain ⟨forests, tail, shape⟩ := splice_after_head_shape found
    (by rw [sourceLength]; exact later) replacement
  have rebased := rebaseBlock_eq_rootedRelocate coherent valid unit position positionUnit
    positive room inside path same forests tail (by rw [← shape]; exact splicedLegal)
  rw [← shape] at rebased
  exact rebased.trans (congrArg rootBlock (equation replacement))

end BTnSSBMS.Source
