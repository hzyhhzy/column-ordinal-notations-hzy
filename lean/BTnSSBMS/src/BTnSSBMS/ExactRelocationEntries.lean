import BTnSSBMS.ExactNumericalPosition
import BTnSSBMS.RelocationSuffix

/-! All ordinary positions introduced on an actual outer relocation
have exact transported parents in each later suffix entry. The witness
is computed by traversing the source, not assumed from NumericalView. -/
namespace BTnSSBMS.Source

theorem relocate_drop_exact_entry (d index : Nat) (e : NumericalExpr)
    (source target : ParentContext) (visible : List Nat)
    (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
    (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
    (targetUnit : Parents.UnitSteps d target) (view : Parents.NumericalView d source target visible) :
    ∃ nextVisible, visible <+: nextVisible ∧
      Parents.Coherent d (dropContext d source index e) ∧
      Parents.ContextValid (dropContext d source index e) ∧
      Parents.Coherent d (dropContext d target index (relocate d source target visible e)) ∧
      Parents.ContextValid (dropContext d target index (relocate d source target visible e)) ∧
      Parents.UnitSteps d (dropContext d target index (relocate d source target visible e)) ∧
      Parents.NumericalView d (dropContext d source index e)
        (dropContext d target index (relocate d source target visible e)) nextVisible ∧
      (∀ root, source.length ≤ root → root < (dropContext d source index e).length →
        Parents.ExactPosition d (dropContext d source index e)
          (dropContext d target index (relocate d source target visible e)) nextVisible root) ∧
      drop index (relocate d source target visible e) =
        relocate d (dropContext d source index e)
          (dropContext d target index (relocate d source target visible e)) nextVisible (drop index e) := by
  induction index generalizing e source target visible with
  | zero =>
    exact ⟨visible, List.prefix_refl _, sourceCoherent, sourceValid, targetCoherent, targetValid,
      targetUnit, view, by intro root after before; simp only [dropContext] at before; omega, rfl⟩
  | succ index ih =>
    cases e with
    | nil =>
      exact ⟨visible, List.prefix_refl _, sourceCoherent, sourceValid, targetCoherent, targetValid,
        targetUnit, view, by intro root after before; simp only [dropContext] at before; omega, rfl⟩
    | cons a hs rest =>
      have nextView := relocation_view_append sourceCoherent sourceValid targetCoherent targetValid view a
      have nextUnit := relocationHead_unitSteps sourceCoherent sourceValid targetCoherent targetValid targetUnit view a
      obtain ⟨nextVisible, extended, laterCoherent, laterValid, laterTargetCoherent, laterTargetValid,
          laterUnit, laterView, exactLater, output⟩ := ih rest
        (source ++ [Parents.label d source a])
        (target ++ [Parents.label d target (relocationHead d source target visible a)]) (visible ++ [target.length])
        (Parents.coherent_append_label sourceCoherent a) (Parents.context_valid_append_label d source sourceValid a)
        (Parents.coherent_append_label targetCoherent _) (Parents.context_valid_append_label d target targetValid _)
        nextUnit nextView
      refine ⟨nextVisible, (List.prefix_append _ _).trans extended, laterCoherent, laterValid,
        laterTargetCoherent, laterTargetValid, laterUnit, laterView, ?_, output⟩
      intro root after before
      by_cases old : root = source.length
      · subst root
        exact (Parents.exactPosition_append sourceCoherent sourceValid targetCoherent targetValid view a).extends
          nextView (Parents.context_valid_append_label d source sourceValid a) (by simp)
          (dropContext_prefix d _ index rest)
          (dropContext_prefix d _ index (relocate d (source ++ [Parents.label d source a])
            (target ++ [Parents.label d target (relocationHead d source target visible a)])
            (visible ++ [target.length]) rest)) extended
      · exact exactLater root (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) before

/-- The same actual-entry witness for the frozen activation-and-shift
copy. All newly traversed ordinary heads have exact parents; no such
claim is made for the already-entered forced copy root. -/
theorem copied_drop_exact_entry {d copyRoot cap phase : Nat}
    {source target : ParentContext} {visible history delta : List Nat}
    (scope : ShiftView d source target visible history copyRoot cap delta phase)
    (e : NumericalExpr) (legal : FiniteLegal d source e) (index : Nat) :
    ∃ nextVisible, visible <+: nextVisible ∧
      Parents.Coherent d (dropContext d source index e) ∧
      Parents.ContextValid (dropContext d source index e) ∧
      Parents.Coherent d (dropContext d target index (copied d copyRoot cap delta phase source history e)) ∧
      Parents.ContextValid (dropContext d target index (copied d copyRoot cap delta phase source history e)) ∧
      Parents.UnitSteps d (dropContext d target index (copied d copyRoot cap delta phase source history e)) ∧
      Parents.NumericalView d (dropContext d source index e)
        (dropContext d target index (copied d copyRoot cap delta phase source history e)) nextVisible ∧
      (∀ root, source.length ≤ root → root < (dropContext d source index e).length →
        Parents.ExactPosition d (dropContext d source index e)
          (dropContext d target index (copied d copyRoot cap delta phase source history e)) nextVisible root) ∧
      drop index (copied d copyRoot cap delta phase source history e) =
        relocate d (dropContext d source index e)
          (dropContext d target index (copied d copyRoot cap delta phase source history e)) nextVisible (drop index e) := by
  simpa only [relocate_eq_copied scope e legal] using
    relocate_drop_exact_entry d index e source target visible scope.sourceCoherent scope.sourceValid
      scope.targetCoherent scope.targetValid scope.targetUnit scope.view

end BTnSSBMS.Source
