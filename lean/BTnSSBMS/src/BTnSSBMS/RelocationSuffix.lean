import BTnSSBMS.SiblingComparison

/-! Recover the actual source and target entry of every outer suffix.
The witness is computed by following the recursive relocation, rather
than assuming that differently entered blocks share a context. -/
namespace BTnSSBMS.Source

theorem relocate_drop_entry (d index : Nat) (e : NumericalExpr)
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
      drop index (relocate d source target visible e) =
        relocate d (dropContext d source index e)
          (dropContext d target index (relocate d source target visible e)) nextVisible (drop index e) := by
  induction index generalizing e source target visible with
  | zero => exact ⟨visible, List.prefix_refl _, sourceCoherent, sourceValid, targetCoherent, targetValid, targetUnit, view, rfl⟩
  | succ index ih =>
    cases e with
    | nil => exact ⟨visible, List.prefix_refl _, sourceCoherent, sourceValid, targetCoherent, targetValid, targetUnit, view, rfl⟩
    | cons a hs rest =>
      have nextView := relocation_view_append sourceCoherent sourceValid targetCoherent targetValid view a
      have nextUnit := relocationHead_unitSteps sourceCoherent sourceValid targetCoherent targetValid targetUnit view a
      obtain ⟨nextVisible, extended, restData⟩ := ih rest
        (source ++ [Parents.label d source a])
        (target ++ [Parents.label d target (relocationHead d source target visible a)]) (visible ++ [target.length])
        (Parents.coherent_append_label sourceCoherent a) (Parents.context_valid_append_label d source sourceValid a)
        (Parents.coherent_append_label targetCoherent _) (Parents.context_valid_append_label d target targetValid _)
        nextUnit nextView
      exact ⟨nextVisible, (List.prefix_append _ _).trans extended, restData⟩

end BTnSSBMS.Source
