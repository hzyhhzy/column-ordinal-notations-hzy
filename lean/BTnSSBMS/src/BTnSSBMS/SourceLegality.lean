import BTnSSBMS.FullLegality

/-!
The ordinary finite numerical legality conditions on a scoped source:
width, unit increments, positive owners, and row-zero forest separation.
These contain no target-encoding invariant. Preservation by Source.expand?
is not included in this file.
-/
namespace BTnSSBMS.Source

mutual
  def FiniteLegal (d : Nat) (context : ParentContext) : NumericalExpr → Prop
    | .nil => True
    | .cons a hs t =>
      a.length = d ∧
      Parents.UnitSteps d (context ++ [Parents.label d context a]) ∧
      (hs ≠ .nil → ∀ j, j < d → 0 < a[j]?.getD 0) ∧
      FiniteLegalForests d (context ++ [Parents.label d context a]) (a[0]?.getD 0) hs ∧
      FiniteLegal d (context ++ [Parents.label d context a]) t
  def FiniteLegalForests (d : Nat) (context : ParentContext) (owner : Nat) : Forests (List Nat) → Prop
    | .nil => True
    | .cons h hs =>
      (∀ col ∈ labels h, owner < col[0]?.getD 0) ∧
      FiniteLegal d context h ∧ FiniteLegalForests d context owner hs
end

mutual
  theorem FiniteLegal.separated {d : Nat} {context : ParentContext} {e : NumericalExpr}
      (legal : FiniteLegal d context e) : ForestSeparated e := by
    cases e with
    | nil => trivial
    | cons a hs t =>
      exact ⟨legal.2.2.2.1.separated, legal.2.2.2.2.separated⟩
  theorem FiniteLegalForests.separated {d : Nat} {context : ParentContext} {owner : Nat}
      {hs : Forests (List Nat)} (legal : FiniteLegalForests d context owner hs) : ForestsAbove owner hs := by
    cases hs with
    | nil => trivial
    | cons h hs => exact ⟨legal.1, legal.2.1.separated, legal.2.2.separated⟩
end

mutual
  theorem FiniteLegal.parented {d : Nat} {context : ParentContext} {e : NumericalExpr}
      (legal : FiniteLegal d context e) (positive : 0 < d) : ParentedAttachments d context e := by
    cases e with
    | nil => trivial
    | cons a hs t =>
      refine ⟨?_, legal.2.2.2.1.parented positive, legal.2.2.2.2.parented positive⟩
      intro nonempty
      have value : 0 < Parents.reading (context ++ [Parents.label d context a]) (d - 1) context.length := by
        rw [Parents.reading_append_label]
        exact legal.2.2.1 nonempty (d - 1) (by omega)
      obtain ⟨p, selected⟩ := legal.2.1.positive_has_parent (by omega : d - 1 < d) (by simp) value
      exact ⟨p, (Parents.append_label_parent d context a (d - 1)).symm.trans selected⟩
  theorem FiniteLegalForests.parented {d : Nat} {context : ParentContext} {owner : Nat}
      {hs : Forests (List Nat)} (legal : FiniteLegalForests d context owner hs) (positive : 0 < d) :
      ParentedForestList d context hs := by
    cases hs with
    | nil => trivial
    | cons h hs => exact ⟨legal.2.1.parented positive, legal.2.2.parented positive⟩
end

end BTnSSBMS.Source

namespace BTnSSBMS.Encoder

/-- The actual encoder maps every finitely numerically legal source to
a finitely numerically legal BMS matrix with exactly two additional rows.
No source or target block inequalities or standardness are assumed. -/
theorem finiteLegal_source_numericallyLegal (d : Nat) (e : NumericalExpr) (positive : 0 < d)
    (legal : Source.FiniteLegal d [] e) : BMS.NumericallyLegal (d + 2) (fromSource d e) :=
  source_numericallyLegal d e positive legal.separated (legal.parented positive)

end BTnSSBMS.Encoder
