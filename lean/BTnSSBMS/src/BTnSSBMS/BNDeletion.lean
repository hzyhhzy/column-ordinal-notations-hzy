import BTnSSBMS.SourceBN

/-! Genuine complete-block BN preservation under terminal deletion.
For each surviving sibling comparison, the old left block already
closed before that sibling, while the right block only decreases. -/
namespace BTnSSBMS.Source

theorem BN.dropLast {d : Nat} {context : ParentContext} {e : NumericalExpr}
    (ordered : BN d context e) (positive : 0 < d) (legal : FiniteLegal d context e) :
    BN d context (Source.dropLast e) := by
  cases e with
  | nil => rw [Source.dropLast]; trivial
  | cons a hs rest =>
    cases rest with
    | nil => rw [Source.dropLast]; trivial
    | cons c js more =>
      rw [Source.dropLast]
      refine ⟨?_, ordered.2.1, ordered.2.2.dropLast positive legal.2.2.2.2⟩
      intro index b ks tail shape same
      rw [drop_dropLast] at shape
      obtain ⟨after, original, pruned, nonempty⟩ := dropLast_cons_inv shape
      have inside := drop_shape_inside original
      rw [dropContext_dropLast d _ index (.cons c js more) inside] at same
      have prior := ordered.1 index b ks after original same
      have laterLegal := legal.2.2.2.2.drop index
      rw [original] at laterLegal
      have sharedValue := same_zero_parent_value positive
        ((List.prefix_append context _).trans (dropContext_prefix d _ index (.cons c js more)))
        a b legal.2.1 laterLegal.2.1 same
      have unchanged := rootBlock_dropLast_of_sibling (a := a) (hs := hs) index original nonempty sharedValue
      simp only [Source.dropLast] at unchanged
      rw [unchanged]
      have decreased := rootBlock_dropLast_le (.cons b ks after)
      have deletion : Source.dropLast (.cons b ks after) = .cons b ks tail := by
        cases after with
        | nil => exact False.elim (nonempty rfl)
        | cons x ys remaining => rw [Source.dropLast, pruned]
      rw [deletion] at decreased
      exact decreased.trans prior

end BTnSSBMS.Source
