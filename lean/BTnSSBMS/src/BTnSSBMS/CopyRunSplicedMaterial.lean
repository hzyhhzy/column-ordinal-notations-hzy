import BTnSSBMS.RootCopySplice
import BTnSSBMS.SpliceExtraction
import BTnSSBMS.CopyIteration

/-! The complete historical material is now the frozen copies function,
not an unspliced template. All legality at its terminal replacement is
derived from the actual finite run. This identifies the rebased block;
it does not yet prove that the later current block is below that block. -/
namespace BTnSSBMS.Source

theorem copyHoleAfter_copies_rebaseBlock {d : Nat} {context target : ParentContext} {a : List Nat}
    {visible : List Nat} {cap : Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d (context ++ [Parents.label d context a])
      (target ++ [Parents.label d target (shift a cap delta phase)]) visible
      (List.replicate context.length 0 ++ [cap]) context.length cap delta phase)
    (hs : Forests (List Nat)) (rest : NumericalExpr)
    (legal : FiniteLegal d context (.cons a hs rest)) (depth : Nat) {site : HoleSite}
    (found : holeSite d context none depth (.cons a hs rest) = some site)
    (positive : 0 < cap) (room : cap < d)
    (selected : (Parents.label d site.context site.terminal).parents[cap]?.join = some context.length)
    (difference : ∀ row, row < cap → site.terminal[row]?.getD 0 = a[row]?.getD 0 + delta[row]?.getD 0)
    (gap : Nat) (nonzero : 0 < gap) {result : ParentContext}
    (computed : copyHoleAfter d cap delta context (.cons a hs rest) depth gap phase target = some result)
    (remaining : Nat) :
    let part := mark cap context.length (List.replicate context.length 0)
      (Parents.annotate d context (.cons a hs rest))
    ∃ oldHole newHole moved,
      holeSite d target none depth
        (copied d context.length cap delta phase context (List.replicate context.length 0)
          (.cons a hs rest)) = some oldHole ∧
      holeSite d result none depth
        (copied d context.length cap delta (phase + gap) context (List.replicate context.length 0)
          (.cons a hs rest)) = some newHole ∧
      (List.range target.length ++ [result.length]) <+: moved ∧
      Parents.NumericalView d oldHole.context newHole.context moved ∧
      rebaseBlock d cap result target.length (shift a cap delta (phase + gap))
        (copies part depth delta none (remaining + 1) phase) =
      rootBlock (splice depth
        (relocate d oldHole.context newHole.context moved (copies part depth delta none remaining (phase + 1)))
        (copied d context.length cap delta (phase + gap) context (List.replicate context.length 0)
          (.cons a hs rest))) := by
  dsimp only
  obtain ⟨oldHole, newHole, moved, oldFound, newFound, extended, view, equation⟩ :=
    copyHoleAfter_spliced_rebaseBlock scope hs rest legal depth found positive room selected difference
      gap nonzero computed
  have complete := (copies_low_finiteLegal legal found (.inl positive) room selected delta difference
    (remaining + 1) phase target visible scope).1
  rw [copies, ascendReplace_splice] at complete
  have replacement := splice_replacement_finiteLegal depth _ _ oldFound complete
    (by intro bound impossible; cases impossible)
  refine ⟨oldHole, newHole, moved, oldFound, newFound, extended, view, ?_⟩
  rw [copies, ascendReplace_splice]
  exact equation _ replacement.1 replacement.2

end BTnSSBMS.Source
