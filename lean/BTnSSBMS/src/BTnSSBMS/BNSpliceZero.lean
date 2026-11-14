import BTnSSBMS.ZeroFloor

/-! BN across a genuine outer terminal replacement. The new material
starts at the old terminal's zero-value and stays at or above that floor.
This is the positive-class seam; the class-zero seam is different. -/
namespace BTnSSBMS.Source

def TerminalFloor (terminal : List Nat) : NumericalExpr → Prop
  | .nil => True
  | .cons a hs rest => a[0]?.getD 0 = terminal[0]?.getD 0 ∧
      ∀ b ∈ labels (.cons a hs rest), terminal[0]?.getD 0 ≤ b[0]?.getD 0

theorem BN.splice_zero {d : Nat} {context : ParentContext} {e replacement : NumericalExpr}
    (ordered : BN d context e) (positive : 0 < d) (legal : FiniteLegal d context e)
    {terminal : List Nat} {attached : Forests (List Nat)}
    (last : last? e = some (terminal, attached))
    (good : BN d (outerContext d context (Source.dropLast e)) replacement)
    (finite : FiniteLegal d (outerContext d context (Source.dropLast e)) replacement)
    (lower : ExprLE replacement (.cons terminal attached .nil))
    (floor : TerminalFloor terminal replacement) :
    BN d context (splice 0 replacement e) := by
  cases e with
  | nil => simp [last?] at last
  | cons a hs rest =>
    cases rest with
    | nil => simpa only [Source.dropLast, outerContext, splice] using good
    | cons c js more =>
      have lastRest : last? (.cons c js more) = some (terminal, attached) := by
        simpa only [last?] using last
      let entry := context ++ [Parents.label d context a]
      let before := outerContext d entry (Source.dropLast (.cons c js more))
      have good' : BN d before replacement := by simpa only [Source.dropLast, outerContext] using good
      have finite' : FiniteLegal d before replacement := by simpa only [Source.dropLast, outerContext] using finite
      rw [splice]
      refine ⟨?_, ordered.2.1, ordered.2.2.splice_zero positive legal.2.2.2.2 lastRest good' finite' lower floor⟩
      intro index b ks tail found same
      rcases splice_zero_drop_cases d entry (.cons c js more) replacement index found with
        ⟨after, old, nonempty, contexts, value⟩ | ⟨offset, selected, contexts⟩
      · rw [contexts] at same
        have prior := ordered.1 index b ks after old same
        have laterLegal := legal.2.2.2.2.drop index
        rw [old] at laterLegal
        have equalZero := same_zero_parent_value positive
          ((List.prefix_append context _).trans (dropContext_prefix d entry index (.cons c js more)))
          a b legal.2.1 laterLegal.2.1 same
        have unchanged := takeAbove_splice_zero_surviving replacement index (a[0]?.getD 0)
          old nonempty (Nat.le_of_eq equalZero)
        change ExprLE (rootBlock (.cons b ks tail))
          (.cons a hs (takeAbove (a[0]?.getD 0) (splice 0 replacement (.cons c js more))))
        rw [unchanged]
        have afterLast := (last_drop_of_cons index (.cons c js more) old).trans lastRest
        have decrease := rootBlock_mono (splice_zero_le (.cons b ks after) replacement afterLast lower)
        rw [← value] at decrease
        exact decrease.trans prior
      · change dropContext d entry index (splice 0 replacement (.cons c js more)) =
          dropContext d before offset replacement at contexts
        rw [contexts] at same
        cases replacement with
        | nil => cases offset <;> simp [Source.drop] at selected
        | cons first forests remaining =>
          have fenced : ∀ v ∈ labels (.cons first forests remaining),
              first[0]?.getD 0 ≤ v[0]?.getD 0 := by
            intro v member
            rw [floor.1]
            exact floor.2 v member
          have initial : context <+: before :=
            (List.prefix_append context _).trans (outerContext_prefix d entry (Source.dropLast (.cons c js more)))
          have external : ∀ p,
              (Parents.label d (dropContext d before offset (.cons first forests remaining)) b).parents[0]?.join = some p →
                p < before.length := by
            intro p hit
            rw [same] at hit
            exact Nat.lt_of_lt_of_le (Parents.label_parent_bound d context a 0 p hit) initial.length_le
          have firstParent := external_suffix_parent positive before first forests remaining offset selected fenced external
          have terminalParent : (Parents.label d before terminal).parents[0]?.join =
              (Parents.label d context a).parents[0]?.join := by
            have terminalFirst : (Parents.label d before terminal).parents[0]?.join =
                (Parents.label d before first).parents[0]?.join := by
              rw [Parents.label_zero d before terminal positive, Parents.label_zero d before first positive, floor.1]
            exact terminalFirst.trans (firstParent.symm.trans same)
          have prior := ordered.1 (length (.cons c js more) - 1) terminal attached .nil
            (drop_last_singleton (.cons c js more) lastRest) (by rw [dropContext_last]; exact terminalParent)
          have terminalLegal := legal.2.2.2.2.last_context lastRest
          have equalZero := same_zero_parent_value positive initial a terminal legal.2.1 terminalLegal.2.1 terminalParent
          have cut : takeAbove (a[0]?.getD 0) (.cons first forests remaining) = .nil := by
            rw [takeAbove, if_neg (by rw [floor.1, equalZero]; omega)]
          have unchanged := takeAbove_splice_zero_last (.cons c js more) (.cons first forests remaining)
            (a[0]?.getD 0) lastRest (Nat.le_of_eq equalZero) cut
          change ExprLE (rootBlock (.cons b ks tail))
            (.cons a hs (takeAbove (a[0]?.getD 0) (splice 0 (.cons first forests remaining) (.cons c js more))))
          rw [unchanged]
          have newBlock := good'.external_block_le positive offset selected fenced external
          have belowTerminal := newBlock.trans ((rootBlock_le (.cons first forests remaining)).trans lower)
          have terminalBlock : rootBlock (.cons terminal attached .nil) = .cons terminal attached .nil := by
            rw [rootBlock, takeAbove]
          rw [terminalBlock] at prior
          exact belowTerminal.trans prior

end BTnSSBMS.Source
