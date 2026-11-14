import BTnSSBMS.BNZeroSplice

/-! Restore the prefix before a zero-class root. New externally
parented heads have the root's zero-value and parent, so the old BN
comparison at that root bounds their complete blocks. -/
namespace BTnSSBMS.Source

theorem outerContext_dropLast_drop (d : Nat) (context : ParentContext) (index : Nat)
    (e : NumericalExpr) {a : List Nat} {hs : Forests (List Nat)} {rest : NumericalExpr}
    (found : drop index e = .cons a hs rest) :
    outerContext d (dropContext d context index e) (dropLast (.cons a hs rest)) =
      outerContext d context (dropLast e) := by
  induction index generalizing context e with
  | zero => change e = .cons a hs rest at found; rw [found, dropContext]
  | succ index ih =>
    cases e with
    | nil => simp [drop] at found
    | cons b ks tail =>
      cases tail with
      | nil => cases index <;> simp [drop] at found
      | cons c js more =>
        simpa only [dropContext, dropLast, outerContext] using
          ih (context ++ [Parents.label d context b]) (.cons c js more) found

theorem zero_parent_before_root {d : Nat} (positive : 0 < d) (context : ParentContext)
    (index : Nat) (e : NumericalExpr) {a : List Nat} {hs : Forests (List Nat)} {rest : NumericalExpr}
    (found : drop index e = .cons a hs rest)
    (above : ∀ b ∈ labels rest, a[0]?.getD 0 < b[0]?.getD 0) :
    (Parents.label d (outerContext d context (dropLast e)) a).parents[0]?.join =
      (Parents.label d (dropContext d context index e) a).parents[0]?.join := by
  have fenced : ∀ b ∈ labels (.cons a hs rest), a[0]?.getD 0 ≤ b[0]?.getD 0 := by
    intro b member
    simp only [labels, List.mem_cons] at member
    rcases member with rfl | later
    · exact Nat.le_refl _
    · exact Nat.le_of_lt (above b later)
  have same := label_zero_dropContext_ge positive (dropContext d context index e)
    (length (.cons a hs rest) - 1) (.cons a hs rest) a fenced
  rw [dropContext_last, outerContext_dropLast_drop d context index e found] at same
  exact same

theorem BN.splice_zero_before_root {d : Nat} {context : ParentContext}
    {e replacement : NumericalExpr} (ordered : BN d context e) (positive : 0 < d)
    (legal : FiniteLegal d context e) (index : Nat)
    {a : List Nat} {hs : Forests (List Nat)} {rest : NumericalExpr}
    (found : Source.drop index e = .cons a hs rest) (nonempty : rest ≠ .nil)
    (above : ∀ b ∈ labels rest, a[0]?.getD 0 < b[0]?.getD 0)
    (rooted : BN d (dropContext d context index e) (splice 0 replacement (.cons a hs rest)))
    {terminal : List Nat} {attached : Forests (List Nat)}
    (last : last? e = some (terminal, attached))
    (good : BN d (outerContext d context (Source.dropLast e)) replacement)
    (lower : ExprLE replacement (.cons terminal attached .nil))
    (floor : TerminalFloor a replacement)
    (blocks : ExprLE (rootBlock replacement) (rootBlock (.cons a hs rest))) :
    BN d context (splice 0 replacement e) := by
  induction index generalizing context e with
  | zero => change e = .cons a hs rest at found; simpa only [dropContext, found] using rooted
  | succ index ih =>
    cases e with
    | nil => simp [Source.drop] at found
    | cons b ks tail =>
      cases tail with
      | nil => cases index <;> simp [Source.drop] at found
      | cons c js more =>
        have selected : Source.drop index (.cons c js more) = .cons a hs rest := by
          simpa only [Source.drop] using found
        have lastRest : last? (.cons c js more) = some (terminal, attached) := by simpa only [last?] using last
        let entry := context ++ [Parents.label d context b]
        let before := outerContext d entry (Source.dropLast (.cons c js more))
        have good' : BN d before replacement := by simpa only [Source.dropLast, outerContext] using good
        rw [splice]
        refine ⟨?_, ordered.2.1, ih ordered.2.2 legal.2.2.2.2 selected rooted lastRest good'⟩
        intro offset v forests remaining hit same
        rcases splice_zero_drop_cases d entry (.cons c js more) replacement offset hit with
          ⟨after, old, survives, contexts, value⟩ | ⟨position, new, contexts⟩
        · rw [contexts] at same
          have prior := ordered.1 offset v forests after old same
          have laterLegal := legal.2.2.2.2.drop offset
          rw [old] at laterLegal
          have equalZero := same_zero_parent_value positive
            ((List.prefix_append context _).trans (dropContext_prefix d entry offset (.cons c js more)))
            b v legal.2.1 laterLegal.2.1 same
          have unchanged := takeAbove_splice_zero_surviving replacement offset (b[0]?.getD 0)
            old survives (Nat.le_of_eq equalZero)
          change ExprLE (rootBlock (.cons v forests remaining))
            (.cons b ks (takeAbove (b[0]?.getD 0) (splice 0 replacement (.cons c js more))))
          rw [unchanged]
          have afterLast := (last_drop_of_cons offset (.cons c js more) old).trans lastRest
          have decrease := rootBlock_mono (splice_zero_le (.cons v forests after) replacement afterLast lower)
          rw [← value] at decrease
          exact decrease.trans prior
        · change dropContext d entry offset (splice 0 replacement (.cons c js more)) =
            dropContext d before position replacement at contexts
          rw [contexts] at same
          cases replacement with
          | nil => cases position <;> simp [Source.drop] at new
          | cons first trees trailing =>
            have fenced : ∀ col ∈ labels (.cons first trees trailing), first[0]?.getD 0 ≤ col[0]?.getD 0 := by
              intro col member
              rw [floor.1]
              exact floor.2 col member
            have initial : context <+: before :=
              (List.prefix_append context _).trans (outerContext_prefix d entry (Source.dropLast (.cons c js more)))
            have external : ∀ p,
                (Parents.label d (dropContext d before position (.cons first trees trailing)) v).parents[0]?.join = some p →
                  p < before.length := by
              intro p edge
              rw [same] at edge
              exact Nat.lt_of_lt_of_le (Parents.label_parent_bound d context b 0 p edge) initial.length_le
            have firstParent := external_suffix_parent positive before first trees trailing position new fenced external
            have rootParent : (Parents.label d (dropContext d entry index (.cons c js more)) a).parents[0]?.join =
                (Parents.label d context b).parents[0]?.join := by
              rw [← zero_parent_before_root positive entry index (.cons c js more) selected above]
              have firstEq : (Parents.label d before a).parents[0]?.join =
                  (Parents.label d before first).parents[0]?.join := by
                rw [Parents.label_zero d before a positive, Parents.label_zero d before first positive, floor.1]
              exact firstEq.trans (firstParent.symm.trans same)
            have prior := ordered.1 index a hs rest selected rootParent
            have rootLegal := legal.2.2.2.2.drop index
            rw [selected] at rootLegal
            have equalZero := same_zero_parent_value positive
              ((List.prefix_append context _).trans (dropContext_prefix d entry index (.cons c js more)))
              b a legal.2.1 rootLegal.2.1 rootParent
            have unchanged := takeAbove_splice_zero_surviving (.cons first trees trailing) index (b[0]?.getD 0)
              selected nonempty (Nat.le_of_eq equalZero)
            change ExprLE (rootBlock (.cons v forests remaining))
              (.cons b ks (takeAbove (b[0]?.getD 0) (splice 0 (.cons first trees trailing) (.cons c js more))))
            rw [unchanged]
            exact (good'.external_block_le positive position new fenced external).trans (blocks.trans prior)

end BTnSSBMS.Source
