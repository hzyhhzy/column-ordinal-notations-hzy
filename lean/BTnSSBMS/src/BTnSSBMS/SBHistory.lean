import BTnSSBMS.SBBlockContext

/-! SB reads complete historical blocks, not the arbitrary tails after
those blocks. This extensionality theorem includes open owner positions
and restores the original history at each sibling forest. -/
namespace BTnSSBMS.Source

theorem append_block_history_eq {size : Nat} {left right : List NumericalExpr}
    (leftLength : left.length = size) (rightLength : right.length = size)
    (same : ∀ root, root < size → rootBlock (left[root]?.getD .nil) = rootBlock (right[root]?.getD .nil))
    {e f : NumericalExpr} (lastSame : rootBlock e = rootBlock f) :
    ∀ root, root < size + 1 →
      rootBlock ((left ++ [e])[root]?.getD .nil) = rootBlock ((right ++ [f])[root]?.getD .nil) := by
  intro root inside
  by_cases old : root < size
  · simpa only [List.getElem?_append_left (by omega : root < left.length),
      List.getElem?_append_left (by omega : root < right.length)] using same root old
  · have last : root = size := by omega
    subst root
    have atLeft : (left ++ [e])[size]? = some e := by rw [← leftLength, List.getElem?_concat_length]
    have atRight : (right ++ [f])[size]? = some f := by rw [← rightLength, List.getElem?_concat_length]
    simpa only [atLeft, atRight, Option.getD_some] using lastSame

theorem HeadSB.history_congr {d cut : Nat} {context : ParentContext}
    {left right : List NumericalExpr} {a : List Nat} {hs : Forests (List Nat)} {rest : NumericalExpr}
    (ordered : HeadSB d cut context left a hs rest)
    (same : ∀ root, root < context.length →
      rootBlock (left[root]?.getD .nil) = rootBlock (right[root]?.getD .nil)) :
    HeadSB d cut context right a hs rest := by
  intro positive room root inside path shared
  have prior := ordered positive room root inside path shared
  simpa only [rebaseBlock, same root inside] using prior

mutual
  theorem SB.history_congr {d cut : Nat} {context : ParentContext}
      {left right : List NumericalExpr} (e : NumericalExpr)
      (leftLength : left.length = context.length) (rightLength : right.length = context.length)
      (same : ∀ root, root < context.length →
        rootBlock (left[root]?.getD .nil) = rootBlock (right[root]?.getD .nil))
      (ordered : SB d cut context left e) : SB d cut context right e := by
    cases e with
    | nil => trivial
    | cons a hs rest =>
      have later := append_block_history_eq leftLength rightLength same (e := .cons a hs rest) rfl
      have leftNext : (left ++ [Expr.cons a hs rest]).length = (context ++ [Parents.label d context a]).length := by
        simp only [List.length_append, List.length_cons, List.length_nil, leftLength]
      have rightNext : (right ++ [Expr.cons a hs rest]).length = (context ++ [Parents.label d context a]).length := by
        simp only [List.length_append, List.length_cons, List.length_nil, rightLength]
      have later' : ∀ root, root < (context ++ [Parents.label d context a]).length →
          rootBlock ((left ++ [.cons a hs rest])[root]?.getD .nil) =
            rootBlock ((right ++ [.cons a hs rest])[root]?.getD .nil) := by simpa only [List.length_append, List.length_cons, List.length_nil] using later
      exact ⟨ordered.1.history_congr same,
        SBForests.history_congr hs leftNext rightNext later' ordered.2.1,
        SB.history_congr rest leftNext rightNext later' ordered.2.2⟩

  theorem SBForests.history_congr {d cut : Nat} {context : ParentContext}
      {left right : List NumericalExpr} (hs : Forests (List Nat))
      (leftLength : left.length = context.length) (rightLength : right.length = context.length)
      (same : ∀ root, root < context.length →
        rootBlock (left[root]?.getD .nil) = rootBlock (right[root]?.getD .nil))
      (ordered : SBForests d cut context left hs) : SBForests d cut context right hs := by
    cases hs with
    | nil => trivial
    | cons h rest => exact ⟨SB.history_congr h leftLength rightLength same ordered.1,
        SBForests.history_congr rest leftLength rightLength same ordered.2⟩
end

end BTnSSBMS.Source
