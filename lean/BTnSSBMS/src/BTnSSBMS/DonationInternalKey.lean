import BTnSSBMS.KeyEmptyExtension

/-! The owned-donation boundary in SB: an internal column's key cannot
equal the whole donor key or its one-empty-forest extension. This uses
the actual recursive attachment structure, not an owner-excluding
highest-ancestor covariance lemma. It still needs the stated original
SB-derived upper comparison in the complete closure argument. -/
namespace BTnSSBMS.Source

mutual
  def columnInside (label : α) (attached : Forests α) : Expr α → Prop
    | .nil => False
    | .cons a hs rest => (a = label ∧ hs = attached) ∨
        columnInsideForests label attached hs ∨ columnInside label attached rest
  def columnInsideForests (label : α) (attached : Forests α) : Forests α → Prop
    | .nil => False
    | .cons h rest => columnInside label attached h ∨ columnInsideForests label attached rest
end

mutual
  theorem columnInside_nodes {label : α} {attached : Forests α} (e : Expr α)
      (occurs : columnInside label attached e) : attached.nodes < e.nodes := by
    cases e with
    | nil => exact False.elim occurs
    | cons a hs rest =>
      rcases occurs with ⟨_, same⟩ | inside | later
      · simp only [Expr.nodes, same]; omega
      · have smaller := columnInsideForests_nodes hs inside
        simp only [Expr.nodes]; omega
      · have smaller := columnInside_nodes rest later
        simp only [Expr.nodes]; omega

  theorem columnInsideForests_nodes {label : α} {attached : Forests α} (hs : Forests α)
      (occurs : columnInsideForests label attached hs) : attached.nodes < hs.nodes := by
    cases hs with
    | nil => exact False.elim occurs
    | cons h rest =>
      rcases occurs with inside | later
      · have smaller := columnInside_nodes h inside
        simp only [Forests.nodes]; omega
      · have smaller := columnInsideForests_nodes rest later
        simp only [Forests.nodes]; omega
end

theorem donation_internal_key_lt (d : Nat) (inner outer : ParentContext)
    (position owner : List Nat) (insideForests donor : Forests (List Nat))
    (occurs : columnInsideForests position insideForests donor)
    (bounded : Keys.compare
      (Keys.ofColumn d inner.length (Parents.label d inner position)
        (Parents.annotateForests d (inner ++ [Parents.label d inner position]) insideForests))
      (Keys.ofColumn d outer.length (Parents.label d outer owner)
        (Parents.annotateForests d (outer ++ [Parents.label d outer owner])
          (appendForests donor (.cons .nil .nil)))) ≠ .gt) :
    Keys.compare
      (Keys.ofColumn d inner.length (Parents.label d inner position)
        (Parents.annotateForests d (inner ++ [Parents.label d inner position]) insideForests))
      (Keys.ofColumn d outer.length (Parents.label d outer owner)
        (Parents.annotateForests d (outer ++ [Parents.label d outer owner]) donor)) = .lt := by
  rw [Keys.source_key_append_empty] at bounded
  apply Keys.smaller_nodes_below_empty_extension ?_ bounded
  rw [Keys.source_key_nodes, Keys.source_key_nodes]
  exact columnInsideForests_nodes donor occurs

end BTnSSBMS.Source
