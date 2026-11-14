import BTnSSBMS.PartialRebaseHead
import BTnSSBMS.RelocationBlocks

/-! A canonical description of the existing partial rebase. Its equality
with the literal activation-and-shift operation is proved here. Complete
attachment lists and outer tails are retained, with their actual scopes. -/
namespace BTnSSBMS.Source

def partialMaterial (d : Nat) (context : ParentContext) (root cut : Nat)
    (position : List Nat) (hs : Forests (List Nat)) (rest : NumericalExpr) : NumericalExpr :=
  let head := partialHead context root cut position
  let next := context ++ [Parents.label d context head]
  let visible := List.range root ++ [context.length]
  .cons head (relocateForests d (context.take (root + 1)) next visible hs)
    (relocate d (context.take (root + 1)) next visible rest)

theorem partialMaterial_eq_copied {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    (unit : Parents.UnitSteps d context) (position : List Nat)
    (positionUnit : Parents.UnitSteps d (context ++ [Parents.label d context position]))
    {cut root : Nat} (positive : 0 < cut) (room : cut < d) (inside : root < context.length)
    (path : Parents.Ancestor (context ++ [Parents.label d context position]) (cut - 1) root context.length)
    (same : (Parents.label d context position).parents[cut]?.join = Parents.parent context cut root)
    (hs : Forests (List Nat)) (rest : NumericalExpr)
    (legal : FiniteLegal d (context.take root)
      (.cons (context[root]?.getD default).coordinates hs rest)) :
    partialMaterial d context root cut position hs rest =
      copied d root cut ((List.range cut).map
        (fun j => position[j]?.getD 0 - (context[root]?.getD default).coordinates[j]?.getD 0))
        1 (context.take root) (List.replicate root 0)
        (.cons (context[root]?.getD default).coordinates hs rest) := by
  have scope := partial_rebase_shiftView coherent valid unit position positionUnit
    positive room inside path same legal.1
  have divided := coherent.take_succ_label inside
  have nextLegal := legal
  simp only [FiniteLegal] at nextLegal
  rw [← divided] at nextLegal
  rw [partialMaterial, copied_at_root]
  rw [← divided]
  simp only [partialHead]
  rw [relocateForests_eq_copied scope ((context[root]?.getD default).coordinates[0]?.getD 0)
    hs nextLegal.2.2.2.1, relocate_eq_copied scope rest nextLegal.2.2.2.2]

theorem partialMaterial_finiteLegal {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    (unit : Parents.UnitSteps d context) (position : List Nat)
    (positionUnit : Parents.UnitSteps d (context ++ [Parents.label d context position]))
    {cut root : Nat} (positive : 0 < cut) (room : cut < d) (inside : root < context.length)
    (path : Parents.Ancestor (context ++ [Parents.label d context position]) (cut - 1) root context.length)
    (same : (Parents.label d context position).parents[cut]?.join = Parents.parent context cut root)
    (hs : Forests (List Nat)) (rest : NumericalExpr)
    (legal : FiniteLegal d (context.take root)
      (.cons (context[root]?.getD default).coordinates hs rest)) :
    FiniteLegal d context (partialMaterial d context root cut position hs rest) := by
  rw [partialMaterial_eq_copied coherent valid unit position positionUnit positive room inside path same hs rest legal]
  exact partial_rebase_finiteLegal coherent valid unit position positionUnit positive room inside path same hs rest legal

end BTnSSBMS.Source
