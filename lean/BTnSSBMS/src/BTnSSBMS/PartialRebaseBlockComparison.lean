import BTnSSBMS.PartialRebaseNaturality
import BTnSSBMS.ExactRelocationEntries

/-! Exact comparison transport of the two complete blocks occurring in
SB. This proves the same-copy comparison reduction, not SB preservation
at a rewritten terminal or between different copy phases. -/
namespace BTnSSBMS.Source

theorem partialMaterial_block_compare {d : Nat} {source target : ParentContext} {visible : List Nat}
    (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
    (sourceUnit : Parents.UnitSteps d source)
    (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
    (targetUnit : Parents.UnitSteps d target) (view : Parents.NumericalView d source target visible)
    (position : List Nat) {root cut : Nat} (positive : 0 < cut) (room : cut < d)
    (inside : root < source.length)
    (path : Parents.Ancestor (source ++ [Parents.label d source position]) (cut - 1) root source.length)
    (same : (Parents.label d source position).parents[cut]?.join = Parents.parent source cut root)
    (exactAt : Parents.ExactPosition d source target visible root)
    (targetWidth : (target[Parents.point visible root]?.getD default).coordinates.length = d)
    (hs ks : Forests (List Nat)) (rest tail : NumericalExpr)
    (oldLegal : FiniteLegal d (source.take root) (.cons (source[root]?.getD default).coordinates hs rest))
    (newLegal : FiniteLegal d source (.cons position ks tail)) :
    (partialMaterial d target (Parents.point visible root) cut
      (relocationHead d source target visible position)
      (relocateForests d (source.take (root + 1))
        (target.take (Parents.point visible root + 1)) (visible.take (root + 1)) hs)
      (relocate d (source.take (root + 1))
        (target.take (Parents.point visible root + 1)) (visible.take (root + 1)) rest)).compare
      (listCompare Ord.compare)
      (rootBlock (relocate d source target visible (.cons position ks tail))) =
    (partialMaterial d source root cut position hs rest).compare (listCompare Ord.compare)
      (rootBlock (.cons position ks tail)) := by
  rw [← partialMaterial_naturality sourceCoherent sourceValid sourceUnit targetCoherent targetValid targetUnit
    view position newLegal.2.1 positive room inside path same exactAt oldLegal.1 targetWidth hs rest,
    ← relocate_rootBlock d (.cons position ks tail) source target visible
      sourceCoherent sourceValid targetCoherent targetValid view (by omega) newLegal]
  exact relocate_compare d _ _ source target visible sourceCoherent sourceValid targetCoherent targetValid view
    (partialMaterial_finiteLegal sourceCoherent sourceValid sourceUnit position newLegal.2.1
      positive room inside path same hs rest oldLegal) (rootBlock_finiteLegal newLegal)

end BTnSSBMS.Source
