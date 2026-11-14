import BTnSSBMS.PartialRebaseBlockComparison
import BTnSSBMS.RelocatedRootMaterial

/-! Return the complete-block commuting result to the literal frozen
copies, including both partial rebases. Ordinary copied roots use the
exact-position witnesses of ExactRelocationEntries; the forced root and
rewritten/donated boundaries remain separate proof obligations. -/
namespace BTnSSBMS.Source

theorem copied_partial_block_compare {d copyRoot cap phase : Nat}
    {source target : ParentContext} {visible history delta : List Nat}
    (scope : ShiftView d source target visible history copyRoot cap delta phase)
    (sourceUnit : Parents.UnitSteps d source) (position : List Nat)
    {root cut : Nat} (positive : 0 < cut) (room : cut < d)
    (afterRoot : copyRoot ≤ root) (inside : root < source.length)
    (path : Parents.Ancestor (source ++ [Parents.label d source position]) (cut - 1) root source.length)
    (same : (Parents.label d source position).parents[cut]?.join = Parents.parent source cut root)
    (exactAt : Parents.ExactPosition d source target visible root)
    (targetWidth : (target[Parents.point visible root]?.getD default).coordinates.length = d)
    (hs ks : Forests (List Nat)) (rest tail : NumericalExpr)
    (oldLegal : FiniteLegal d (source.take root) (.cons (source[root]?.getD default).coordinates hs rest))
    (newLegal : FiniteLegal d source (.cons position ks tail)) :
    let moved := shift position (Keys.threshold cap copyRoot history (Parents.label d source position)) delta phase
    let targetRoot := (target[Parents.point visible root]?.getD default).coordinates
    let targetDelta := (List.range cut).map (fun j => moved[j]?.getD 0 - targetRoot[j]?.getD 0)
    let movedForests := copiedForests d copyRoot cap delta phase
      (source.take (root + 1)) (history.take (root + 1)) hs
    let movedRest := copied d copyRoot cap delta phase
      (source.take (root + 1)) (history.take (root + 1)) rest
    (copied d (Parents.point visible root) cut targetDelta 1
      (target.take (Parents.point visible root)) (List.replicate (Parents.point visible root) 0)
      (.cons targetRoot movedForests movedRest)).compare (listCompare Ord.compare)
      (rootBlock (copied d copyRoot cap delta phase source history (.cons position ks tail))) =
    (copied d root cut ((List.range cut).map
      (fun j => position[j]?.getD 0 - (source[root]?.getD default).coordinates[j]?.getD 0))
      1 (source.take root) (List.replicate root 0)
      (.cons (source[root]?.getD default).coordinates hs rest)).compare
      (listCompare Ord.compare) (rootBlock (.cons position ks tail)) := by
  dsimp only
  have movedPair := partial_pair_transport scope.sourceCoherent scope.sourceValid scope.targetCoherent
    scope.targetValid scope.view position positive room inside path same exactAt
  have movedUnit := relocationHead_unitSteps scope.sourceCoherent scope.sourceValid scope.targetCoherent
    scope.targetValid scope.targetUnit scope.view position
  have oldMovedLegal := relocated_root_material_finiteLegal scope.sourceCoherent scope.sourceValid sourceUnit
    scope.targetCoherent scope.targetValid scope.targetUnit scope.view (by omega) inside exactAt targetWidth hs rest oldLegal
  have result := partialMaterial_block_compare scope.sourceCoherent scope.sourceValid sourceUnit
    scope.targetCoherent scope.targetValid scope.targetUnit scope.view position positive room inside path same
    exactAt targetWidth hs ks rest tail oldLegal newLegal
  rw [partialMaterial_eq_copied scope.targetCoherent scope.targetValid scope.targetUnit
      (relocationHead d source target visible position) movedUnit positive room (scope.view.bounded root inside)
      movedPair.1 movedPair.2 _ _ oldMovedLegal,
    partialMaterial_eq_copied scope.sourceCoherent scope.sourceValid sourceUnit position newLegal.2.1
      positive room inside path same hs rest oldLegal] at result
  have restricted := scope.prefix_at root inside afterRoot
  have nextLegal := oldLegal
  simp only [FiniteLegal] at nextLegal
  rw [← scope.sourceCoherent.take_succ_label inside] at nextLegal
  rw [relocateForests_eq_copied restricted ((source[root]?.getD default).coordinates[0]?.getD 0)
      hs nextLegal.2.2.2.1,
    relocate_eq_copied restricted rest nextLegal.2.2.2.2,
    relocate_eq_copied scope (.cons position ks tail) newLegal,
    relocationHead_eq_shift scope position newLegal.1 newLegal.2.1] at result
  exact result

end BTnSSBMS.Source
