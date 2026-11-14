import BTnSSBMS.PartialRebaseMaterial

/-! The full partial-rebase commuting square. Earlier and later entries
are distinct. Both composed position maps and the mixed head are derived;
no equality of separately computed labels is a premise. This treats
ordinary transported material, not inserted holes or donated lists. -/
namespace BTnSSBMS.Source

theorem partialMaterial_naturality {d : Nat} {source target : ParentContext} {visible : List Nat}
    (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
    (sourceUnit : Parents.UnitSteps d source)
    (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
    (targetUnit : Parents.UnitSteps d target) (view : Parents.NumericalView d source target visible)
    (position : List Nat) (positionUnit : Parents.UnitSteps d (source ++ [Parents.label d source position]))
    {root cut : Nat} (positive : 0 < cut) (room : cut < d) (inside : root < source.length)
    (path : Parents.Ancestor (source ++ [Parents.label d source position]) (cut - 1) root source.length)
    (same : (Parents.label d source position).parents[cut]?.join = Parents.parent source cut root)
    (exactAt : Parents.ExactPosition d source target visible root)
    (sourceWidth : (source[root]?.getD default).coordinates.length = d)
    (targetWidth : (target[Parents.point visible root]?.getD default).coordinates.length = d)
    (hs : Forests (List Nat)) (rest : NumericalExpr) :
    relocate d source target visible (partialMaterial d source root cut position hs rest) =
      partialMaterial d target (Parents.point visible root) cut
        (relocationHead d source target visible position)
        (relocateForests d (source.take (root + 1))
          (target.take (Parents.point visible root + 1)) (visible.take (root + 1)) hs)
        (relocate d (source.take (root + 1))
          (target.take (Parents.point visible root + 1)) (visible.take (root + 1)) rest) := by
  let oldHead := partialHead source root cut position
  let newHead := partialHead target (Parents.point visible root) cut
    (relocationHead d source target visible position)
  let oldNext := source ++ [Parents.label d source oldHead]
  let newNext := target ++ [Parents.label d target newHead]
  have head := partialHead_transport sourceCoherent sourceValid sourceUnit targetCoherent targetValid
    targetUnit view position positionUnit positive room inside path same exactAt sourceWidth targetWidth
  have extended : Parents.NumericalView d oldNext newNext (visible ++ [target.length]) := by
    simpa only [oldNext, newNext, oldHead, newHead, head] using
      relocation_view_append sourceCoherent sourceValid targetCoherent targetValid view oldHead
  have move := partial_rebase_shiftView sourceCoherent sourceValid sourceUnit position positionUnit
    positive room inside path same sourceWidth
  have restricted := view.prefix_at targetValid root inside
  have mapSquare := extended.transplant_maps (root := root) (by
    dsimp only [oldNext]
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_sub_cancel]
    exact inside)
  have mapAt : Parents.point (visible ++ [target.length]) root = Parents.point visible root :=
    Parents.point_append_old visible root target.length (by rw [view.length]; exact inside)
  simp only [oldNext, newNext, List.length_append, List.length_cons, List.length_nil,
    Nat.add_sub_cancel, mapAt,
    List.take_append_of_le_length (show root + 1 ≤ visible.length by rw [view.length]; omega)] at mapSquare
  have length : (List.range (Parents.point visible root) ++ [target.length]).length =
      (target.take (Parents.point visible root + 1)).length := by
    have bound := view.bounded root inside
    simp only [List.length_append, List.length_range, List.length_cons, List.length_nil, List.length_take]
    omega
  have afterLength : (visible ++ [target.length]).length = oldNext.length := by
    simp only [oldNext, List.length_append, List.length_cons, List.length_nil, view.length]
  have leftForests := relocateForests_compose d hs (source.take (root + 1)) oldNext newNext
    (List.range root ++ [source.length]) (visible ++ [target.length])
    (sourceCoherent.restrict (List.take_prefix ..)) (sourceValid.restrict (List.take_prefix ..))
    (Parents.coherent_append_label sourceCoherent oldHead)
    (Parents.context_valid_append_label d source sourceValid oldHead) move.view afterLength
  have rightForests := relocateForests_compose d hs (source.take (root + 1))
    (target.take (Parents.point visible root + 1)) newNext
    (visible.take (root + 1)) (List.range (Parents.point visible root) ++ [target.length])
    (sourceCoherent.restrict (List.take_prefix ..)) (sourceValid.restrict (List.take_prefix ..))
    (targetCoherent.restrict (List.take_prefix ..)) (targetValid.restrict (List.take_prefix ..)) restricted length
  have leftTail := relocate_compose d rest (source.take (root + 1)) oldNext newNext
    (List.range root ++ [source.length]) (visible ++ [target.length])
    (sourceCoherent.restrict (List.take_prefix ..)) (sourceValid.restrict (List.take_prefix ..))
    (Parents.coherent_append_label sourceCoherent oldHead)
    (Parents.context_valid_append_label d source sourceValid oldHead) move.view afterLength
  have rightTail := relocate_compose d rest (source.take (root + 1))
    (target.take (Parents.point visible root + 1)) newNext
    (visible.take (root + 1)) (List.range (Parents.point visible root) ++ [target.length])
    (sourceCoherent.restrict (List.take_prefix ..)) (sourceValid.restrict (List.take_prefix ..))
    (targetCoherent.restrict (List.take_prefix ..)) (targetValid.restrict (List.take_prefix ..)) restricted length
  have forests := leftForests.trans ((congrArg (fun positions =>
    relocateForests d (source.take (root + 1)) newNext positions hs) mapSquare).trans rightForests.symm)
  have tail := leftTail.trans ((congrArg (fun positions =>
    relocate d (source.take (root + 1)) newNext positions rest) mapSquare).trans rightTail.symm)
  simp only [partialMaterial, relocate, head]
  exact congr (congrArg (Expr.cons newHead) forests) tail

end BTnSSBMS.Source
