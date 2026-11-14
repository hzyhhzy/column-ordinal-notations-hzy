import BTnSSBMS.ExactNumericalPosition

/-! Legality of the complete material at an earlier ordinary transported
root, checked in that root's own entry. A view alone is not used to
identify its stored coordinates or preserve positive attachments. -/
namespace BTnSSBMS.Source

theorem relocated_root_material_finiteLegal {d root : Nat}
    {source target : ParentContext} {visible : List Nat}
    (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
    (sourceUnit : Parents.UnitSteps d source)
    (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
    (targetUnit : Parents.UnitSteps d target) (view : Parents.NumericalView d source target visible)
    (positive : 0 < d) (inside : root < source.length)
    (exactAt : Parents.ExactPosition d source target visible root)
    (targetWidth : (target[Parents.point visible root]?.getD default).coordinates.length = d)
    (hs : Forests (List Nat)) (rest : NumericalExpr)
    (legal : FiniteLegal d (source.take root) (.cons (source[root]?.getD default).coordinates hs rest)) :
    FiniteLegal d (target.take (Parents.point visible root))
      (.cons (target[Parents.point visible root]?.getD default).coordinates
        (relocateForests d (source.take (root + 1))
          (target.take (Parents.point visible root + 1)) (visible.take (root + 1)) hs)
        (relocate d (source.take (root + 1))
          (target.take (Parents.point visible root + 1)) (visible.take (root + 1)) rest)) := by
  have sourceDivide := sourceCoherent.take_succ_label inside
  have targetBound := view.bounded root inside
  have targetDivide := targetCoherent.take_succ_label targetBound
  have sourceLength : (source.take (root + 1)).length = root + 1 := by simp only [List.length_take]; omega
  have targetLength : (target.take (Parents.point visible root + 1)).length = Parents.point visible root + 1 := by
    simp only [List.length_take]; omega
  have sourceReading : Parents.reading (source.take (root + 1)) 0 root =
      (source[root]?.getD default).coordinates[0]?.getD 0 := by
    rw [Parents.reading_prefix (List.take_prefix ..) 0 root (by rw [sourceLength]; omega)]
    rfl
  have targetReading : Parents.reading (target.take (Parents.point visible root + 1)) 0
      (Parents.point (visible.take (root + 1)) root) =
      (target[Parents.point visible root]?.getD default).coordinates[0]?.getD 0 := by
    rw [Parents.point_take visible (root + 1) root (by omega),
      Parents.reading_prefix (List.take_prefix ..) 0 (Parents.point visible root) (by rw [targetLength]; omega)]
    rfl
  have oldLegal := legal
  simp only [FiniteLegal] at oldLegal
  rw [← sourceDivide] at oldLegal
  have restricted := view.prefix_at targetValid root inside
  have nextUnit := targetUnit.restrict targetValid (List.take_prefix (Parents.point visible root + 1) target)
  have forests := relocateForests_finiteLegal d hs _ _ _
    (sourceCoherent.restrict (List.take_prefix ..)) (sourceValid.restrict (List.take_prefix ..))
    (targetCoherent.restrict (List.take_prefix ..)) (targetValid.restrict (List.take_prefix ..)) nextUnit restricted
    positive root (by rw [sourceLength]; omega) (by rw [sourceLength, Nat.add_sub_cancel]; exact .refl _)
    (by rw [sourceReading]; exact oldLegal.2.2.2.1)
  rw [targetReading] at forests
  have tail := relocate_finiteLegal d rest _ _ _
    (sourceCoherent.restrict (List.take_prefix ..)) (sourceValid.restrict (List.take_prefix ..))
    (targetCoherent.restrict (List.take_prefix ..)) (targetValid.restrict (List.take_prefix ..)) nextUnit restricted
    positive oldLegal.2.2.2.2
  simp only [FiniteLegal]
  rw [← targetDivide]
  refine ⟨targetWidth, nextUnit, ?_, forests, tail⟩
  intro nonempty row room
  have oldNonempty : hs ≠ .nil := by intro empty; subst hs; exact nonempty rfl
  exact (exactAt.positive_iff view sourceUnit targetUnit inside room).mpr (legal.2.2.1 oldNonempty row room)

end BTnSSBMS.Source
