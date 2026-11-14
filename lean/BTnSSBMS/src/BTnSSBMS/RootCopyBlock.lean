import BTnSSBMS.RootCopyMaterial
import BTnSSBMS.SourceSB

/-! Complete root blocks commute with a forced-root copy. Rebasing an
earlier complete, unspliced template at a later forced root gives exactly
the later template's block. The actual run producing the roots is dealt
with separately; no final-splice block inequality is asserted here. -/
namespace BTnSSBMS.Source

theorem copied_forced_rootBlock {d : Nat} {context target : ParentContext} {a : List Nat}
    {visible : List Nat} {cap : Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d (context ++ [Parents.label d context a])
      (target ++ [Parents.label d target (shift a cap delta phase)]) visible
      (List.replicate context.length 0 ++ [cap]) context.length cap delta phase)
    (positive : 0 < d) (hs : Forests (List Nat)) (rest : NumericalExpr)
    (legal : FiniteLegal d context (.cons a hs rest)) :
    copied d context.length cap delta phase context (List.replicate context.length 0)
        (rootBlock (.cons a hs rest)) =
      rootBlock (copied d context.length cap delta phase context (List.replicate context.length 0)
        (.cons a hs rest)) := by
  have after := relocate_takeAbove d rest
    (context ++ [Parents.label d context a])
    (target ++ [Parents.label d target (shift a cap delta phase)]) visible
    scope.sourceCoherent scope.sourceValid scope.targetCoherent scope.targetValid scope.view
    positive context.length (by simp)
    (by simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_sub_cancel]; exact .refl _)
    legal.2.2.2.2
  rw [Parents.reading_append_label, root_view_point scope, Parents.reading_append_label] at after
  rw [relocate_eq_copied scope _ (takeAbove_finiteLegal legal.2.2.2.2),
    relocate_eq_copied scope rest legal.2.2.2.2] at after
  simpa only [rootBlock, copied_at_root] using congrArg
    (Expr.cons (shift a cap delta phase)
      (copiedForests d context.length cap delta phase (context ++ [Parents.label d context a])
        (List.replicate context.length 0 ++ [cap]) hs)) after

theorem root_copy_rebaseBlock {d : Nat} {context target later : ParentContext} {a : List Nat}
    {visible nextVisible : List Nat} {cap : Nat} {delta : List Nat} {phase nextPhase : Nat}
    (scope : ShiftView d (context ++ [Parents.label d context a])
      (target ++ [Parents.label d target (shift a cap delta phase)]) visible
      (List.replicate context.length 0 ++ [cap]) context.length cap delta phase)
    (next : ShiftView d (context ++ [Parents.label d context a])
      (later ++ [Parents.label d later (shift a cap delta nextPhase)]) nextVisible
      (List.replicate context.length 0 ++ [cap]) context.length cap delta nextPhase)
    (fixed : nextVisible.take context.length = visible.take context.length)
    (hs : Forests (List Nat)) (rest : NumericalExpr) (legal : FiniteLegal d context (.cons a hs rest))
    (positive : 0 < cap) (room : cap < d)
    (initial : target ++ [Parents.label d target (shift a cap delta phase)] <+: later)
    (path : Parents.Ancestor (later ++ [Parents.label d later (shift a cap delta nextPhase)])
      (cap - 1) target.length later.length)
    (same : (Parents.label d later (shift a cap delta nextPhase)).parents[cap]?.join =
      (Parents.label d target (shift a cap delta phase)).parents[cap]?.join) :
    rebaseBlock d cap later target.length (shift a cap delta nextPhase)
        (copied d context.length cap delta phase context (List.replicate context.length 0) (.cons a hs rest)) =
      rootBlock (copied d context.length cap delta nextPhase context (List.replicate context.length 0)
        (.cons a hs rest)) := by
  have dimension : 0 < d := by omega
  have inside : target.length < later.length := by
    have bound := initial.length_le
    simp only [List.length_append, List.length_cons, List.length_nil] at bound
    omega
  have before : target <+: later := (List.prefix_append _ _).trans initial
  have takeBefore : later.take target.length = target := (List.prefix_iff_eq_take.mp before).symm
  have coordinates := root_prefix_coordinates initial
  have parentSame : (Parents.label d later (shift a cap delta nextPhase)).parents[cap]?.join =
      Parents.parent later cap target.length := by
    rw [← Parents.parent_prefix_eq initial cap target.length (by simp), Parents.append_label_parent]
    exact same
  have blockLegal := rootBlock_finiteLegal legal
  have oldLegal := copied_root_finiteLegal scope dimension hs (takeAbove (a[0]?.getD 0) rest) blockLegal
  rw [copied_at_root] at oldLegal
  have atRoot : FiniteLegal d (later.take target.length)
      (.cons (later[target.length]?.getD default).coordinates
        (copiedForests d context.length cap delta phase (context ++ [Parents.label d context a])
          (List.replicate context.length 0 ++ [cap]) hs)
        (copied d context.length cap delta phase (context ++ [Parents.label d context a])
          (List.replicate context.length 0 ++ [cap]) (takeAbove (a[0]?.getD 0) rest))) := by
    rw [takeBefore, coordinates]
    exact oldLegal
  have material := partialMaterial_eq_copied
    (next.targetCoherent.restrict (List.prefix_append _ _))
    (next.targetValid.restrict (List.prefix_append _ _))
    (next.targetUnit.restrict next.targetValid (List.prefix_append _ _))
    (shift a cap delta nextPhase) next.targetUnit positive room inside path parentSame _ _ atRoot
  have reset := root_copy_partialMaterial scope next fixed hs (takeAbove (a[0]?.getD 0) rest)
    blockLegal positive room initial path
  rw [coordinates] at material
  rw [rebaseBlock, ← copied_forced_rootBlock scope dimension hs rest legal, rootBlock, copied_at_root,
    coordinates, ← material, reset]
  exact copied_forced_rootBlock next dimension hs rest legal

end BTnSSBMS.Source
