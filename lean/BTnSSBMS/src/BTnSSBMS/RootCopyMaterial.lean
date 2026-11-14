import BTnSSBMS.RootCopyReset

/-! Exact partial rebasing of a complete forced-root template. The
forests and the entire outer tail commute through the two actual scoped
transports. No clipping to a first column or bounded depth is used. -/
namespace BTnSSBMS.Source

theorem root_copy_partialMaterial {d : Nat} {context target later : ParentContext} {a : List Nat}
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
      (cap - 1) target.length later.length) :
    partialMaterial d later target.length cap (shift a cap delta nextPhase)
      (copiedForests d context.length cap delta phase (context ++ [Parents.label d context a])
        (List.replicate context.length 0 ++ [cap]) hs)
      (copied d context.length cap delta phase (context ++ [Parents.label d context a])
        (List.replicate context.length 0 ++ [cap]) rest) =
      copied d context.length cap delta nextPhase context (List.replicate context.length 0) (.cons a hs rest) := by
  have head := root_copy_partial_head (next.targetCoherent.restrict (List.prefix_append _ _))
    legal.1 positive room initial path
  have takeOld : later.take (target.length + 1) = target ++ [Parents.label d target (shift a cap delta phase)] := by
    simpa only [List.length_append, List.length_cons, List.length_nil] using (List.prefix_iff_eq_take.mp initial).symm
  have mapSquare := root_views_reset_map scope next fixed
  have length : (List.range target.length ++ [later.length]).length =
      (target ++ [Parents.label d target (shift a cap delta phase)]).length := by simp
  have forests := relocateForests_compose d hs (context ++ [Parents.label d context a])
    (target ++ [Parents.label d target (shift a cap delta phase)])
    (later ++ [Parents.label d later (shift a cap delta nextPhase)])
    visible (List.range target.length ++ [later.length])
    scope.sourceCoherent scope.sourceValid scope.targetCoherent scope.targetValid scope.view length
  rw [mapSquare, relocateForests_eq_copied scope (a[0]?.getD 0) hs legal.2.2.2.1,
    relocateForests_eq_copied next (a[0]?.getD 0) hs legal.2.2.2.1] at forests
  have tail := relocate_compose d rest (context ++ [Parents.label d context a])
    (target ++ [Parents.label d target (shift a cap delta phase)])
    (later ++ [Parents.label d later (shift a cap delta nextPhase)])
    visible (List.range target.length ++ [later.length])
    scope.sourceCoherent scope.sourceValid scope.targetCoherent scope.targetValid scope.view length
  rw [mapSquare, relocate_eq_copied scope rest legal.2.2.2.2,
    relocate_eq_copied next rest legal.2.2.2.2] at tail
  rw [partialMaterial, head, takeOld, copied_at_root]
  exact congr (congrArg (Expr.cons (shift a cap delta nextPhase)) forests) tail

end BTnSSBMS.Source
