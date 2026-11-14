import BTnSSBMS.CopyHoleSquare
import BTnSSBMS.RootedRelocation
import BTnSSBMS.CopySeamNaturality

/-! Naturality for two literal copy phases with a commuting visible map.
The mixed seam head needs exact high parents, not just preserved ancestry.
These are finite transport identities, not a block-order conclusion. -/
namespace BTnSSBMS.Source

theorem ShiftView.head_relocation_square {d : Nat} {source middle target : ParentContext}
    {first direct history nextHistory : List Nat} {root cap : Nat} {delta : List Nat}
    {phase nextPhase : Nat}
    (scope : ShiftView d source middle first history root cap delta phase)
    (next : ShiftView d source target direct nextHistory root cap delta nextPhase)
    (between : List Nat) (square : first.map (Parents.point between) = direct)
    (a : List Nat) (width : a.length = d)
    (unit : Parents.UnitSteps d (source ++ [Parents.label d source a])) :
    relocationHead d middle target between
      (shift a (Keys.threshold cap root history (Parents.label d source a)) delta phase) =
      shift a (Keys.threshold cap root nextHistory (Parents.label d source a)) delta nextPhase := by
  rw [← relocationHead_eq_shift scope a width unit,
    relocationHead_compose scope.sourceCoherent scope.sourceValid scope.targetCoherent
      scope.targetValid scope.view target between a, square,
    relocationHead_eq_shift next a width unit]

theorem rooted_copy_relocation_square {d : Nat} {context target later : ParentContext} {a : List Nat}
    {visible nextVisible : List Nat} {cap : Nat} {delta : List Nat} {phase nextPhase : Nat}
    (scope : ShiftView d (context ++ [Parents.label d context a])
      (target ++ [Parents.label d target (shift a cap delta phase)]) visible
      (List.replicate context.length 0 ++ [cap]) context.length cap delta phase)
    (next : ShiftView d (context ++ [Parents.label d context a])
      (later ++ [Parents.label d later (shift a cap delta nextPhase)]) nextVisible
      (List.replicate context.length 0 ++ [cap]) context.length cap delta nextPhase)
    (between : List Nat) (length : between.length = target.length + 1)
    (square : visible.map (Parents.point between) = nextVisible)
    (hs : Forests (List Nat)) (rest : NumericalExpr)
    (legal : FiniteLegal d context (.cons a hs rest)) :
    rootedRelocate d target later between (shift a cap delta nextPhase)
      (copied d context.length cap delta phase context (List.replicate context.length 0)
        (.cons a hs rest)) =
      copied d context.length cap delta nextPhase context (List.replicate context.length 0)
        (.cons a hs rest) := by
  have mapLength : between.length =
      (target ++ [Parents.label d target (shift a cap delta phase)]).length := by simpa using length
  have forests := relocateForests_compose d hs (context ++ [Parents.label d context a])
    (target ++ [Parents.label d target (shift a cap delta phase)])
    (later ++ [Parents.label d later (shift a cap delta nextPhase)]) visible between
    scope.sourceCoherent scope.sourceValid scope.targetCoherent scope.targetValid scope.view mapLength
  rw [square, relocateForests_eq_copied scope (a[0]?.getD 0) hs legal.2.2.2.1,
    relocateForests_eq_copied next (a[0]?.getD 0) hs legal.2.2.2.1] at forests
  have tail := relocate_compose d rest (context ++ [Parents.label d context a])
    (target ++ [Parents.label d target (shift a cap delta phase)])
    (later ++ [Parents.label d later (shift a cap delta nextPhase)]) visible between
    scope.sourceCoherent scope.sourceValid scope.targetCoherent scope.targetValid scope.view mapLength
  rw [square, relocate_eq_copied scope rest legal.2.2.2.2,
    relocate_eq_copied next rest legal.2.2.2.2] at tail
  simp only [copied_at_root, rootedRelocate]
  exact congr (congrArg (Expr.cons (shift a cap delta nextPhase)) forests) tail

theorem ShiftView.next_head_relocation_square {d : Nat} {source middle target : ParentContext}
    {first direct history nextHistory between : List Nat} {root cap : Nat} {delta : List Nat}
    {phase nextPhase : Nat}
    (scope : ShiftView d source middle first history root cap delta phase)
    (next : ShiftView d source target direct nextHistory root cap delta nextPhase)
    (view : Parents.NumericalView d middle target between)
    (square : first.map (Parents.point between) = direct)
    (terminal : List Nat) (width : terminal.length = d)
    (unit : Parents.UnitSteps d (source ++ [Parents.label d source terminal]))
    (rootWidth : (source[root]?.getD default).coordinates.length = d)
    (room : cap < d)
    (selected : (Parents.label d source terminal).parents[cap]?.join = some root)
    (difference : ∀ row, row < cap →
      terminal[row]?.getD 0 = Parents.reading source row root + delta[row]?.getD 0)
    (highParents : ∀ row, cap ≤ row → row < d →
      Parents.parent target row (Parents.point between (Parents.point first root)) =
        (Parents.parent middle row (Parents.point first root)).map (Parents.point between)) :
    relocationHead d middle target between
      (shift (source[root]?.getD default).coordinates cap delta (phase + 1)) =
      shift (source[root]?.getD default).coordinates cap delta (nextPhase + 1) := by
  have oldThreshold := Keys.threshold_at_selected_root scope.sourceCoherent scope.sourceValid
    scope.historyCorrect scope.historyLength scope.afterRoot room terminal selected
  have newThreshold := Keys.threshold_at_selected_root next.sourceCoherent next.sourceValid
    next.historyCorrect next.historyLength next.afterRoot room terminal selected
  have oldSelected := scope.head_parents terminal width unit cap room
  rw [oldThreshold, selected, Option.map_some] at oldSelected
  have terminalTransport := scope.head_relocation_square next between square terminal width unit
  rw [oldThreshold, newThreshold] at terminalTransport
  have oldValues := scope.next_head_values terminal width rootWidth room difference
  have newValues := next.next_head_values terminal width rootWidth room difference
  have rootSquare : Parents.point between (Parents.point first root) = Parents.point direct root := by
    have equation := congrArg (fun values => Parents.point values root) square
    rw [Parents.point_map first between root (by rw [scope.view.length]; exact scope.afterRoot)] at equation
    exact equation
  apply first_copy_head_relocation scope.targetCoherent scope.targetValid view next.targetUnit
    (shift terminal cap delta phase)
    (shift (source[root]?.getD default).coordinates cap delta (phase + 1))
    (shift (source[root]?.getD default).coordinates cap delta (nextPhase + 1))
    (by rw [shift_width]; exact rootWidth) room oldSelected highParents oldValues.1 oldValues.2
  · intro row below
    rw [terminalTransport]
    exact newValues.1 row below
  · intro row above inside
    rw [rootSquare]
    exact newValues.2 row above inside

end BTnSSBMS.Source
