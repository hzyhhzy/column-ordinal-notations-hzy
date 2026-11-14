import BTnSSBMS.ExactCopyHole
import BTnSSBMS.SBCopyAncestry

/-!
The same-class barrier at an actual nested copy hole. The hole context,
activation history, exact ordinary parents, source ancestry and strict
row barrier are all derived from the frozen copied template. The later
endpoint's two lower-row paths remain the explicit classification inputs.
-/
namespace BTnSSBMS.Source

theorem copied_root_next_shared_parent_excluded {d : Nat}
    {context target : ParentContext} {a : List Nat} {visible : List Nat}
    {cap : Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d (context ++ [Parents.label d context a])
      (target ++ [Parents.label d target (shift a cap delta phase)]) visible
      (List.replicate context.length 0 ++ [cap]) context.length cap delta phase)
    (hs : Forests (List Nat)) (rest : NumericalExpr)
    (legal : FiniteLegal d context (.cons a hs rest)) (depth : Nat) {site : HoleSite}
    (found : holeSite d context none depth (.cons a hs rest) = some site)
    (positive : 0 < cap) (room : cap < d)
    (selected : (Parents.label d site.context site.terminal).parents[cap]?.join = some context.length)
    (difference : ∀ row, row < cap →
      site.terminal[row]?.getD 0 = a[row]?.getD 0 + delta[row]?.getD 0) :
    ∃ targetSite holeVisible,
      holeSite d target none depth
        (copied d context.length cap delta phase context (List.replicate context.length 0)
          (.cons a hs rest)) = some targetSite ∧
      ∀ position, context.length < position → position < site.context.length →
      ∀ later : ParentContext,
        targetSite.context ++ [Parents.label d targetSite.context (shift a cap delta (phase + 1))] <+: later →
        Parents.Coherent d later → Parents.ContextValid later →
      ∀ endpoint : List Nat,
        Parents.UnitSteps d (later ++ [Parents.label d later endpoint]) →
        Parents.Ancestor (later ++ [Parents.label d later endpoint])
          (cap - 1) (Parents.point holeVisible position) later.length →
        Parents.Ancestor (later ++ [Parents.label d later endpoint])
          (cap - 1) targetSite.context.length later.length →
        (Parents.label d later endpoint).parents[cap]?.join ≠
          Parents.parent later cap (Parents.point holeVisible position) := by
  have later := Parents.label_parent_bound d site.context site.terminal cap context.length selected
  obtain ⟨targetSite, targetFound, hole⟩ :=
    copied_root_holeSite_exact scope hs rest legal depth found later
  obtain ⟨holeVisible, holeHistory, _, atHole, exactAt, _, _⟩ := hole
  have sourceHole := (holeSite_finiteLegal depth (.cons a hs rest) legal
    (by intro bound impossible; cases impossible) found).1
  have coordinates := holeSite_root_coordinates found later
  have rootWidth : (site.context[context.length]?.getD default).coordinates.length = d := by
    rw [coordinates]
    exact legal.1
  have actualDifference : ∀ row, row < cap → site.terminal[row]?.getD 0 =
      Parents.reading site.context row context.length + delta[row]?.getD 0 := by
    intro row below
    change site.terminal[row]?.getD 0 =
      (site.context[context.length]?.getD default).coordinates[row]?.getD 0 + delta[row]?.getD 0
    rw [coordinates]
    exact difference row below
  refine ⟨targetSite, holeVisible, targetFound, ?_⟩
  intro position after inside laterContext initial coherent valid endpoint unit oldPath rootPath
  have actualInitial : targetSite.context ++ [Parents.label d targetSite.context
      (shift (site.context[context.length]?.getD default).coordinates cap delta (phase + 1))] <+:
      laterContext := by
    simpa only [coordinates] using initial
  exact atHole.next_root_shared_parent_excluded_of_ancestry site.terminal sourceHole.1
    sourceHole.2.1 rootWidth positive room selected actualDifference exactAt after inside
    actualInitial coherent valid endpoint unit oldPath rootPath

end BTnSSBMS.Source
