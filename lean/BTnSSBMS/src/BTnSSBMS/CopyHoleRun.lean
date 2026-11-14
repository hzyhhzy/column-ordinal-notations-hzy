import BTnSSBMS.CopyHoleDensity
import BTnSSBMS.CopyRootChain

/-! A finite observer of the existing copy recursion. At each step it
computes the real copied template's terminal-hole context, exactly the
context used to enter the next replica. It does not change expansion.
The iteration theorem constructs its numerical scopes and lower-row
root chain for every finite number of copies. -/
namespace BTnSSBMS.Source

def copyHoleAfter (d cap : Nat) (delta : List Nat) (context : ParentContext)
    (template : NumericalExpr) (depth : Nat) : Nat → Nat → ParentContext → Option ParentContext
  | 0, _, target => some target
  | count + 1, phase, target =>
      match holeSite d target none depth
          (copied d context.length cap delta phase context (List.replicate context.length 0) template) with
      | none => none
      | some site => copyHoleAfter d cap delta context template depth count (phase + 1) site.context

theorem take_visible_prefix {initial visible : List Nat} (extended : initial <+: visible)
    {count : Nat} (inside : count ≤ initial.length) : visible.take count = initial.take count := by
  obtain ⟨tail, rfl⟩ := extended
  exact List.take_append_of_le_length inside

theorem copyHoleAfter_prefix (d cap : Nat) (delta : List Nat) (context : ParentContext)
    (template : NumericalExpr) (depth count phase : Nat) (target : ParentContext)
    {result : ParentContext}
    (computed : copyHoleAfter d cap delta context template depth count phase target = some result) :
    target <+: result := by
  induction count generalizing phase target with
  | zero =>
    have same : result = target := by simpa only [copyHoleAfter, Option.some.injEq] using computed.symm
    subst result
    exact List.prefix_refl _
  | succ count ih =>
    simp only [copyHoleAfter] at computed
    cases found : holeSite d target none depth
        (copied d context.length cap delta phase context (List.replicate context.length 0) template) with
    | none => simp only [found] at computed; cases computed
    | some site =>
      simp only [found] at computed
      exact (holeSite_extends d target none depth _ found).trans (ih (phase + 1) site.context computed)

theorem copyHoleAfter_state {d : Nat} {context target : ParentContext} {a : List Nat}
    {visible : List Nat} {cap : Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d (context ++ [Parents.label d context a])
      (target ++ [Parents.label d target (shift a cap delta phase)]) visible
      (List.replicate context.length 0 ++ [cap]) context.length cap delta phase)
    (hs : Forests (List Nat)) (rest : NumericalExpr)
    (legal : FiniteLegal d context (.cons a hs rest)) (depth : Nat) {site : HoleSite}
    (found : holeSite d context none depth (.cons a hs rest) = some site)
    (room : cap < d)
    (selected : (Parents.label d site.context site.terminal).parents[cap]?.join = some context.length)
    (difference : ∀ row, row < cap →
      site.terminal[row]?.getD 0 = a[row]?.getD 0 + delta[row]?.getD 0) (count : Nat) :
    ∃ result finalVisible,
      copyHoleAfter d cap delta context (.cons a hs rest) depth count phase target = some result ∧
      ShiftView d (context ++ [Parents.label d context a])
        (result ++ [Parents.label d result (shift a cap delta (phase + count))]) finalVisible
        (List.replicate context.length 0 ++ [cap]) context.length cap delta (phase + count) ∧
      finalVisible.take context.length = visible.take context.length ∧
      target ++ [Parents.label d target (shift a cap delta phase)] <+:
        result ++ [Parents.label d result (shift a cap delta (phase + count))] ∧
      ∀ row, row < cap → Parents.Ancestor
        (result ++ [Parents.label d result (shift a cap delta (phase + count))])
        row target.length result.length := by
  induction count generalizing target visible phase with
  | zero => exact ⟨target, visible, rfl, scope, rfl, List.prefix_refl _, fun _ _ => .refl _⟩
  | succ count ih =>
    have later := Parents.label_parent_bound d site.context site.terminal cap context.length selected
    have coordinates := holeSite_root_coordinates found later
    have rootTake := holeSite_root_take found later
    have sourceHole := (holeSite_finiteLegal depth (.cons a hs rest) legal
      (by intro bound impossible; cases impossible) found).1
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
    obtain ⟨hole, holeFound, holeView⟩ := copied_root_holeSite_exact scope hs rest legal depth found later
    obtain ⟨holeVisible, holeHistory, holePrefix, atHole, _, _, _⟩ := holeView
    have density := copied_root_hole_density scope hs rest depth found holeFound later atHole.view holePrefix
    have restart := atHole.restart site.terminal sourceHole.1 sourceHole.2.1 rootWidth room selected actualDifference
    dsimp only at restart
    rw [rootTake, coordinates] at restart
    obtain ⟨result, finalVisible, computed, finalScope, finalTake, finalPrefix, rootChain⟩ := ih restart
    have phaseEq : phase + 1 + count = phase + (count + 1) := by omega
    rw [phaseEq] at finalScope finalPrefix rootChain
    refine ⟨result, finalVisible, ?_, finalScope, ?_, ?_, ?_⟩
    · simpa only [copyHoleAfter, holeFound] using computed
    · rw [finalTake]
      have takeLength : (holeVisible.take context.length).length = context.length := by
        simp only [List.length_take, atHole.view.length]
        omega
      rw [List.take_append_of_le_length (by omega : context.length ≤ (holeVisible.take context.length).length),
        List.take_take, Nat.min_self]
      exact take_visible_prefix holePrefix (by rw [scope.view.length]; simp)
    · have targetLater : target.length < hole.context.length := by
        rw [← density.1]
        exact atHole.view.bounded context.length later
      have rootFound := holeFound
      rw [copied_at_root] at rootFound
      exact (holeSite_after_head rootFound targetLater).trans ((List.prefix_append _ _).trans finalPrefix)
    · intro row low
      have previous := atHole.next_root_retains_previous_root site.terminal sourceHole.1 sourceHole.2.1
        rootWidth room selected actualDifference low
      rw [density.1, coordinates] at previous
      exact (previous.prefix finalPrefix).trans (rootChain row low)

end BTnSSBMS.Source
