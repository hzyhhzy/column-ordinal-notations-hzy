import BTnSSBMS.BNZeroSplice
import BTnSSBMS.HWLowCopies

/-! All zero-class copies preserve BN. They remain in one outer forest;
every repeated root has the same complete pruned block, and all other
heads are strictly above that root's zero-value. -/
namespace BTnSSBMS.Source

theorem copies_zero_BN {d : Nat} {context : ParentContext}
    {a : List Nat} {hs : Forests (List Nat)} {rest : NumericalExpr} {site : HoleSite}
    (legal : FiniteLegal d context (.cons a hs rest)) (ordered : BN d context (.cons a hs rest))
    (found : holeSite d context none 0 (.cons a hs rest) = some site) (positive : 0 < d)
    (selected : (Parents.label d site.context site.terminal).parents[0]?.join = some context.length)
    (count phase : Nat) (target : ParentContext) (visible : List Nat)
    (scope : ShiftView d (context ++ [Parents.label d context a])
      (target ++ [Parents.label d target (shift a 0 [] phase)]) visible
      (List.replicate context.length 0 ++ [0]) context.length 0 [] phase) :
    BN d target (copies (mark 0 context.length (List.replicate context.length 0)
      (Parents.annotate d context (.cons a hs rest))) 0 [] none count phase) := by
  induction count generalizing phase target visible with
  | zero => rw [copies]; trivial
  | succ count ih =>
    have later := Parents.label_parent_bound d site.context site.terminal 0 context.length selected
    have nonempty : rest ≠ .nil := (holeSite_root_not_terminal found later).resolve_right (fun h => h rfl)
    have coordinates := holeSite_root_coordinates found later
    have takeRoot := holeSite_root_take found later
    have sourceHole := (holeSite_finiteLegal 0 (.cons a hs rest) legal
      (by intro bound impossible; cases impossible) found).1
    obtain ⟨targetSite, targetFound, holeView⟩ := copied_root_holeSite scope hs rest legal 0 found later
    obtain ⟨holeVisible, holeHistory, atHole, terminalEq, _⟩ := holeView
    have width : (site.context[context.length]?.getD default).coordinates.length = d := by
      rw [coordinates]; exact legal.1
    have next := atHole.restart site.terminal sourceHole.1 sourceHole.2.1 width positive selected
      (by intro j impossible; omega)
    dsimp only at next
    rw [takeRoot, coordinates] at next
    have replacement := ih (phase + 1) targetSite.context
      (holeVisible.take context.length ++ [targetSite.context.length]) next
    have replacementFinite := copies_low_finiteLegal legal found (.inr rfl) positive selected []
      (by intro j impossible; omega) count (phase + 1) targetSite.context
      (holeVisible.take context.length ++ [targetSite.context.length]) next
    rw [shift_empty] at replacementFinite
    have strict := Parents.label_root_lower_value atHole.sourceCoherent atHole.sourceValid
      site.terminal positive selected (Nat.le_refl 0)
    change (site.context[context.length]?.getD default).coordinates[0]?.getD 0 < site.terminal[0]?.getD 0 at strict
    rw [coordinates] at strict
    have headLess := low_shift_next_lt [] phase (by rw [legal.1]; exact positive)
      (by rw [sourceHole.1]; exact positive) (by intro j impossible; omega) strict
    rw [shift_empty, shift_empty] at headLess
    rw [shift_empty] at terminalEq
    rw [← terminalEq] at headLess
    let part := mark 0 context.length (List.replicate context.length 0)
      (Parents.annotate d context (.cons a hs rest))
    let replacementTerm := copies part 0 [] none count (phase + 1)
    have erase : part.map Prod.fst = .cons a hs rest := by
      simp only [part, mark_erase, Parents.annotate_erase]
    have lower : replacementTerm.compare (listCompare Ord.compare)
        (.cons targetSite.terminal targetSite.attached .nil) = .lt := by
      cases count with
      | zero => simp only [replacementTerm, copies, Expr.compare]
      | succ count =>
        rw [show replacementTerm = splice 0 (copies part 0 [] none count (phase + 1 + 1)) (.cons a hs rest) from
          (zero_copies_succ part count (phase + 1)).trans (congrArg (splice 0 _) erase),
          splice_cons_tail 0 _ a hs rest nonempty]
        simp only [Expr.compare, headLess]
    have floor : TerminalFloor a replacementTerm := by
      cases count with
      | zero => simp only [replacementTerm, copies, TerminalFloor]
      | succ count =>
        change TerminalFloor a (copies part 0 [] none (count + 1) (phase + 1))
        rw [zero_copies_succ, erase, splice_cons_tail 0 _ a hs rest nonempty]
        refine ⟨rfl, ?_⟩
        intro col member
        apply replacementFinite.2 col
        change col ∈ labels (copies part 0 [] none (count + 1) (phase + 1))
        rwa [zero_copies_succ, erase, splice_cons_tail 0 _ a hs rest nonempty]
    have fullCoherent := Parents.coherent_append_label atHole.sourceCoherent site.terminal
    have fullValid := Parents.context_valid_append_label d site.context atHole.sourceValid site.terminal
    have path : Parents.Ancestor (site.context ++ [Parents.label d site.context site.terminal]) 0
        context.length site.context.length := Parents.Ancestor.up (by rw [Parents.append_label_parent]; exact selected) (.refl _)
    have above := holeSite_root_tail_above 0 rest found fullCoherent fullValid positive path
    have wholeLegal := copied_root_finiteLegal scope positive hs rest legal
    have wholeBN := selected_root_copied_BN
      (scope.sourceCoherent.restrict (List.prefix_append _ _))
      (scope.sourceValid.restrict (List.prefix_append _ _)) legal ordered found positive selected scope
    rw [copied_empty] at wholeLegal wholeBN targetFound
    have blocks : ExprLE (rootBlock replacementTerm) (dropLast (.cons a hs rest)) := by
      cases count with
      | zero => exact ExprLE.nil _
      | succ count =>
        change ExprLE (rootBlock (copies part 0 [] none (count + 1) (phase + 1))) _
        rw [zero_copies_rootBlock erase nonempty above]
        exact .refl _
    have atTerminal := holeSite_zero_data (.cons a hs rest) targetFound
    rw [zero_copies_succ]
    change BN d target (splice 0 replacementTerm (part.map Prod.fst))
    rw [erase]
    exact wholeBN.splice_zero_root positive wholeLegal nonempty above atTerminal.2
      (by rw [← atTerminal.1]; exact replacement)
      (by rw [← atTerminal.1]; exact replacementFinite.1) (.of_lt lower) floor blocks

theorem initial_copies_zero_BN {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    {a : List Nat} {hs : Forests (List Nat)} {rest : NumericalExpr} {site : HoleSite}
    (legal : FiniteLegal d context (.cons a hs rest)) (ordered : BN d context (.cons a hs rest))
    (found : holeSite d context none 0 (.cons a hs rest) = some site) (positive : 0 < d)
    (selected : (Parents.label d site.context site.terminal).parents[0]?.join = some context.length)
    (count : Nat) :
    BN d site.context (copies (mark 0 context.length (List.replicate context.length 0)
      (Parents.annotate d context (.cons a hs rest))) 0 [] none count 1) := by
  have state := holeSite_contexts coherent valid 0 (.cons a hs rest) found
  have sourceHole := (holeSite_finiteLegal 0 (.cons a hs rest) legal
    (by intro bound impossible; cases impossible) found).1
  have unit := sourceHole.2.1.restrict
    (Parents.context_valid_append_label d site.context state.2 site.terminal) (List.prefix_append _ _)
  have later := Parents.label_parent_bound d site.context site.terminal 0 context.length selected
  have coordinates := holeSite_root_coordinates found later
  have takeRoot := holeSite_root_take found later
  have width : (site.context[context.length]?.getD default).coordinates.length = d := by
    rw [coordinates]; exact legal.1
  have scope := first_copy_shiftView state.1 state.2 unit site.terminal sourceHole.2.1 positive selected width
  dsimp only at scope
  rw [takeRoot, coordinates] at scope
  exact copies_zero_BN legal ordered found positive selected count 1 site.context _ scope

end BTnSSBMS.Source
