import BTnSSBMS.BNSplice
import BTnSSBMS.HWLowCopies

/-! All positive low-class copies preserve BN. The hole entry,
replacement floor, ordinary-copy BN, and strict terminal comparison
are constructed at every iteration of the frozen copies function. -/
namespace BTnSSBMS.Source

theorem copies_positive_BN {d cap : Nat} {context : ParentContext}
    {a : List Nat} {hs : Forests (List Nat)} {rest : NumericalExpr} {depth : Nat} {site : HoleSite}
    (legal : FiniteLegal d context (.cons a hs rest)) (ordered : BN d context (.cons a hs rest))
    (found : holeSite d context none depth (.cons a hs rest) = some site)
    (positiveCap : 0 < cap) (room : cap < d)
    (selected : (Parents.label d site.context site.terminal).parents[cap]?.join = some context.length)
    (delta : List Nat)
    (difference : ∀ j, j < cap → site.terminal[j]?.getD 0 = a[j]?.getD 0 + delta[j]?.getD 0)
    (count phase : Nat) (target : ParentContext) (visible : List Nat)
    (scope : ShiftView d (context ++ [Parents.label d context a])
      (target ++ [Parents.label d target (shift a cap delta phase)]) visible
      (List.replicate context.length 0 ++ [cap]) context.length cap delta phase) :
    BN d target (copies (mark cap context.length (List.replicate context.length 0)
      (Parents.annotate d context (.cons a hs rest))) depth delta none count phase) := by
  induction count generalizing phase target visible with
  | zero => rw [copies]; trivial
  | succ count ih =>
    have later := Parents.label_parent_bound d site.context site.terminal cap context.length selected
    have coordinates := holeSite_root_coordinates found later
    have takeRoot := holeSite_root_take found later
    have sourceHole := (holeSite_finiteLegal depth (.cons a hs rest) legal
      (by intro bound impossible; cases impossible) found).1
    obtain ⟨targetSite, targetFound, holeView⟩ := copied_root_holeSite scope hs rest legal depth found later
    obtain ⟨holeVisible, holeHistory, atHole, terminalEq, _⟩ := holeView
    have width : (site.context[context.length]?.getD default).coordinates.length = d := by
      rw [coordinates]; exact legal.1
    have deltaEq : ∀ j, j < cap → site.terminal[j]?.getD 0 =
        Parents.reading site.context j context.length + delta[j]?.getD 0 := by
      intro j before
      change site.terminal[j]?.getD 0 =
        (site.context[context.length]?.getD default).coordinates[j]?.getD 0 + delta[j]?.getD 0
      rw [coordinates]
      exact difference j before
    have next := atHole.restart site.terminal sourceHole.1 sourceHole.2.1 width room selected deltaEq
    dsimp only at next
    rw [takeRoot, coordinates] at next
    have replacement := ih (phase + 1) targetSite.context
      (holeVisible.take context.length ++ [targetSite.context.length]) next
    have replacementFinite := copies_low_finiteLegal legal found (.inl positiveCap) room selected delta difference
      count (phase + 1) targetSite.context (holeVisible.take context.length ++ [targetSite.context.length]) next
    have threshold := Keys.threshold_at_selected_root atHole.sourceCoherent atHole.sourceValid
      atHole.historyCorrect atHole.historyLength atHole.afterRoot room site.terminal selected
    have values := atHole.next_head_values site.terminal sourceHole.1 width room deltaEq
    have sameZero : (shift a cap delta (phase + 1))[0]?.getD 0 = targetSite.terminal[0]?.getD 0 := by
      rw [terminalEq, threshold]
      simpa only [coordinates] using values.1 0 positiveCap
    have strict := Parents.label_root_lower_value atHole.sourceCoherent atHole.sourceValid
      site.terminal room selected (Nat.le_refl cap)
    change (site.context[context.length]?.getD default).coordinates[cap]?.getD 0 < site.terminal[cap]?.getD 0 at strict
    rw [coordinates] at strict
    have headLess := low_shift_next_lt delta phase (by rw [legal.1]; exact room)
      (by rw [sourceHole.1]; exact room) difference strict
    rw [threshold] at terminalEq
    rw [← terminalEq] at headLess
    have seam :
        (copies (mark cap context.length (List.replicate context.length 0)
          (Parents.annotate d context (.cons a hs rest))) depth delta none count (phase + 1)).compare
          (listCompare Ord.compare) (.cons targetSite.terminal targetSite.attached .nil) = .lt ∧
        TerminalFloor targetSite.terminal (copies (mark cap context.length (List.replicate context.length 0)
          (Parents.annotate d context (.cons a hs rest))) depth delta none count (phase + 1)) := by
      cases count with
      | zero => simp only [copies, Expr.compare, TerminalFloor, and_self]
      | succ count =>
        obtain ⟨ks, tail, shape, _⟩ := marked_root_copies_first_head a hs rest delta none count (phase + 1)
          (holeSite_root_not_terminal found later)
        rw [shape]
        refine ⟨by simp only [Expr.compare, headLess], sameZero, ?_⟩
        intro col member
        rw [← shape] at member
        rw [← sameZero]
        exact replacementFinite.2 col member
    have wholeLegal := copied_root_finiteLegal scope (by omega) hs rest legal
    have wholeBN := selected_root_copied_BN
      (scope.sourceCoherent.restrict (List.prefix_append _ _))
      (scope.sourceValid.restrict (List.prefix_append _ _)) legal ordered found room selected scope
    have result := splice_BN depth
      (copied d context.length cap delta phase context (List.replicate context.length 0) (.cons a hs rest))
      _ wholeBN (by omega) wholeLegal targetFound replacement replacementFinite.1 seam.1 seam.2
    rw [copies, ascendReplace_splice]
    exact result

theorem initial_copies_positive_BN {d cap : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    {a : List Nat} {hs : Forests (List Nat)} {rest : NumericalExpr} {depth : Nat} {site : HoleSite}
    (legal : FiniteLegal d context (.cons a hs rest)) (ordered : BN d context (.cons a hs rest))
    (found : holeSite d context none depth (.cons a hs rest) = some site) (positiveCap : 0 < cap) (room : cap < d)
    (selected : (Parents.label d site.context site.terminal).parents[cap]?.join = some context.length)
    (count : Nat) :
    let delta := (List.range cap).map (fun j => site.terminal[j]?.getD 0 - a[j]?.getD 0)
    BN d site.context (copies (mark cap context.length (List.replicate context.length 0)
      (Parents.annotate d context (.cons a hs rest))) depth delta none count 1) := by
  dsimp only
  have state := holeSite_contexts coherent valid depth (.cons a hs rest) found
  have sourceHole := (holeSite_finiteLegal depth (.cons a hs rest) legal
    (by intro bound impossible; cases impossible) found).1
  have unit := sourceHole.2.1.restrict
    (Parents.context_valid_append_label d site.context state.2 site.terminal) (List.prefix_append _ _)
  have later := Parents.label_parent_bound d site.context site.terminal cap context.length selected
  have coordinates := holeSite_root_coordinates found later
  have takeRoot := holeSite_root_take found later
  have width : (site.context[context.length]?.getD default).coordinates.length = d := by
    rw [coordinates]; exact legal.1
  have scope := first_copy_shiftView state.1 state.2 unit site.terminal sourceHole.2.1 room selected width
  dsimp only at scope
  rw [takeRoot, coordinates] at scope
  apply copies_positive_BN legal ordered found positiveCap room selected _ _ count 1 site.context
    (List.range context.length ++ [site.context.length]) scope
  intro j before
  simp only [List.getElem?_map, List.getElem?_range before, Option.map_some, Option.getD_some]
  have smaller := Parents.label_root_lower_value state.1 state.2 site.terminal room selected (by omega : j ≤ cap)
  change (site.context[context.length]?.getD default).coordinates[j]?.getD 0 < site.terminal[j]?.getD 0 at smaller
  rw [coordinates] at smaller
  omega

theorem initial_copies_positive_floor {d cap : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    {a : List Nat} {hs : Forests (List Nat)} {rest : NumericalExpr} {depth : Nat} {site : HoleSite}
    (legal : FiniteLegal d context (.cons a hs rest))
    (found : holeSite d context none depth (.cons a hs rest) = some site) (positiveCap : 0 < cap) (room : cap < d)
    (selected : (Parents.label d site.context site.terminal).parents[cap]?.join = some context.length)
    (count : Nat) :
    let delta := (List.range cap).map (fun j => site.terminal[j]?.getD 0 - a[j]?.getD 0)
    TerminalFloor site.terminal (copies (mark cap context.length (List.replicate context.length 0)
      (Parents.annotate d context (.cons a hs rest))) depth delta none count 1) := by
  dsimp only
  let delta := (List.range cap).map (fun j => site.terminal[j]?.getD 0 - a[j]?.getD 0)
  have state := holeSite_contexts coherent valid depth (.cons a hs rest) found
  have later := Parents.label_parent_bound d site.context site.terminal cap context.length selected
  have coordinates := holeSite_root_coordinates found later
  have width : (site.context[context.length]?.getD default).coordinates.length = d := by
    rw [coordinates]; exact legal.1
  have values := shifted_copy_head_values state.1 state.2 site.terminal room selected width
  dsimp only at values
  rw [coordinates] at values
  have sameZero : (shift a cap delta 1)[0]?.getD 0 = site.terminal[0]?.getD 0 := values.1 0 positiveCap
  have computed := initial_copies_low_finiteLegal coherent valid legal found (.inl positiveCap) room selected count
  cases count with
  | zero => rw [copies]; trivial
  | succ count =>
    obtain ⟨ks, tail, shape, _⟩ := marked_root_copies_first_head a hs rest delta none count 1
      (holeSite_root_not_terminal found later)
    rw [shape]
    refine ⟨sameZero, ?_⟩
    intro col member
    rw [← shape] at member
    rw [← sameZero]
    exact computed.2 col member

end BTnSSBMS.Source
