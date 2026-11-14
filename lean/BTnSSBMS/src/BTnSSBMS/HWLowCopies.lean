import BTnSSBMS.HWTransport

/-! All actual low-class iterations preserve hereditary forest order.
Every recursive entry is constructed at the copied terminal, rather than
assumed for later replicas. This includes the zero numerical class. -/
namespace BTnSSBMS.Source

theorem low_shift_next_lt {a terminal : List Nat} {cap : Nat} (delta : List Nat) (phase : Nat)
    (left : cap < a.length) (right : cap < terminal.length)
    (difference : ∀ j, j < cap → terminal[j]?.getD 0 = a[j]?.getD 0 + delta[j]?.getD 0)
    (strict : a[cap]?.getD 0 < terminal[cap]?.getD 0) :
    listCompare Ord.compare (shift a cap delta (phase + 1)) (shift terminal cap delta phase) = .lt := by
  apply columnCompare_lt_at _ _ cap (by rw [shift_width]; exact left) (by rw [shift_width]; exact right)
  · intro j before
    rw [shift_value _ _ _ _ j (by omega), shift_value _ _ _ _ j (by omega)]
    simp only [if_pos before, Nat.mul_succ, difference j before]
    omega
  · rw [shift_value _ _ _ _ cap left, shift_value _ _ _ _ cap right]
    simpa only [Nat.lt_irrefl, if_false, Nat.add_zero] using strict

theorem copies_low_HW {d cap : Nat} {context : ParentContext}
    {a : List Nat} {hs : Forests (List Nat)} {rest : NumericalExpr} {depth : Nat} {site : HoleSite}
    (legal : FiniteLegal d context (.cons a hs rest)) (ordered : HW (.cons a hs rest))
    (found : holeSite d context none depth (.cons a hs rest) = some site) (room : cap < d)
    (selected : (Parents.label d site.context site.terminal).parents[cap]?.join = some context.length)
    (delta : List Nat)
    (difference : ∀ j, j < cap → site.terminal[j]?.getD 0 = a[j]?.getD 0 + delta[j]?.getD 0)
    (count phase : Nat) (target : ParentContext) (visible : List Nat)
    (scope : ShiftView d (context ++ [Parents.label d context a])
      (target ++ [Parents.label d target (shift a cap delta phase)]) visible
      (List.replicate context.length 0 ++ [cap]) context.length cap delta phase) :
    HW (copies (mark cap context.length (List.replicate context.length 0)
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
    have threshold := Keys.threshold_at_selected_root atHole.sourceCoherent atHole.sourceValid
      atHole.historyCorrect atHole.historyLength atHole.afterRoot room site.terminal selected
    have strict := Parents.label_root_lower_value atHole.sourceCoherent atHole.sourceValid
      site.terminal room selected (Nat.le_refl cap)
    change (site.context[context.length]?.getD default).coordinates[cap]?.getD 0 < site.terminal[cap]?.getD 0 at strict
    rw [coordinates] at strict
    have headLess := low_shift_next_lt delta phase (by rw [legal.1]; exact room)
      (by rw [sourceHole.1]; exact room) difference strict
    rw [threshold] at terminalEq
    rw [← terminalEq] at headLess
    have lower : (copies (mark cap context.length (List.replicate context.length 0)
        (Parents.annotate d context (.cons a hs rest))) depth delta none count (phase + 1)).compare
        (listCompare Ord.compare) (.cons targetSite.terminal targetSite.attached .nil) = .lt := by
      cases count with
      | zero => simp only [copies, Expr.compare]
      | succ count =>
        obtain ⟨ks, tail, shape, _⟩ := marked_root_copies_first_head a hs rest delta none count (phase + 1)
          (holeSite_root_not_terminal found later)
        rw [shape]
        simp only [Expr.compare, headLess]
    have result := splice_HW depth
      (copied d context.length cap delta phase context (List.replicate context.length 0) (.cons a hs rest))
      _ (copied_root_HW scope hs rest legal ordered) replacement targetFound lower
    rw [copies, ascendReplace_splice]
    exact result

theorem initial_copies_low_HW {d cap : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    {a : List Nat} {hs : Forests (List Nat)} {rest : NumericalExpr} {depth : Nat} {site : HoleSite}
    (legal : FiniteLegal d context (.cons a hs rest)) (ordered : HW (.cons a hs rest))
    (found : holeSite d context none depth (.cons a hs rest) = some site) (room : cap < d)
    (selected : (Parents.label d site.context site.terminal).parents[cap]?.join = some context.length)
    (count : Nat) :
    let delta := (List.range cap).map (fun j => site.terminal[j]?.getD 0 - a[j]?.getD 0)
    HW (copies (mark cap context.length (List.replicate context.length 0)
      (Parents.annotate d context (.cons a hs rest))) depth delta none count 1) := by
  dsimp only
  have state := holeSite_contexts coherent valid depth (.cons a hs rest) found
  have sourceHole := (holeSite_finiteLegal depth (.cons a hs rest) legal
    (by intro bound impossible; cases impossible) found).1
  have unit := sourceHole.2.1.restrict
    (Parents.context_valid_append_label d site.context state.2 site.terminal) (List.prefix_append ..)
  have later := Parents.label_parent_bound d site.context site.terminal cap context.length selected
  have coordinates := holeSite_root_coordinates found later
  have takeRoot := holeSite_root_take found later
  have width : (site.context[context.length]?.getD default).coordinates.length = d := by
    rw [coordinates]; exact legal.1
  have scope := first_copy_shiftView state.1 state.2 unit site.terminal sourceHole.2.1 room selected width
  dsimp only at scope
  rw [takeRoot, coordinates] at scope
  apply copies_low_HW legal ordered found room selected _ _ count 1 site.context
    (List.range context.length ++ [site.context.length]) scope
  intro j before
  simp only [List.getElem?_map, List.getElem?_range before, Option.map_some, Option.getD_some]
  have smaller := Parents.label_root_lower_value state.1 state.2 site.terminal room selected (by omega : j ≤ cap)
  change (site.context[context.length]?.getD default).coordinates[j]?.getD 0 < site.terminal[j]?.getD 0 at smaller
  rw [coordinates] at smaller
  omega

end BTnSSBMS.Source
