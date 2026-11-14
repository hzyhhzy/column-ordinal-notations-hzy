import BTnSSBMS.CopyRoot

/-!
Induction over the actual frozen copies function. In the positive low
numerical classes the next copy's first coordinate equals the virtual
terminal's first coordinate. The zero class is covered when the hole and
root are in the same forest. No legality or separation of the replacement
is assumed.
-/
namespace BTnSSBMS.Source

theorem splice_outer_lower (depth : Nat) (e replacement : NumericalExpr) (bound : Nat)
    (old : ∀ a ∈ labels e, bound ≤ a[0]?.getD 0)
    (new : ∀ a ∈ labels replacement, bound ≤ a[0]?.getD 0) :
    ∀ a ∈ labels (splice depth replacement e), bound ≤ a[0]?.getD 0 := by
  cases e with
  | nil => simp [splice, labels]
  | cons a hs rest =>
    cases rest with
    | nil =>
      cases depth with
      | zero => rw [splice]; exact new
      | succ k =>
        rw [splice]
        intro col member
        simp only [labels, List.mem_cons, List.not_mem_nil, or_false] at member
        subst col
        exact old a (by simp [labels])
    | cons b ks t =>
      rw [splice]
      intro col member
      simp only [labels, List.mem_cons] at member
      rcases member with rfl | later
      · exact old col (by simp [labels])
      · exact splice_outer_lower depth (.cons b ks t) replacement bound
          (by
            intro col member
            exact old col (List.mem_cons_of_mem a member)) new col later

/-- All finite iterations of a rooted low-class copy are legal when the
class is positive or root and terminal belong to the same forest.
The computed terminal and real numerical parent select the seam. The
replacement's legality, its entering view, and its owner fence are derived
inside the induction, rather than supplied as separate hypotheses. -/
theorem copies_low_finiteLegal {d cap : Nat} {context : ParentContext}
    {a : List Nat} {hs : Forests (List Nat)} {rest : NumericalExpr} {depth : Nat} {site : HoleSite}
    (legal : FiniteLegal d context (.cons a hs rest))
    (found : holeSite d context none depth (.cons a hs rest) = some site)
    (seam : 0 < cap ∨ depth = 0) (room : cap < d)
    (selected : (Parents.label d site.context site.terminal).parents[cap]?.join = some context.length)
    (delta : List Nat)
    (difference : ∀ j, j < cap → site.terminal[j]?.getD 0 = a[j]?.getD 0 + delta[j]?.getD 0)
    (count phase : Nat) (target : ParentContext) (visible : List Nat)
    (scope : ShiftView d (context ++ [Parents.label d context a])
      (target ++ [Parents.label d target (shift a cap delta phase)]) visible
      (List.replicate context.length 0 ++ [cap]) context.length cap delta phase) :
    let result := copies (mark cap context.length (List.replicate context.length 0)
      (Parents.annotate d context (.cons a hs rest))) depth delta none count phase
    FiniteLegal d target result ∧
      ∀ col ∈ labels result, (shift a cap delta phase)[0]?.getD 0 ≤ col[0]?.getD 0 := by
  dsimp only
  induction count generalizing phase target visible with
  | zero => exact ⟨trivial, by simp [copies, labels]⟩
  | succ count ih =>
    have positive : 0 < d := by omega
    have later := Parents.label_parent_bound d site.context site.terminal cap context.length selected
    have rootCoordinates := holeSite_root_coordinates found later
    have rootTake := holeSite_root_take found later
    have sourceHole := (holeSite_finiteLegal depth (.cons a hs rest) legal
      (by intro bound impossible; cases impossible) found).1
    have wholeLegal := copied_root_finiteLegal scope positive hs rest legal
    obtain ⟨targetSite, targetFound, holeView⟩ := copied_root_holeSite scope hs rest legal depth found later
    obtain ⟨holeVisible, holeHistory, atHole, terminalEq, attachedEq⟩ := holeView
    have width : (site.context[context.length]?.getD default).coordinates.length = d := by
      rw [rootCoordinates]; exact legal.1
    have deltaEq : ∀ j, j < cap → site.terminal[j]?.getD 0 =
        Parents.reading site.context j context.length + delta[j]?.getD 0 := by
      intro j below
      change site.terminal[j]?.getD 0 =
        (site.context[context.length]?.getD default).coordinates[j]?.getD 0 + delta[j]?.getD 0
      rw [rootCoordinates]
      exact difference j below
    have next := atHole.restart site.terminal sourceHole.1 sourceHole.2.1 width room selected deltaEq
    dsimp only at next
    rw [rootTake, rootCoordinates] at next
    have replacement := ih (phase + 1) targetSite.context (holeVisible.take context.length ++ [targetSite.context.length]) next
    have targetHole := holeSite_finiteLegal depth
      (copied d context.length cap delta phase context (List.replicate context.length 0) (.cons a hs rest))
      wholeLegal (by intro bound impossible; cases impossible) targetFound
    have fits : FitsOwner targetSite.owner
        (copies (mark cap context.length (List.replicate context.length 0)
          (Parents.annotate d context (.cons a hs rest))) depth delta none count (phase + 1)) := by
      intro bound owner col member
      rcases seam with positiveCap | sameForest
      · have threshold := Keys.threshold_at_selected_root atHole.sourceCoherent atHole.sourceValid
          atHole.historyCorrect atHole.historyLength atHole.afterRoot room site.terminal selected
        have values := atHole.next_head_values site.terminal sourceHole.1 width room deltaEq
        have sameZero : (shift a cap delta (phase + 1))[0]?.getD 0 = targetSite.terminal[0]?.getD 0 := by
          rw [terminalEq, threshold]
          simpa only [rootCoordinates] using values.1 0 positiveCap
        have headAbove := targetHole.2.head bound owner
        rw [← sameZero] at headAbove
        exact Nat.lt_of_lt_of_le headAbove (replacement.2 col member)
      · subst depth
        have noOwner := holeSite_zero_owner _ targetFound
        rw [noOwner] at owner
        cases owner
    have legalResult := splice_finiteLegal depth
      (copied d context.length cap delta phase context (List.replicate context.length 0) (.cons a hs rest))
      (copies (mark cap context.length (List.replicate context.length 0)
        (Parents.annotate d context (.cons a hs rest))) depth delta none count (phase + 1))
      wholeLegal (by intro bound impossible; cases impossible) targetFound replacement.1 fits
    have originalPath : Parents.Ancestor (site.context ++ [Parents.label d site.context site.terminal])
        cap context.length site.context.length :=
      .up (by rw [Parents.append_label_parent]; exact selected) (.refl _)
    have originalZero := originalPath.lower_row
      (Parents.coherent_append_label atHole.sourceCoherent site.terminal) room (Nat.zero_le cap)
    have tailAbove := holeSite_root_tail_above depth rest found
      (Parents.coherent_append_label atHole.sourceCoherent site.terminal)
      (Parents.context_valid_append_label d site.context atHole.sourceValid site.terminal) positive originalZero
    have materialLower := copied_root_lower scope positive hs rest legal tailAbove
    have nextHigher : (shift a cap delta phase)[0]?.getD 0 ≤ (shift a cap delta (phase + 1))[0]?.getD 0 := by
      rw [shift_value _ _ _ _ 0 (by rw [legal.1]; exact positive),
        shift_value _ _ _ _ 0 (by rw [legal.1]; exact positive)]
      by_cases active : 0 < cap
      · simp only [if_pos active, Nat.mul_succ]; omega
      · simp only [if_neg active]; exact Nat.le_refl _
    have allLower := splice_outer_lower depth
      (copied d context.length cap delta phase context (List.replicate context.length 0) (.cons a hs rest))
      (copies (mark cap context.length (List.replicate context.length 0)
        (Parents.annotate d context (.cons a hs rest))) depth delta none count (phase + 1))
      ((shift a cap delta phase)[0]?.getD 0) materialLower
      (by intro col member; exact Nat.le_trans nextHigher (replacement.2 col member))
    rw [copies, ascendReplace_splice]
    exact ⟨legalResult.1, allLower⟩

/-- The initial view and difference vector are constructed from the
computed numerical root. This theorem has no transport-state premise. -/
theorem initial_copies_low_finiteLegal {d cap : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    {a : List Nat} {hs : Forests (List Nat)} {rest : NumericalExpr} {depth : Nat} {site : HoleSite}
    (legal : FiniteLegal d context (.cons a hs rest))
    (found : holeSite d context none depth (.cons a hs rest) = some site)
    (seam : 0 < cap ∨ depth = 0) (room : cap < d)
    (selected : (Parents.label d site.context site.terminal).parents[cap]?.join = some context.length)
    (count : Nat) :
    let delta := (List.range cap).map (fun j => site.terminal[j]?.getD 0 - a[j]?.getD 0)
    let result := copies (mark cap context.length (List.replicate context.length 0)
      (Parents.annotate d context (.cons a hs rest))) depth delta none count 1
    FiniteLegal d site.context result ∧
      ∀ col ∈ labels result, (shift a cap delta 1)[0]?.getD 0 ≤ col[0]?.getD 0 := by
  dsimp only
  have sourceState := holeSite_contexts coherent valid depth (.cons a hs rest) found
  have sourceHole := (holeSite_finiteLegal depth (.cons a hs rest) legal
    (by intro bound impossible; cases impossible) found).1
  have unit := sourceHole.2.1.restrict
    (Parents.context_valid_append_label d site.context sourceState.2 site.terminal) (List.prefix_append ..)
  have later := Parents.label_parent_bound d site.context site.terminal cap context.length selected
  have rootCoordinates := holeSite_root_coordinates found later
  have rootTake := holeSite_root_take found later
  have width : (site.context[context.length]?.getD default).coordinates.length = d := by
    rw [rootCoordinates]; exact legal.1
  have scope := first_copy_shiftView sourceState.1 sourceState.2 unit site.terminal sourceHole.2.1 room selected width
  dsimp only at scope
  rw [rootTake, rootCoordinates] at scope
  apply copies_low_finiteLegal legal found seam room selected _ _ count 1 site.context
    (List.range context.length ++ [site.context.length]) scope
  intro j below
  simp only [List.getElem?_map, List.getElem?_range below, Option.map_some, Option.getD_some]
  have smaller := Parents.label_root_lower_value sourceState.1 sourceState.2 site.terminal room selected
    (by omega : j ≤ cap)
  change (site.context[context.length]?.getD default).coordinates[j]?.getD 0 < site.terminal[j]?.getD 0 at smaller
  rw [rootCoordinates] at smaller
  omega

/-- Install the entire computed repeated tail in the original rooted
template. This checks the first outer splice as well as every recursive
copy, with the original zero-phase prefix left unchanged. -/
theorem rooted_low_expansion_finiteLegal {d cap : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    {a : List Nat} {hs : Forests (List Nat)} {rest : NumericalExpr} {depth : Nat} {site : HoleSite}
    (legal : FiniteLegal d context (.cons a hs rest))
    (found : holeSite d context none depth (.cons a hs rest) = some site)
    (seam : 0 < cap ∨ depth = 0) (room : cap < d)
    (selected : (Parents.label d site.context site.terminal).parents[cap]?.join = some context.length)
    (count : Nat) :
    let delta := (List.range cap).map (fun j => site.terminal[j]?.getD 0 - a[j]?.getD 0)
    let part := mark cap context.length (List.replicate context.length 0)
      (Parents.annotate d context (.cons a hs rest))
    FiniteLegal d context (ascendReplace part (copies part depth delta none count 1) (some depth) delta 0) := by
  dsimp only
  let delta := (List.range cap).map (fun j => site.terminal[j]?.getD 0 - a[j]?.getD 0)
  let part := mark cap context.length (List.replicate context.length 0)
    (Parents.annotate d context (.cons a hs rest))
  have computed := initial_copies_low_finiteLegal coherent valid legal found seam room selected count
  have fits : FitsOwner site.owner (copies part depth delta none count 1) := by
    intro bound owner col member
    rcases seam with positiveCap | sameForest
    · have sourceState := holeSite_contexts coherent valid depth (.cons a hs rest) found
      have later := Parents.label_parent_bound d site.context site.terminal cap context.length selected
      have rootCoordinates := holeSite_root_coordinates found later
      have width : (site.context[context.length]?.getD default).coordinates.length = d := by
        rw [rootCoordinates]; exact legal.1
      have values := shifted_copy_head_values sourceState.1 sourceState.2 site.terminal room selected width
      dsimp only at values
      rw [rootCoordinates] at values
      have first := values.1 0 positiveCap
      have sourceHole := holeSite_finiteLegal depth (.cons a hs rest) legal
        (by intro bound impossible; cases impossible) found
      have above := sourceHole.2.head bound owner
      have lower := computed.2 col member
      rw [first] at lower
      exact Nat.lt_of_lt_of_le above lower
    · subst depth
      have noOwner := holeSite_zero_owner _ found
      rw [noOwner] at owner
      cases owner
  have result := (splice_finiteLegal depth (.cons a hs rest) (copies part depth delta none count 1)
    legal (by intro bound impossible; cases impossible) found computed.1 fits).1
  rw [ascendReplace_splice]
  have identity : part.map (fun a => shift a.1 a.2 delta 0) = .cons a hs rest := by
    simp only [part, shift_zero, mark_erase, Parents.annotate_erase]
  rw [identity]
  exact result

end BTnSSBMS.Source
