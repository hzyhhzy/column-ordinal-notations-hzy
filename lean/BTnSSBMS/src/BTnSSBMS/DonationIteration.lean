import BTnSSBMS.DonationMaterial

/-!
All finite highest-class iterations, including the previous-phase
donation and the literal setFirstForests operation. The root precedes a
nonempty outer tail, so it is not an owner of the terminal hole. Connecting
this finite condition to the actual highest-key search is a later step.
-/
namespace BTnSSBMS.Source

theorem copies_high_finiteLegal {d : Nat} {context : ParentContext}
    {a : List Nat} {hs : Forests (List Nat)} {rest : NumericalExpr} {depth : Nat} {site : HoleSite}
    (legal : FiniteLegal d context (.cons a hs rest))
    (found : holeSite d context none depth (.cons a hs rest) = some site)
    (nonowned : rest ≠ .nil) (positive : 0 < d) (later : context.length < site.context.length)
    (path : Parents.Ancestor (site.context ++ [Parents.label d site.context site.terminal])
      (d - 1) context.length site.context.length)
    (delta : List Nat)
    (difference : ∀ j, j < d → site.terminal[j]?.getD 0 = a[j]?.getD 0 + delta[j]?.getD 0)
    (count phase : Nat) (positivePhase : 0 < phase) (target : ParentContext) (visible : List Nat)
    (scope : ShiftView d (context ++ [Parents.label d context a])
      (target ++ [Parents.label d target (shift a d delta phase)]) visible
      (List.replicate context.length 0 ++ [d]) context.length d delta phase)
    (donated : FiniteLegalForests d (target ++ [Parents.label d target (shift a d delta phase)])
      ((shift a d delta phase)[0]?.getD 0)
      (ascendForests (donationAt d context.length site) .nil none delta (phase - 1))) :
    let result := copies (mark d context.length (List.replicate context.length 0)
      (Parents.annotate d context (.cons a hs rest))) depth delta (some (donationAt d context.length site)) count phase
    FiniteLegal d target result ∧
      ∀ col ∈ labels result, (shift a d delta phase)[0]?.getD 0 ≤ col[0]?.getD 0 := by
  dsimp only
  induction count generalizing phase target visible with
  | zero => exact ⟨trivial, by simp [copies, labels]⟩
  | succ count ih =>
    have rootCoordinates := holeSite_root_coordinates found later
    have rootTake := holeSite_root_take found later
    have sourceHole := (holeSite_finiteLegal depth (.cons a hs rest) legal
      (by intro bound impossible; cases impossible) found).1
    have wholeLegal := copied_root_finiteLegal scope positive hs rest legal
    obtain ⟨targetSite, targetFound, holeView⟩ := copied_root_holeSite scope hs rest legal depth found later
    obtain ⟨holeVisible, holeHistory, atHole, terminalEq, attachedEq⟩ := holeView
    have width : (site.context[context.length]?.getD default).coordinates.length = d := by
      rw [rootCoordinates]; exact legal.1
    have deltaEq : ∀ j, j < d → site.terminal[j]?.getD 0 =
        Parents.reading site.context j context.length + delta[j]?.getD 0 := by
      intro j room
      change site.terminal[j]?.getD 0 =
        (site.context[context.length]?.getD default).coordinates[j]?.getD 0 + delta[j]?.getD 0
      rw [rootCoordinates]
      exact difference j room
    have next := atHole.restart_high positive site.terminal sourceHole.1 sourceHole.2.1 width path deltaEq
    dsimp only at next
    rw [rootTake, rootCoordinates] at next
    have nextDonation := atHole.donationAt_finiteLegal positive sourceHole width path deltaEq
    dsimp only at nextDonation
    rw [rootCoordinates] at nextDonation
    have replacement := ih (phase + 1) (by omega) targetSite.context
      (holeVisible.take context.length ++ [targetSite.context.length]) next
      (by simpa only [Nat.add_sub_cancel] using nextDonation)
    have threshold := Keys.threshold_at_top_ancestor atHole.sourceCoherent atHole.sourceValid
      atHole.historyCorrect atHole.historyLength atHole.afterRoot positive site.terminal path
    have same : shift a d delta (phase + 1) = targetSite.terminal := by
      rw [terminalEq, threshold]
      exact top_shift_eq d a site.terminal delta phase legal.1 sourceHole.1 difference
    have targetHole := holeSite_finiteLegal depth
      (copied d context.length d delta phase context (List.replicate context.length 0) (.cons a hs rest))
      wholeLegal (by intro bound impossible; cases impossible) targetFound
    have fits : FitsOwner targetSite.owner
        (copies (mark d context.length (List.replicate context.length 0)
          (Parents.annotate d context (.cons a hs rest))) depth delta
          (some (donationAt d context.length site)) count (phase + 1)) := by
      intro bound owner col member
      have headAbove := targetHole.2.head bound owner
      rw [← same] at headAbove
      exact Nat.lt_of_lt_of_le headAbove (replacement.2 col member)
    have legalResult := splice_finiteLegal depth
      (copied d context.length d delta phase context (List.replicate context.length 0) (.cons a hs rest))
      (copies (mark d context.length (List.replicate context.length 0)
        (Parents.annotate d context (.cons a hs rest))) depth delta
        (some (donationAt d context.length site)) count (phase + 1))
      wholeLegal (by intro bound impossible; cases impossible) targetFound replacement.1 fits
    have originalCoherent := Parents.coherent_append_label atHole.sourceCoherent site.terminal
    have originalZero := path.lower_row originalCoherent (by omega : d - 1 < d) (Nat.zero_le _)
    have tailAbove := holeSite_root_tail_above depth rest found originalCoherent
      (Parents.context_valid_append_label d site.context atHole.sourceValid site.terminal) positive originalZero
    have materialLower := copied_root_lower scope positive hs rest legal tailAbove
    have nextHigher : (shift a d delta phase)[0]?.getD 0 ≤ (shift a d delta (phase + 1))[0]?.getD 0 := by
      rw [shift_value _ _ _ _ 0 (by rw [legal.1]; exact positive),
        shift_value _ _ _ _ 0 (by rw [legal.1]; exact positive)]
      simp only [if_pos positive, Nat.mul_succ]
      omega
    have allLower := splice_outer_lower depth
      (copied d context.length d delta phase context (List.replicate context.length 0) (.cons a hs rest))
      (copies (mark d context.length (List.replicate context.length 0)
        (Parents.annotate d context (.cons a hs rest))) depth delta
        (some (donationAt d context.length site)) count (phase + 1))
      ((shift a d delta phase)[0]?.getD 0) materialLower
      (by intro col member; exact Nat.le_trans nextHigher (replacement.2 col member))
    have headPositive : ∀ j, j < d → 0 < (shift a d delta phase)[j]?.getD 0 := by
      intro j room
      have below := (path.lower_row originalCoherent (by omega : d - 1 < d) (by omega : j ≤ d - 1)).reading_lt
        originalCoherent (by omega)
      rw [Parents.reading_append_label,
        ← Parents.reading_prefix (List.prefix_append site.context _) j context.length later] at below
      change (site.context[context.length]?.getD default).coordinates[j]?.getD 0 < site.terminal[j]?.getD 0 at below
      rw [rootCoordinates] at below
      have positiveDelta : 0 < delta[j]?.getD 0 := by have equation := difference j room; omega
      have product := Nat.mul_pos positiveDelta positivePhase
      rw [shift_value _ _ _ _ j (by rw [legal.1]; exact room), if_pos room]
      omega
    have shape : ∃ ks t, splice depth
        (copies (mark d context.length (List.replicate context.length 0)
          (Parents.annotate d context (.cons a hs rest))) depth delta
          (some (donationAt d context.length site)) count (phase + 1))
        (copied d context.length d delta phase context (List.replicate context.length 0) (.cons a hs rest)) =
        .cons (shift a d delta phase) ks t := by
      rw [copied_at_root, splice_cons_tail depth _ _ _ _ (by
        intro empty
        exact nonowned ((copied_nil_iff ..).mp empty))]
      exact ⟨_, _, rfl⟩
    obtain ⟨ks, t, shape⟩ := shape
    rw [copies, ascendReplace_splice]
    constructor
    · change FiniteLegal d target (setFirstForests _ (splice depth _
        (copied d context.length d delta phase context (List.replicate context.length 0) (.cons a hs rest))))
      rw [shape]
      apply setFirstForests_finiteLegal _ headPositive donated
      rw [← shape]
      exact legalResult.1
    · rw [labels_setFirstForests]
      exact allLower

/-- The first high-class root view and donation are obtained from the
original coherent finite template. Neither is an input assumption here. -/
theorem initial_copies_high_finiteLegal {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    {a : List Nat} {hs : Forests (List Nat)} {rest : NumericalExpr} {depth : Nat} {site : HoleSite}
    (legal : FiniteLegal d context (.cons a hs rest))
    (found : holeSite d context none depth (.cons a hs rest) = some site)
    (nonowned : rest ≠ .nil) (positive : 0 < d) (later : context.length < site.context.length)
    (path : Parents.Ancestor (site.context ++ [Parents.label d site.context site.terminal])
      (d - 1) context.length site.context.length) (count : Nat) :
    let delta := (List.range d).map (fun j => site.terminal[j]?.getD 0 - a[j]?.getD 0)
    let result := copies (mark d context.length (List.replicate context.length 0)
      (Parents.annotate d context (.cons a hs rest))) depth delta (some (donationAt d context.length site)) count 1
    FiniteLegal d site.context result ∧
      ∀ col ∈ labels result, site.terminal[0]?.getD 0 ≤ col[0]?.getD 0 := by
  dsimp only
  let delta := (List.range d).map (fun j => site.terminal[j]?.getD 0 - a[j]?.getD 0)
  have sourceState := holeSite_contexts coherent valid depth (.cons a hs rest) found
  have sourceHole := (holeSite_finiteLegal depth (.cons a hs rest) legal
    (by intro bound impossible; cases impossible) found).1
  have unit := sourceHole.2.1.restrict
    (Parents.context_valid_append_label d site.context sourceState.2 site.terminal) (List.prefix_append ..)
  have rootCoordinates := holeSite_root_coordinates found later
  have rootTake := holeSite_root_take found later
  have width : (site.context[context.length]?.getD default).coordinates.length = d := by
    rw [rootCoordinates]; exact legal.1
  have difference : ∀ j, j < d → site.terminal[j]?.getD 0 = a[j]?.getD 0 + delta[j]?.getD 0 := by
    intro j room
    simp only [delta, List.getElem?_map, List.getElem?_range room, Option.map_some, Option.getD_some]
    have fullCoherent := Parents.coherent_append_label sourceState.1 site.terminal
    have smaller := (path.lower_row fullCoherent (by omega : d - 1 < d) (by omega : j ≤ d - 1)).reading_lt
      fullCoherent (by omega)
    rw [Parents.reading_append_label,
      ← Parents.reading_prefix (List.prefix_append site.context _) j context.length later] at smaller
    change (site.context[context.length]?.getD default).coordinates[j]?.getD 0 < site.terminal[j]?.getD 0 at smaller
    rw [rootCoordinates] at smaller
    omega
  have deltaEq : ∀ j, j < d → site.terminal[j]?.getD 0 =
      Parents.reading site.context j context.length + delta[j]?.getD 0 := by
    intro j room
    change site.terminal[j]?.getD 0 =
      (site.context[context.length]?.getD default).coordinates[j]?.getD 0 + delta[j]?.getD 0
    rw [rootCoordinates]
    exact difference j room
  have zero := ShiftView.zero sourceState.1 sourceState.2 unit context.length d delta later (Nat.le_refl d)
  have scope := zero.restart_high positive site.terminal sourceHole.1 sourceHole.2.1 width path deltaEq
  dsimp only at scope
  rw [rootTake, rootCoordinates] at scope
  have headAtOne := top_shift_eq d a site.terminal delta 0 legal.1 sourceHole.1 difference
  rw [shift_zero] at headAtOne
  have donated : FiniteLegalForests d (site.context ++ [Parents.label d site.context (shift a d delta 1)])
      ((shift a d delta 1)[0]?.getD 0)
      (ascendForests (donationAt d context.length site) .nil none delta (1 - 1)) := by
    rw [headAtOne]
    change FiniteLegalForests d (site.context ++ [Parents.label d site.context site.terminal])
      (site.terminal[0]?.getD 0) (ascendForests (donationAt d context.length site) .nil none delta 0)
    rw [donationAt_zero]
    exact sourceHole.2.2.2.1.dropLast
  have result := copies_high_finiteLegal legal found nonowned positive later path delta difference count 1
    (by decide) site.context _ scope donated
  rw [headAtOne] at result
  exact result

/-- All high-class copies, including each donated first list, are
installed at the original terminal with the zero-phase outer prefix.
This still concerns a rooted template, not root extraction from expand?. -/
theorem rooted_high_expansion_finiteLegal {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    {a : List Nat} {hs : Forests (List Nat)} {rest : NumericalExpr} {depth : Nat} {site : HoleSite}
    (legal : FiniteLegal d context (.cons a hs rest))
    (found : holeSite d context none depth (.cons a hs rest) = some site)
    (nonowned : rest ≠ .nil) (positive : 0 < d) (later : context.length < site.context.length)
    (path : Parents.Ancestor (site.context ++ [Parents.label d site.context site.terminal])
      (d - 1) context.length site.context.length) (count : Nat) :
    let delta := (List.range d).map (fun j => site.terminal[j]?.getD 0 - a[j]?.getD 0)
    let part := mark d context.length (List.replicate context.length 0)
      (Parents.annotate d context (.cons a hs rest))
    FiniteLegal d context (ascendReplace part
      (copies part depth delta (some (donationAt d context.length site)) count 1) (some depth) delta 0) := by
  dsimp only
  let delta := (List.range d).map (fun j => site.terminal[j]?.getD 0 - a[j]?.getD 0)
  let part := mark d context.length (List.replicate context.length 0)
    (Parents.annotate d context (.cons a hs rest))
  have computed := initial_copies_high_finiteLegal coherent valid legal found nonowned positive later path count
  have sourceHole := holeSite_finiteLegal depth (.cons a hs rest) legal
    (by intro bound impossible; cases impossible) found
  have fits : FitsOwner site.owner (copies part depth delta (some (donationAt d context.length site)) count 1) := by
    intro bound owner col member
    exact Nat.lt_of_lt_of_le (sourceHole.2.head bound owner) (computed.2 col member)
  have result := (splice_finiteLegal depth (.cons a hs rest)
    (copies part depth delta (some (donationAt d context.length site)) count 1)
    legal (by intro bound impossible; cases impossible) found computed.1 fits).1
  rw [ascendReplace_splice]
  have identity : part.map (fun a => shift a.1 a.2 delta 0) = .cons a hs rest := by
    simp only [part, shift_zero, mark_erase, Parents.annotate_erase]
  rw [identity]
  exact result

end BTnSSBMS.Source
