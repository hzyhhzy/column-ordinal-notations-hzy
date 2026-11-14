import BTnSSBMS.BNDonation

/-! All highest-class copies preserve BN, including each literal
previous-phase donation. The copied root has no later zero-parent
sibling even after its terminal hole has been replaced. -/
namespace BTnSSBMS.Source

theorem copies_high_BN {d : Nat} {context : ParentContext}
    {a : List Nat} {hs : Forests (List Nat)} {rest : NumericalExpr} {depth : Nat} {site : HoleSite}
    (legal : FiniteLegal d context (.cons a hs rest)) (ordered : BN d context (.cons a hs rest))
    (found : holeSite d context none depth (.cons a hs rest) = some site)
    (nonowned : rest ≠ .nil) (positive : 0 < d) (later : context.length < site.context.length)
    (attached : site.attached ≠ .nil)
    (path : Parents.Ancestor (site.context ++ [Parents.label d site.context site.terminal])
      (d - 1) context.length site.context.length)
    (delta : List Nat)
    (difference : ∀ j, j < d → site.terminal[j]?.getD 0 = a[j]?.getD 0 + delta[j]?.getD 0)
    (count phase : Nat) (target : ParentContext) (visible : List Nat)
    (scope : ShiftView d (context ++ [Parents.label d context a])
      (target ++ [Parents.label d target (shift a d delta phase)]) visible
      (List.replicate context.length 0 ++ [d]) context.length d delta phase)
    (donated : BNForests d (target ++ [Parents.label d target (shift a d delta phase)])
      (ascendForests (donationAt d context.length site) .nil none delta (phase - 1))) :
    BN d target (copies (mark d context.length (List.replicate context.length 0)
      (Parents.annotate d context (.cons a hs rest))) depth delta
      (some (donationAt d context.length site)) count phase) := by
  induction count generalizing phase target visible with
  | zero => rw [copies]; trivial
  | succ count ih =>
    have coordinates := holeSite_root_coordinates found later
    have takeRoot := holeSite_root_take found later
    have sourceHole := (holeSite_finiteLegal depth (.cons a hs rest) legal
      (by intro bound impossible; cases impossible) found).1
    have holeOrdered := ordered.holeSite depth (.cons a hs rest) found
    obtain ⟨targetSite, targetFound, holeView⟩ := copied_root_holeSite scope hs rest legal depth found later
    obtain ⟨holeVisible, holeHistory, atHole, terminalEq, attachedEq⟩ := holeView
    have width : (site.context[context.length]?.getD default).coordinates.length = d := by
      rw [coordinates]; exact legal.1
    have deltaEq : ∀ j, j < d → site.terminal[j]?.getD 0 =
        Parents.reading site.context j context.length + delta[j]?.getD 0 := by
      intro j room
      change site.terminal[j]?.getD 0 =
        (site.context[context.length]?.getD default).coordinates[j]?.getD 0 + delta[j]?.getD 0
      rw [coordinates]
      exact difference j room
    have next := atHole.restart_high positive site.terminal sourceHole.1 sourceHole.2.1 width path deltaEq
    dsimp only at next
    rw [takeRoot, coordinates] at next
    have threshold := Keys.threshold_at_top_ancestor atHole.sourceCoherent atHole.sourceValid
      atHole.historyCorrect atHole.historyLength atHole.afterRoot positive site.terminal path
    have same : shift a d delta (phase + 1) = targetSite.terminal := by
      rw [terminalEq, threshold]
      exact top_shift_eq d a site.terminal delta phase legal.1 sourceHole.1 difference
    have nextDonation := atHole.donationAt_BN positive sourceHole holeOrdered threshold
    rw [← top_shift_eq d a site.terminal delta phase legal.1 sourceHole.1 difference] at nextDonation
    have replacement := ih (phase + 1) targetSite.context
      (holeVisible.take context.length ++ [targetSite.context.length]) next
      (by simpa only [Nat.add_sub_cancel] using nextDonation)
    have nextFinite := atHole.donationAt_finiteLegal positive sourceHole width path deltaEq
    dsimp only at nextFinite
    rw [coordinates] at nextFinite
    have replacementFinite := copies_high_finiteLegal legal found nonowned positive later path delta difference
      count (phase + 1) (by omega) targetSite.context
      (holeVisible.take context.length ++ [targetSite.context.length]) next
      (by simpa only [Nat.add_sub_cancel] using nextFinite)
    have donor : ascendForests (donationAt d context.length site) .nil none delta phase =
        dropLastForest targetSite.attached := by
      rw [donationAt_shift atHole.sourceCoherent atHole.sourceValid atHole.historyCorrect atHole.historyLength,
        copiedForests_dropLast, attachedEq, threshold]
    have targetAttached : targetSite.attached ≠ .nil := by
      rw [attachedEq]
      intro empty
      exact attached ((copiedForests_nil_iff ..).mp empty)
    let replacementTerm := copies (mark d context.length (List.replicate context.length 0)
      (Parents.annotate d context (.cons a hs rest))) depth delta
      (some (donationAt d context.length site)) count (phase + 1)
    have seam : replacementTerm.compare (listCompare Ord.compare)
        (.cons targetSite.terminal targetSite.attached .nil) = .lt ∧
        TerminalFloor targetSite.terminal replacementTerm := by
      cases count with
      | zero => simp only [replacementTerm, copies, Expr.compare, TerminalFloor, and_self]
      | succ count =>
        obtain ⟨ks, tail, shape, first⟩ := marked_root_copies_first_head a hs rest delta
          (some (donationAt d context.length site)) count (phase + 1) (holeSite_root_not_terminal found later)
        have pruned := first (donationAt d context.length site) rfl
        rw [Nat.add_sub_cancel, donor] at pruned
        change (copies _ _ _ _ _ _).compare _ _ = .lt ∧ TerminalFloor _ (copies _ _ _ _ _ _)
        rw [shape]
        refine ⟨?_, congrArg (fun col : List Nat => col[0]?.getD 0) same, ?_⟩
        · rw [same, pruned]
          simp only [Expr.compare, columnCompare_self, dropLastForest_lt targetAttached]
        · intro col member
          rw [← shape] at member
          rw [← same]
          exact replacementFinite.2 col member
    have fullCoherent := Parents.coherent_append_label atHole.sourceCoherent site.terminal
    have fullValid := Parents.context_valid_append_label d site.context atHole.sourceValid site.terminal
    have zeroPath := path.lower_row fullCoherent (by omega : d - 1 < d) (Nat.zero_le _)
    have above := holeSite_root_tail_above depth rest found fullCoherent fullValid positive zeroPath
    have wholeLegal := copied_root_finiteLegal scope positive hs rest legal
    have wholeBN := copied_root_BN scope positive hs rest legal ordered above
    have result := splice_BN depth
      (copied d context.length d delta phase context (List.replicate context.length 0) (.cons a hs rest))
      replacementTerm wholeBN positive wholeLegal targetFound replacement replacementFinite.1 seam.1 seam.2
    have targetHole := holeSite_finiteLegal depth
      (copied d context.length d delta phase context (List.replicate context.length 0) (.cons a hs rest))
      wholeLegal (by intro bound impossible; cases impossible) targetFound
    have fits : FitsOwner targetSite.owner replacementTerm := by
      intro bound owner col member
      have headAbove := targetHole.2.head bound owner
      rw [← same] at headAbove
      exact Nat.lt_of_lt_of_le headAbove (replacementFinite.2 col member)
    have resultFinite := (splice_finiteLegal depth
      (copied d context.length d delta phase context (List.replicate context.length 0) (.cons a hs rest))
      replacementTerm wholeLegal (by intro bound impossible; cases impossible) targetFound replacementFinite.1 fits).1
    have copiedAbove := copied_above scope positive (by simp : context.length < (context ++ [Parents.label d context a]).length)
      (by simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_sub_cancel]; exact Parents.Ancestor.refl _)
      rest legal.2.2.2.2 (by rw [Parents.reading_append_label]; exact above)
    rw [root_view_point scope, Parents.reading_append_label] at copiedAbove
    have rootBelow := zeroPath.reading_lt fullCoherent (by omega)
    rw [Parents.reading_append_label,
      ← Parents.reading_prefix (List.prefix_append site.context _) 0 context.length later] at rootBelow
    change (site.context[context.length]?.getD default).coordinates[0]?.getD 0 < site.terminal[0]?.getD 0 at rootBelow
    rw [coordinates] at rootBelow
    have positiveDelta : 0 < delta[0]?.getD 0 := by have equation := difference 0 positive; omega
    have nextHigher : (shift a d delta phase)[0]?.getD 0 < (shift a d delta (phase + 1))[0]?.getD 0 := by
      rw [shift_value _ _ _ _ 0 (by rw [legal.1]; exact positive),
        shift_value _ _ _ _ 0 (by rw [legal.1]; exact positive)]
      simp only [if_pos positive, Nat.mul_succ]
      omega
    have tailAbove := splice_outer_lower depth
      (copied d context.length d delta phase (context ++ [Parents.label d context a])
        (List.replicate context.length 0 ++ [d]) rest) replacementTerm
      ((shift a d delta phase)[0]?.getD 0 + 1)
      (by intro col member; exact copiedAbove col member)
      (by intro col member; exact Nat.le_trans nextHigher (replacementFinite.2 col member))
    have nonempty : copied d context.length d delta phase (context ++ [Parents.label d context a])
        (List.replicate context.length 0 ++ [d]) rest ≠ .nil := by
      intro empty
      exact nonowned ((copied_nil_iff ..).mp empty)
    rw [copied_at_root, splice_cons_tail depth _ _ _ _ nonempty] at result resultFinite
    rw [copies, ascendReplace_splice]
    change BN d target (setFirstForests _ (splice depth replacementTerm
      (copied d context.length d delta phase context (List.replicate context.length 0) (.cons a hs rest))))
    rw [copied_at_root, splice_cons_tail depth _ _ _ _ nonempty]
    exact result.setFirstForests_above positive resultFinite tailAbove _ donated

/-- Both the first transport state and the first donated BN list are
constructed from the actual source hole. -/
theorem initial_copies_high_BN {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    {a : List Nat} {hs : Forests (List Nat)} {rest : NumericalExpr} {depth : Nat} {site : HoleSite}
    (legal : FiniteLegal d context (.cons a hs rest)) (ordered : BN d context (.cons a hs rest))
    (found : holeSite d context none depth (.cons a hs rest) = some site)
    (nonowned : rest ≠ .nil) (positive : 0 < d) (later : context.length < site.context.length)
    (attached : site.attached ≠ .nil)
    (path : Parents.Ancestor (site.context ++ [Parents.label d site.context site.terminal])
      (d - 1) context.length site.context.length) (count : Nat) :
    let delta := (List.range d).map (fun j => site.terminal[j]?.getD 0 - a[j]?.getD 0)
    BN d site.context (copies (mark d context.length (List.replicate context.length 0)
      (Parents.annotate d context (.cons a hs rest))) depth delta
      (some (donationAt d context.length site)) count 1) := by
  dsimp only
  let delta := (List.range d).map (fun j => site.terminal[j]?.getD 0 - a[j]?.getD 0)
  have state := holeSite_contexts coherent valid depth (.cons a hs rest) found
  have sourceHole := (holeSite_finiteLegal depth (.cons a hs rest) legal
    (by intro bound impossible; cases impossible) found).1
  have unit := sourceHole.2.1.restrict
    (Parents.context_valid_append_label d site.context state.2 site.terminal) (List.prefix_append ..)
  have coordinates := holeSite_root_coordinates found later
  have takeRoot := holeSite_root_take found later
  have width : (site.context[context.length]?.getD default).coordinates.length = d := by
    rw [coordinates]; exact legal.1
  have difference : ∀ j, j < d → site.terminal[j]?.getD 0 = a[j]?.getD 0 + delta[j]?.getD 0 := by
    intro j room
    simp only [delta, List.getElem?_map, List.getElem?_range room, Option.map_some, Option.getD_some]
    have fullCoherent := Parents.coherent_append_label state.1 site.terminal
    have smaller := (path.lower_row fullCoherent (by omega : d - 1 < d) (by omega : j ≤ d - 1)).reading_lt
      fullCoherent (by omega)
    rw [Parents.reading_append_label,
      ← Parents.reading_prefix (List.prefix_append site.context _) j context.length later] at smaller
    change (site.context[context.length]?.getD default).coordinates[j]?.getD 0 < site.terminal[j]?.getD 0 at smaller
    rw [coordinates] at smaller
    omega
  have deltaEq : ∀ j, j < d → site.terminal[j]?.getD 0 =
      Parents.reading site.context j context.length + delta[j]?.getD 0 := by
    intro j room
    change site.terminal[j]?.getD 0 =
      (site.context[context.length]?.getD default).coordinates[j]?.getD 0 + delta[j]?.getD 0
    rw [coordinates]
    exact difference j room
  have zero := ShiftView.zero state.1 state.2 unit context.length d delta later (Nat.le_refl d)
  have scope := zero.restart_high positive site.terminal sourceHole.1 sourceHole.2.1 width path deltaEq
  dsimp only at scope
  rw [takeRoot, coordinates] at scope
  apply copies_high_BN legal ordered found nonowned positive later attached path delta difference count 1
    site.context _ scope
  have headAtOne := top_shift_eq d a site.terminal delta 0 legal.1 sourceHole.1 difference
  rw [shift_zero] at headAtOne
  rw [Nat.sub_self, donationAt_zero, headAtOne]
  exact (ordered.holeSite depth (.cons a hs rest) found).dropLast

theorem initial_copies_high_floor {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    {a : List Nat} {hs : Forests (List Nat)} {rest : NumericalExpr} {depth : Nat} {site : HoleSite}
    (legal : FiniteLegal d context (.cons a hs rest))
    (found : holeSite d context none depth (.cons a hs rest) = some site)
    (nonowned : rest ≠ .nil) (positive : 0 < d) (later : context.length < site.context.length)
    (path : Parents.Ancestor (site.context ++ [Parents.label d site.context site.terminal])
      (d - 1) context.length site.context.length) (count : Nat) :
    let delta := (List.range d).map (fun j => site.terminal[j]?.getD 0 - a[j]?.getD 0)
    TerminalFloor site.terminal (copies (mark d context.length (List.replicate context.length 0)
      (Parents.annotate d context (.cons a hs rest))) depth delta
      (some (donationAt d context.length site)) count 1) := by
  dsimp only
  let delta := (List.range d).map (fun j => site.terminal[j]?.getD 0 - a[j]?.getD 0)
  have state := holeSite_contexts coherent valid depth (.cons a hs rest) found
  have sourceHole := (holeSite_finiteLegal depth (.cons a hs rest) legal
    (by intro bound impossible; cases impossible) found).1
  have headAtOne := first_high_shift_eq legal.1 sourceHole.1 (by
    intro j room
    have fullCoherent := Parents.coherent_append_label state.1 site.terminal
    have smaller := (path.lower_row fullCoherent (by omega : d - 1 < d) (by omega : j ≤ d - 1)).reading_lt
      fullCoherent (by omega)
    rw [Parents.reading_append_label,
      ← Parents.reading_prefix (List.prefix_append site.context _) j context.length later] at smaller
    change (site.context[context.length]?.getD default).coordinates[j]?.getD 0 < site.terminal[j]?.getD 0 at smaller
    rw [holeSite_root_coordinates found later] at smaller
    exact Nat.le_of_lt smaller)
  have computed := initial_copies_high_finiteLegal coherent valid legal found nonowned positive later path count
  cases count with
  | zero => rw [copies]; trivial
  | succ count =>
    obtain ⟨ks, tail, shape, _⟩ := marked_root_copies_first_head a hs rest delta
      (some (donationAt d context.length site)) count 1 (holeSite_root_not_terminal found later)
    rw [shape]
    refine ⟨congrArg (fun col : List Nat => col[0]?.getD 0) headAtOne, ?_⟩
    intro col member
    rw [← shape] at member
    exact computed.2 col member

end BTnSSBMS.Source
