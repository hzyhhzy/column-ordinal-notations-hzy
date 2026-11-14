import BTnSSBMS.HWLowCopies

/-! Highest-class HW preservation with literal previous-phase donation.
The donated first list equals a strict pruning of the copied terminal list;
it is not identified with a differently rebased parent's attachment. -/
namespace BTnSSBMS.Source

theorem dropLastForest_map (f : α → β) (hs : Forests α) :
    (dropLastForest hs).map f = dropLastForest (hs.map f) := by
  cases hs with
  | nil => simp only [dropLastForest, Forests.map]
  | cons h rest =>
    cases rest with
    | nil => simp only [dropLastForest, Forests.map]
    | cons k ks => simp only [dropLastForest, Forests.map, dropLastForest_map f (.cons k ks)]

theorem copiedForests_dropLast (d root cap : Nat) (delta : List Nat) (phase : Nat)
    (context : ParentContext) (history : List Nat) (hs : Forests (List Nat)) :
    copiedForests d root cap delta phase context history (dropLastForest hs) =
      dropLastForest (copiedForests d root cap delta phase context history hs) := by
  simp only [copiedForests, annotateForests_dropLast, markForests_dropLast, dropLastForest_map]

theorem copies_high_HW {d : Nat} {context : ParentContext}
    {a : List Nat} {hs : Forests (List Nat)} {rest : NumericalExpr} {depth : Nat} {site : HoleSite}
    (legal : FiniteLegal d context (.cons a hs rest)) (ordered : HW (.cons a hs rest))
    (found : holeSite d context none depth (.cons a hs rest) = some site)
    (positive : 0 < d) (later : context.length < site.context.length)
    (attached : site.attached ≠ .nil)
    (path : Parents.Ancestor (site.context ++ [Parents.label d site.context site.terminal])
      (d - 1) context.length site.context.length)
    (delta : List Nat)
    (difference : ∀ j, j < d → site.terminal[j]?.getD 0 = a[j]?.getD 0 + delta[j]?.getD 0)
    (count phase : Nat) (target : ParentContext) (visible : List Nat)
    (scope : ShiftView d (context ++ [Parents.label d context a])
      (target ++ [Parents.label d target (shift a d delta phase)]) visible
      (List.replicate context.length 0 ++ [d]) context.length d delta phase)
    (donated : HWForests (ascendForests (donationAt d context.length site) .nil none delta (phase - 1))) :
    HW (copies (mark d context.length (List.replicate context.length 0)
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
    have nextDonation := atHole.donationAt_HW sourceHole holeOrdered threshold
    have replacement := ih (phase + 1) targetSite.context
      (holeVisible.take context.length ++ [targetSite.context.length]) next
      (by simpa only [Nat.add_sub_cancel] using nextDonation)
    have same : shift a d delta (phase + 1) = targetSite.terminal := by
      rw [terminalEq, threshold]
      exact top_shift_eq d a site.terminal delta phase legal.1 sourceHole.1 difference
    have donor : ascendForests (donationAt d context.length site) .nil none delta phase =
        dropLastForest targetSite.attached := by
      rw [donationAt_shift atHole.sourceCoherent atHole.sourceValid atHole.historyCorrect atHole.historyLength,
        copiedForests_dropLast, attachedEq, threshold]
    have targetAttached : targetSite.attached ≠ .nil := by
      rw [attachedEq]
      intro empty
      exact attached ((copiedForests_nil_iff ..).mp empty)
    have lower : (copies (mark d context.length (List.replicate context.length 0)
        (Parents.annotate d context (.cons a hs rest))) depth delta
        (some (donationAt d context.length site)) count (phase + 1)).compare
        (listCompare Ord.compare) (.cons targetSite.terminal targetSite.attached .nil) = .lt := by
      cases count with
      | zero => simp only [copies, Expr.compare]
      | succ count =>
        obtain ⟨ks, tail, shape, first⟩ := marked_root_copies_first_head a hs rest delta
          (some (donationAt d context.length site)) count (phase + 1) (holeSite_root_not_terminal found later)
        have pruned := first (donationAt d context.length site) rfl
        rw [Nat.add_sub_cancel, donor] at pruned
        rw [shape, same, pruned]
        simp only [Expr.compare, columnCompare_self, dropLastForest_lt targetAttached]
    have result := splice_HW depth
      (copied d context.length d delta phase context (List.replicate context.length 0) (.cons a hs rest))
      _ (copied_root_HW scope hs rest legal ordered) replacement targetFound lower
    rw [copies, ascendReplace_splice]
    exact setFirstForests_HW result donated

theorem initial_copies_high_HW {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    {a : List Nat} {hs : Forests (List Nat)} {rest : NumericalExpr} {depth : Nat} {site : HoleSite}
    (legal : FiniteLegal d context (.cons a hs rest)) (ordered : HW (.cons a hs rest))
    (found : holeSite d context none depth (.cons a hs rest) = some site)
    (positive : 0 < d) (later : context.length < site.context.length) (attached : site.attached ≠ .nil)
    (path : Parents.Ancestor (site.context ++ [Parents.label d site.context site.terminal])
      (d - 1) context.length site.context.length) (count : Nat) :
    let delta := (List.range d).map (fun j => site.terminal[j]?.getD 0 - a[j]?.getD 0)
    HW (copies (mark d context.length (List.replicate context.length 0)
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
  apply copies_high_HW legal ordered found positive later attached path delta difference count 1
    site.context _ scope
  rw [Nat.sub_self, donationAt_zero]
  exact (ordered.holeSite depth (.cons a hs rest) found).dropLast

end BTnSSBMS.Source
