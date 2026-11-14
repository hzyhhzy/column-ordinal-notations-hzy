import BTnSSBMS.SourceStopTotality

/-! The frozen source expansion returns a finite term on every finite-legal
positive-dimensional input. Every lookup witness is derived from the input;
none is supplied as a totality assumption. -/
namespace BTnSSBMS.Source

theorem selected_parent_exists {d depth : Nat} {e stop : NumericalExpr}
    (positive : 0 < d) (legal : FiniteLegal d [] e)
    (stopSelected : (spine e)[depth]? = some stop)
    {terminal : List Nat} {attached : Forests (List Nat)}
    (stopLast : last? stop = some (terminal, attached))
    (nonzero : zeroColumn (terminal, attached) ≠ true)
    {parentStop : ParentExpr} {parentTerminal : ParentLabel} {parentAttached : Forests ParentLabel}
    (parentSelected : (spine (parents d e))[depth]? = some parentStop)
    (parentLast : last? parentStop = some (parentTerminal, parentAttached)) :
    ∃ cap root, highestParent 0 parentTerminal.parents = some (cap, root) := by
  cases chosen : highestParent 0 parentTerminal.parents with
  | some pair => exact ⟨pair.1, pair.2, rfl⟩
  | none =>
    have allParents := (highestParent_none_iff parentTerminal.parents 0).mp chosen
    have noParent : ∀ j : Nat, parentTerminal.parents[j]?.join = none := by
      intro j
      cases lookup : parentTerminal.parents[j]? with
      | none => rfl
      | some value =>
        have empty := allParents value (List.mem_of_getElem? lookup)
        simp only [empty, Option.join_some]
    have actual := ((parents_attachedTop positive e legal).spine depth (parents d e) parentSelected).last parentLast
    have noAttached : parentAttached = .nil := by
      by_cases empty : parentAttached = .nil
      · exact empty
      obtain ⟨root, found⟩ := actual.1 empty
      rw [noParent d] at found
      cases found
    have erased : parentStop.map ParentLabel.coordinates = stop := by
      have equation := congrArg (fun term : NumericalExpr => (spine term)[depth]?) (parents_erase d e)
      simp only [spine_map, List.getElem?_map, parentSelected, Option.map_some, stopSelected] at equation
      exact Option.some.inj equation
    have last := last_map ParentLabel.coordinates parentStop
    rw [erased, stopLast, parentLast, noAttached, Option.map_some] at last
    have empty : attached = .nil := congrArg Prod.snd (Option.some.inj last)
    obtain ⟨layer, found, same⟩ := layerAt_exists (d := d) [] none [] stopSelected
    have atLast : last? layer.term = some (terminal, attached) := by rw [same]; exact stopLast
    have state := layerAt_legal (Parents.empty_coherent d) Parents.empty_context_valid depth e legal
      (by intro bound impossible; cases impossible) found
    have terminalLegal := state.2.2.1.last_context atLast
    let before := outerContext d layer.context (dropLast layer.term)
    change FiniteLegal d before (.cons terminal attached .nil) at terminalLegal
    have numeric := actual_terminal_numerical_label parentSelected parentLast found atLast
    have allZero : terminal.all (· == 0) = true := by
      apply List.all_eq_true.mpr
      intro value member
      obtain ⟨j, lookup⟩ := List.mem_iff_getElem?.mp member
      have inside := (List.getElem?_eq_some_iff.mp lookup).choose
      have room : j < d := by rw [terminalLegal.1] at inside; exact inside
      have absent : (Parents.label d before terminal).parents[j]?.join = none := by
        rw [← numeric]
        simp only [Parents.truncate, List.getElem?_take_of_lt room, noParent j]
      have unit := terminalLegal.2.1 before.length (by simp) j room
      simpa only [Parents.reading_append_label, Parents.append_label_parent, absent,
        Option.map_none, Option.getD_none, lookup, Option.getD_some, beq_iff_eq] using unit
    exact False.elim (nonzero (by simp only [zeroColumn, empty, allZero, Bool.true_and]))

theorem expand_exists {d : Nat} {e : NumericalExpr} (positive : 0 < d)
    (legal : FiniteLegal d [] e) (count : Nat) : ∃ f, expand? d e count = some f := by
  cases atLast : last? e with
  | none => exact ⟨.nil, by simp only [expand?, atLast, Option.pure_def]⟩
  | some outer =>
    by_cases zero : zeroColumn outer = true
    · exact ⟨dropLast e, by simp [expand?, atLast, zero]⟩
    obtain ⟨stop, stopSelected, _⟩ := first_stop_selected e
    have nonempty : e ≠ .nil := by intro empty; simp [empty, last?] at atLast
    have stopNonempty := first_stop_nonempty nonempty stopSelected
    obtain ⟨terminal, attached, stopLast⟩ : ∃ a hs, last? stop = some (a, hs) := by
      cases result : last? stop with
      | none => exact False.elim (stopNonempty ((last_none_iff stop).mp result))
      | some column => exact ⟨column.1, column.2, rfl⟩
    by_cases specialCase : specialColumn (terminal, attached) = true
    · exact ⟨special count ((spine e).findIdx stopping) e,
        by simp [expand?, atLast, zero, stopSelected, stopLast, specialCase]⟩
    obtain ⟨parentStop, parentSelected, erases⟩ :=
      mapped_spine_exists ParentLabel.coordinates (parents_erase d e) stopSelected
    obtain ⟨parentTerminal, parentAttached, parentLast, _, _⟩ :=
      mapped_last_exists ParentLabel.coordinates erases stopLast
    obtain ⟨cap, root, chosen⟩ := selected_parent_exists positive legal stopSelected stopLast
      (first_stop_nonzero legal atLast zero stopSelected stopLast) parentSelected parentLast
    obtain ⟨layer, atStop, same⟩ := layerAt_exists (d := d) [] none [] stopSelected
    have last : last? layer.term = some (terminal, attached) := by rw [same]; exact stopLast
    have width := selected_parent_width stopSelected stopLast parentSelected parentLast
    have capBound := (highestParent_found parentTerminal.parents 0 cap root chosen).2.1
    rw [width] at capBound
    let before := outerContext d layer.context (dropLast layer.term)
    have earlier : root < before.length := by
      by_cases top : cap = d
      · subst cap
        exact (selected_top_scoped parentSelected parentLast chosen atStop).1
      · have numeric := selected_low_numerical_root parentSelected parentLast chosen (by omega) atStop last
        exact Parents.label_parent_bound d before terminal cap root numeric
    have size := layerAt_context_length ((spine e).findIdx stopping) e atStop
    simp only [List.length_nil, Nat.zero_add] at size
    have inSpine : root < (((spine e).take ((spine e).findIdx stopping)).map length).sum + length stop := by
      dsimp only [before] at earlier
      rw [outerContext_length, length_dropLast, size, same] at earlier
      omega
    obtain ⟨rootDepth, index, location⟩ := locateRoot_exists_before (spine e) root _ stopSelected inSpine
    have beforeDepth := locateRoot_before (spine e) root rootDepth index _ location stopSelected inSpine
    obtain ⟨rootTerm, rootSelected, rootInside, _⟩ := locateRoot_sound (spine e) root rootDepth index location
    have rootLabelInside : index < (labels rootTerm).length := by rw [labels_length]; exact rootInside
    let rootColumn := (labels rootTerm)[index]
    have rootRead : ((((spine e).take ((spine e).findIdx stopping + 1)).flatMap labels)[root]?) = some rootColumn := by
      rw [locateRoot_visible_label (spine e) root rootDepth index _ location beforeDepth rootSelected]
      exact List.getElem?_eq_getElem rootLabelInside
    let marked := mark cap root [] (parents d e)
    have markedErase : marked.map Prod.fst = e := by rw [mark_erase, parents_erase]
    obtain ⟨rootPart, partSelected, _⟩ := mapped_spine_exists Prod.fst markedErase rootSelected
    obtain ⟨tailPart, tailSelected, tailErase⟩ := mapped_spine_exists Prod.fst markedErase stopSelected
    obtain ⟨tailColumn, tailForests, tailLast, _, _⟩ := mapped_last_exists Prod.fst tailErase stopLast
    dsimp only [marked] at partSelected tailSelected
    let delta := (List.range cap).map (fun j => terminal[j]?.getD 0 - rootColumn[j]?.getD 0)
    let donation := if cap = d then some (dropLastForest tailForests) else none
    refine ⟨ascendReplace marked
      (copies (drop index rootPart) ((spine e).findIdx stopping - rootDepth) delta donation count 1)
      (some ((spine e).findIdx stopping)) delta 0, ?_⟩
    simp [expand?, atLast, zero, stopSelected, stopLast, specialCase,
      parentSelected, parentLast, chosen, location, rootRead, partSelected, tailSelected, tailLast,
      delta, donation, marked]

theorem expand_total_finiteLegal {d : Nat} {e : NumericalExpr} (positive : 0 < d)
    (legal : FiniteLegal d [] e) (count : Nat) :
    ∃ f, expand? d e count = some f ∧ FiniteLegal d [] f := by
  obtain ⟨f, edge⟩ := expand_exists positive legal count
  exact ⟨f, edge, expand_finiteLegal positive legal count edge⟩

theorem standard_expand_total {d : Nat} {e : NumericalExpr} (positive : 0 < d)
    (standard : Standard d e) (count : Nat) :
    ∃ f, expand? d e count = some f ∧ Standard d f ∧ FiniteLegal d [] f := by
  obtain ⟨f, edge, legal⟩ := expand_total_finiteLegal positive (standard_finiteLegal positive standard) count
  exact ⟨f, edge, standard_closed d e f count standard edge, legal⟩

end BTnSSBMS.Source
