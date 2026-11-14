import BTnSSBMS.SourceLowLeaf

/-!
The zero class cannot jump across an open forest boundary at the first
stopping layer: that boundary would already have triggered the frozen
special-column test one layer earlier.
-/
namespace BTnSSBMS.Source

theorem highestParent_later_none (parents : List (Option Nat)) (offset branch root index : Nat)
    (chosen : highestParent offset parents = some (branch, root)) (later : branch < offset + index) :
    parents[index]?.join = none := by
  cases lookup : parents[index]? with
  | none => rfl
  | some value =>
    cases value with
    | none => rfl
    | some parent =>
      have lower := highestParent_above parents offset branch root index parent chosen lookup
      omega

theorem selected_zero_terminal_tail {d root depth : Nat} {e stop : NumericalExpr}
    (legal : FiniteLegal d [] e) (stopSelected : (spine e)[depth]? = some stop)
    {terminal : List Nat} {attached : Forests (List Nat)}
    (stopLast : last? stop = some (terminal, attached))
    {parentStop : ParentExpr} {parentTerminal : ParentLabel} {parentAttached : Forests ParentLabel}
    (parentSelected : (spine (parents d e))[depth]? = some parentStop)
    (parentLast : last? parentStop = some (parentTerminal, parentAttached))
    (chosen : highestParent 0 parentTerminal.parents = some (0, root)) :
    (terminal.drop 1).all (· == 0) = true := by
  obtain ⟨layer, found, same⟩ := layerAt_exists (d := d) [] none [] stopSelected
  have last : last? layer.term = some (terminal, attached) := by rw [same]; exact stopLast
  have state := layerAt_legal (Parents.empty_coherent d) Parents.empty_context_valid depth e legal
    (by intro bound impossible; cases impossible) found
  have terminalLegal := state.2.2.1.last_context last
  let before := outerContext d layer.context (dropLast layer.term)
  change FiniteLegal d before (.cons terminal attached .nil) at terminalLegal
  have numeric := actual_terminal_numerical_label parentSelected parentLast found last
  have zero : ∀ j, 0 < j → j < terminal.length → terminal[j]?.getD 0 = 0 := by
    intro j positive inside
    have room : j < d := by rw [terminalLegal.1] at inside; exact inside
    have noParent : (Parents.label d before terminal).parents[j]?.join = none := by
      rw [← numeric]
      simp only [Parents.truncate, List.getElem?_take_of_lt room]
      exact highestParent_later_none parentTerminal.parents 0 0 root j chosen (by omega)
    have unit := terminalLegal.2.1 before.length (by simp) j room
    simpa only [Parents.reading_append_label, Parents.append_label_parent, noParent,
      Option.map_none, Option.getD_none] using unit
  apply List.all_eq_true.mpr
  intro value member
  obtain ⟨i, lookup⟩ := List.mem_iff_getElem?.mp member
  rw [List.getElem?_drop] at lookup
  have inside := (List.getElem?_eq_some_iff.mp lookup).choose
  have atZero := zero (1 + i) (by omega) inside
  simpa only [lookup, Option.getD_some, beq_iff_eq] using atZero

theorem outerContext_prefix (d : Nat) (context : ParentContext) (e : NumericalExpr) :
    context <+: outerContext d context e := by
  cases e with
  | nil => exact List.prefix_refl _
  | cons a hs rest =>
    exact (List.prefix_append context [Parents.label d context a]).trans
      (outerContext_prefix d (context ++ [Parents.label d context a]) rest)

theorem last_label_mem (e : Expr α) {a : α} {hs : Forests α}
    (found : last? e = some (a, hs)) : a ∈ labels e := by
  cases e with
  | nil => simp [last?] at found
  | cons b ks rest =>
    cases rest with
    | nil =>
      have same : (b, ks) = (a, hs) := by simpa only [last?, Option.some.injEq] using found
      cases same
      simp [labels]
    | cons c js tail =>
      exact List.mem_cons_of_mem b (last_label_mem (.cons c js tail) (by simpa only [last?] using found))

theorem zero_parent_outside_forest_special {d root : Nat} (positive : 0 < d)
    (context : ParentContext) (owner : List Nat) (forests : Forests (List Nat))
    {h : NumericalExpr} (child : lastForest? forests = some h)
    (legal : FiniteLegal d (context ++ [Parents.label d context owner]) h)
    (above : ∀ col ∈ labels h, owner[0]?.getD 0 < col[0]?.getD 0)
    {terminal : List Nat} (last : last? h = some (terminal, .nil))
    (tailZero : (terminal.drop 1).all (· == 0) = true)
    (selected : (Parents.label d
      (outerContext d (context ++ [Parents.label d context owner]) (dropLast h)) terminal).parents[0]?.join = some root)
    (outside : root < (context ++ [Parents.label d context owner]).length) :
    specialColumn (owner, forests) = true := by
  let entry := context ++ [Parents.label d context owner]
  let before := outerContext d entry (dropLast h)
  have initial : entry <+: before := outerContext_prefix d entry (dropLast h)
  have ownerInside : context.length < entry.length := by simp [entry]
  have ownerBefore : context.length < before.length := Nat.lt_of_lt_of_le ownerInside initial.length_le
  have ownerReading : Parents.reading before 0 context.length = owner[0]?.getD 0 := by
    rw [← Parents.reading_prefix initial 0 context.length ownerInside]
    exact Parents.reading_append_label d context owner 0
  have terminalAbove := above terminal (last_label_mem h last)
  have search : Parents.search before 0 (terminal[0]?.getD 0) before.length = some root := by
    rw [← Parents.label_zero d before terminal positive]
    exact selected
  obtain ⟨p, lower, found⟩ := Parents.search_zero_exists_above before (terminal[0]?.getD 0)
    before.length context.length (Nat.le_refl _) ownerBefore (by rw [ownerReading]; exact terminalAbove)
  have same : p = root := Option.some.inj (found.symm.trans search)
  have rootOwner : root = context.length := by
    simp only [List.length_append, List.length_cons, List.length_nil] at outside
    omega
  have terminalLegal := legal.last_context last
  change FiniteLegal d before (.cons terminal .nil .nil) at terminalLegal
  change (Parents.label d before terminal).parents[0]?.join = some root at selected
  have rootInside : root < before.length := by rw [rootOwner]; exact ownerBefore
  have equation := terminalLegal.2.1 before.length (by simp) 0 positive
  rw [Parents.reading_append_label, Parents.append_label_parent, selected,
    Option.map_some, Option.getD_some,
    ← Parents.reading_prefix (List.prefix_append before [Parents.label d before terminal]) 0 root rootInside,
    rootOwner, ownerReading] at equation
  have head : terminal.head? = some (owner.headD 0 + 1) := by
    have width := terminalLegal.1
    cases terminal with
    | nil => simp at width; omega
    | cons first rest =>
      simpa only [List.head?_cons, List.getElem?_cons_zero, Option.getD_some,
        List.headD_eq_head?_getD, List.head?_eq_getElem?, Option.some.injEq] using equation
  simp only [specialColumn, child, Option.bind_some, last, head, beq_self_eq_true,
    tailZero, Bool.true_and]

end BTnSSBMS.Source
