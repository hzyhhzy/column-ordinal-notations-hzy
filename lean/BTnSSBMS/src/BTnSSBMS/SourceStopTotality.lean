import BTnSSBMS.SourceFiniteClosure

/-! Finite lookup totality for the frozen stopping-spine algorithm. The
arguments use literal spine positions and scope boundaries, not an
alternative expansion algorithm. -/
namespace BTnSSBMS.Source

theorem not_stopping_child (e : NumericalExpr) (notStop : stopping e = false) :
    ∃ h, lastChild? e = some h ∧ h ≠ .nil := by
  cases atLast : last? e with
  | none => simp [stopping, atLast] at notStop
  | some column =>
    cases child : lastForest? column.2 with
    | none => simp [stopping, atLast, child] at notStop
    | some h =>
      cases h with
      | nil => simp [stopping, atLast, child] at notStop
      | cons a hs rest =>
        exact ⟨.cons a hs rest, by simp [lastChild?, atLast, child], by intro impossible; cases impossible⟩

theorem spine_next {e part h : Expr α} {depth : Nat}
    (selected : (spine e)[depth]? = some part) (child : lastChild? part = some h) :
    (spine e)[depth + 1]? = some h := by
  induction depth generalizing e with
  | zero =>
    have same : e = part := by simpa only [spine, List.getElem?_cons_zero, Option.some.injEq] using selected
    subst e
    rw [spine_get_succ, child, Option.bind_some]
    rfl
  | succ depth ih =>
    rw [spine_get_succ] at selected
    obtain ⟨next, nextChild, below⟩ := Option.bind_eq_some_iff.mp selected
    rw [spine_get_succ, nextChild, Option.bind_some]
    exact ih below

theorem spine_has_stopping (e : NumericalExpr) : ∃ part ∈ spine e, stopping part = true := by
  have nonempty : 0 < (spine e).length := by simp [spine]
  let final := (spine e).length - 1
  have inside : final < (spine e).length := by omega
  let part := (spine e)[final]
  have selected : (spine e)[final]? = some part := List.getElem?_eq_getElem inside
  by_cases yes : stopping part = true
  · exact ⟨part, List.mem_of_getElem? selected, yes⟩
  obtain ⟨child, atChild, _⟩ := not_stopping_child part (Bool.eq_false_iff.mpr yes)
  have next := spine_next selected atChild
  have room := (List.getElem?_eq_some_iff.mp next).choose
  omega

theorem first_stop_selected (e : NumericalExpr) :
    ∃ stop, (spine e)[(spine e).findIdx stopping]? = some stop ∧ stopping stop = true := by
  have inside := List.findIdx_lt_length_of_exists (spine_has_stopping e)
  exact ⟨(spine e)[(spine e).findIdx stopping], List.getElem?_eq_getElem inside,
    List.findIdx_getElem⟩

theorem first_stop_nonempty {e stop : NumericalExpr} (nonempty : e ≠ .nil)
    (selected : (spine e)[(spine e).findIdx stopping]? = some stop) : stop ≠ .nil := by
  generalize first : (spine e).findIdx stopping = depth at selected
  cases depth with
  | zero =>
    have same : e = stop := by simpa only [spine, List.getElem?_cons_zero, Option.some.injEq] using selected
    rw [← same]
    exact nonempty
  | succ depth =>
    have inside := (List.getElem?_eq_some_iff.mp selected).choose
    have previousInside : depth < (spine e).length := by omega
    let previous := (spine e)[depth]
    have previousSelected : (spine e)[depth]? = some previous := List.getElem?_eq_getElem previousInside
    have notStop := stopping_before previousSelected (by omega)
    obtain ⟨child, atChild, childNonempty⟩ := not_stopping_child previous notStop
    have same := Option.some.inj ((spine_next previousSelected atChild).symm.trans selected)
    rw [← same]
    exact childNonempty

theorem mapped_spine_exists (f : α → β) {e : Expr α} {image part : Expr β} {depth : Nat}
    (erases : e.map f = image) (selected : (spine image)[depth]? = some part) :
    ∃ original, (spine e)[depth]? = some original ∧ original.map f = part := by
  rw [← erases, spine_map, List.getElem?_map] at selected
  exact Option.map_eq_some_iff.mp selected

theorem mapped_last_exists (f : α → β) {e : Expr α} {image : Expr β}
    (erases : e.map f = image) {a : β} {hs : Forests β}
    (last : last? image = some (a, hs)) :
    ∃ b ks, last? e = some (b, ks) ∧ f b = a ∧ ks.map f = hs := by
  rw [← erases, last_map] at last
  obtain ⟨⟨b, ks⟩, selected, same⟩ := Option.map_eq_some_iff.mp last
  exact ⟨b, ks, selected, congrArg Prod.fst same, congrArg Prod.snd same⟩

theorem locateRoot_exists_before (sp : List (Expr α)) (root depth : Nat) {part : Expr α}
    (selected : sp[depth]? = some part)
    (before : root < ((sp.take depth).map length).sum + length part) :
    ∃ rootDepth index, locateRoot sp root = some (rootDepth, index) := by
  induction sp generalizing root depth with
  | nil => simp at selected
  | cons head rest ih =>
    by_cases inside : root < length head
    · exact ⟨0, root, by rw [locateRoot, if_pos inside]⟩
    cases depth with
    | zero =>
      have same : head = part := by simpa only [List.getElem?_cons_zero, Option.some.injEq] using selected
      subst part
      simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add] at before
      exact False.elim (inside before)
    | succ depth =>
      have next : rest[depth]? = some part := by simpa only [List.getElem?_cons_succ] using selected
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons] at before
      obtain ⟨rootDepth, index, found⟩ := ih (root - length head) depth next (by omega)
      exact ⟨rootDepth + 1, index, by rw [locateRoot, if_neg inside, found, Option.map_some]⟩

theorem layerAt_positive_owner {d : Nat} (context : ParentContext) (owner : Option Nat) (owners : List Nat)
    (depth : Nat) (e : NumericalExpr) {layer : SpineLayer}
    (found : layerAt d context owner owners (depth + 1) e = some layer) : ∃ bound, layer.owner = some bound := by
  induction depth generalizing context owner owners e with
  | zero =>
    simp only [layerAt, Option.bind_eq_some_iff] at found
    obtain ⟨⟨a, hs⟩, _, h, _, same⟩ := found
    have equal := Option.some.inj same
    rw [← equal]
    exact ⟨a[0]?.getD 0, rfl⟩
  | succ depth ih =>
    rw [layerAt] at found
    obtain ⟨⟨a, hs⟩, _, h, _, next⟩ := by
      simpa only [Option.bind_eq_some_iff] using found
    exact ih _ _ _ h next

theorem first_stop_nonzero {d : Nat} {e stop : NumericalExpr}
    (legal : FiniteLegal d [] e) {outer : List Nat × Forests (List Nat)}
    (atLast : last? e = some outer) (nonzero : zeroColumn outer ≠ true)
    (selected : (spine e)[(spine e).findIdx stopping]? = some stop)
    {terminal : List Nat} {attached : Forests (List Nat)}
    (last : last? stop = some (terminal, attached)) : zeroColumn (terminal, attached) ≠ true := by
  generalize first : (spine e).findIdx stopping = depth at selected
  cases depth with
  | zero =>
    have same : e = stop := by simpa only [spine, List.getElem?_cons_zero, Option.some.injEq] using selected
    rw [← same, atLast] at last
    have pair := Option.some.inj last
    rw [← pair]
    exact nonzero
  | succ depth =>
    obtain ⟨layer, found, same⟩ := layerAt_exists (d := d) [] none [] selected
    obtain ⟨bound, owner⟩ := layerAt_positive_owner [] none [] depth e found
    have state := layerAt_legal (Parents.empty_coherent d) Parents.empty_context_valid (depth + 1) e legal
      (by intro b impossible; cases impossible) found
    have above := state.2.2.2 bound owner terminal (by rw [same]; exact last_label_mem stop last)
    intro zero
    have all : terminal.all (· == 0) = true := (Bool.and_eq_true_iff.mp zero).1
    have headZero : terminal[0]?.getD 0 = 0 := by
      cases terminal with
      | nil => rfl
      | cons head rest =>
        have value := List.all_eq_true.mp all head (by simp)
        simpa only [List.getElem?_cons_zero, Option.getD_some, beq_iff_eq] using value
    omega

end BTnSSBMS.Source
