import BTnSSBMS.SourceTopExistence

/-! Actual low-class terminal columns are leaves, in every positive
dimension. The statement follows from finite source legality and actual
key-parent existence, not a restriction added to the source domain. -/
namespace BTnSSBMS.Source

theorem highestParent_above (parents : List (Option Nat)) (offset branch root index parent : Nat)
    (chosen : highestParent offset parents = some (branch, root))
    (present : parents[index]? = some (some parent)) : offset + index ≤ branch := by
  induction parents generalizing offset index with
  | nil => simp at present
  | cons head rest ih =>
    cases index with
    | zero => exact (highestParent_found (head :: rest) offset branch root chosen).1
    | succ index =>
      have nextPresent : rest[index]? = some (some parent) := by
        simpa only [List.getElem?_cons_succ] using present
      rw [highestParent] at chosen
      cases next : highestParent (offset + 1) rest with
      | none =>
        have all := (highestParent_none_iff rest (offset + 1)).mp next
        have impossible := all (some parent) (List.mem_of_getElem? nextPresent)
        cases impossible
      | some pair =>
        have same : pair = (branch, root) := by simpa only [next, Option.some.injEq] using chosen
        subst pair
        have lower := ih (offset + 1) index next nextPresent
        omega

theorem AttachedTop.last {d : Nat} {e : ParentExpr} (safe : AttachedTop d e)
    {a : ParentLabel} {hs : Forests ParentLabel} (found : last? e = some (a, hs)) :
    (hs ≠ .nil → ∃ root, a.parents[d]?.join = some root) ∧ AttachedTopForests d hs := by
  cases e with
  | nil => simp [last?] at found
  | cons b ks rest =>
    cases rest with
    | nil =>
      have same : (b, ks) = (a, hs) := by simpa only [last?, Option.some.injEq] using found
      cases same
      exact ⟨safe.1, safe.2.1⟩
    | cons c js tail => exact safe.2.2.last (by simpa only [last?] using found)

theorem AttachedTopForests.last {d : Nat} {hs : Forests ParentLabel}
    (safe : AttachedTopForests d hs) {h : ParentExpr} (found : lastForest? hs = some h) :
    AttachedTop d h := by
  cases hs with
  | nil => simp [lastForest?] at found
  | cons first rest =>
    cases rest with
    | nil =>
      have same : first = h := by simpa only [lastForest?, Option.some.injEq] using found
      subst h
      exact safe.1
    | cons k ks => exact safe.2.last (by simpa only [lastForest?] using found)

theorem AttachedTop.spine {d : Nat} (depth : Nat) (e : ParentExpr) (safe : AttachedTop d e)
    {part : ParentExpr} (selected : (spine e)[depth]? = some part) : AttachedTop d part := by
  induction depth generalizing e part with
  | zero =>
    have same : e = part := by simpa only [Source.spine, List.getElem?_cons_zero, Option.some.injEq] using selected
    subst part
    exact safe
  | succ depth ih =>
    rw [spine_get_succ] at selected
    obtain ⟨h, child, below⟩ := Option.bind_eq_some_iff.mp selected
    obtain ⟨⟨a, hs⟩, last, forest⟩ := Option.bind_eq_some_iff.mp child
    exact ih h ((safe.last last).2.last forest) below

theorem selected_low_terminal_leaf {d cap root depth : Nat} {e stop : NumericalExpr}
    (positive : 0 < d) (legal : FiniteLegal d [] e) (room : cap < d)
    (stopSelected : (spine e)[depth]? = some stop)
    {terminal : List Nat} {attached : Forests (List Nat)}
    (stopLast : last? stop = some (terminal, attached))
    {parentStop : ParentExpr} {parentTerminal : ParentLabel} {parentAttached : Forests ParentLabel}
    (parentSelected : (spine (parents d e))[depth]? = some parentStop)
    (parentLast : last? parentStop = some (parentTerminal, parentAttached))
    (chosen : highestParent 0 parentTerminal.parents = some (cap, root)) : attached = .nil := by
  have actual := ((parents_attachedTop positive e legal).spine depth (parents d e) parentSelected).last parentLast
  have noForests : parentAttached = .nil := by
    by_cases empty : parentAttached = .nil
    · exact empty
    obtain ⟨top, selected⟩ := actual.1 empty
    cases lookup : parentTerminal.parents[d]? with
    | none => simp [lookup] at selected
    | some value =>
      have same : value = some top := by simpa only [lookup, Option.join_some] using selected
      rw [same] at lookup
      have lower := highestParent_above parentTerminal.parents 0 cap root d top chosen lookup
      omega
  have numerical : parentStop.map ParentLabel.coordinates = stop := by
    have mapped : (spine (parents d e)).map (Expr.map ParentLabel.coordinates) = spine e := by
      rw [← spine_map, parents_erase]
    have atIndex := congrArg (fun sp : List NumericalExpr => sp[depth]?) mapped
    rw [List.getElem?_map, parentSelected, Option.map_some, stopSelected] at atIndex
    exact Option.some.inj atIndex
  have last := last_map ParentLabel.coordinates parentStop
  rw [numerical, stopLast, parentLast, Option.map_some, noForests] at last
  exact congrArg Prod.snd (Option.some.inj last)

end BTnSSBMS.Source
