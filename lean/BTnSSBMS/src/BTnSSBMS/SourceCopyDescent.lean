import BTnSSBMS.SourceLeafParents

/-! The first actual copied column is strictly below the replaced terminal:
at a numerical coordinate in a low branch, and at the attached-list
component in a highest branch. Later replicas do not affect this comparison. -/
namespace BTnSSBMS.Source

theorem first_low_shift_lt {a terminal : List Nat} {cap : Nat}
    (left : cap < a.length) (right : cap < terminal.length)
    (lower : ∀ j, j ≤ cap → a[j]?.getD 0 < terminal[j]?.getD 0) :
    listCompare Ord.compare
      (shift a cap ((List.range cap).map (fun j => terminal[j]?.getD 0 - a[j]?.getD 0)) 1) terminal = .lt := by
  apply columnCompare_lt_at _ _ cap (by rw [shift_width]; exact left) right
  · intro j before
    rw [shift_value _ _ _ _ j (by omega)]
    simp only [if_pos before, List.getElem?_map, List.getElem?_range before,
      Option.map_some, Option.getD_some, Nat.mul_one]
    have := lower j (by omega)
    omega
  · rw [shift_value _ _ _ _ cap left]
    simp only [Nat.lt_irrefl, if_false, Nat.add_zero]
    exact lower cap (Nat.le_refl _)

theorem first_high_shift_eq {a terminal : List Nat} {d : Nat}
    (left : a.length = d) (right : terminal.length = d)
    (lower : ∀ j, j < d → a[j]?.getD 0 ≤ terminal[j]?.getD 0) :
    shift a d ((List.range d).map (fun j => terminal[j]?.getD 0 - a[j]?.getD 0)) 1 = terminal := by
  apply List.ext_getElem (by rw [shift_width, left, right])
  intro j inLeft inRight
  have room : j < d := by rw [right] at inRight; exact inRight
  have value := shift_value a ((List.range d).map (fun j => terminal[j]?.getD 0 - a[j]?.getD 0)) d 1 j
    (by rw [left]; exact room)
  simp only [if_pos room, List.getElem?_map, List.getElem?_range room,
    Option.map_some, Option.getD_some, Nat.mul_one] at value
  have := lower j room
  have same : (shift a d ((List.range d).map (fun j => terminal[j]?.getD 0 - a[j]?.getD 0)) 1)[j]?.getD 0 =
      terminal[j]?.getD 0 := by omega
  simpa only [List.getElem?_eq_getElem inLeft, List.getElem?_eq_getElem inRight, Option.getD_some] using same

theorem copies_first_head (a : List Nat) (cap : Nat) (hs : Forests (List Nat × Nat))
    (rest : MarkedExpr) (depth : Nat) (delta : List Nat) (donation : Option (Forests (List Nat × Nat)))
    (count phase : Nat) (safe : rest ≠ .nil ∨ depth ≠ 0) :
    ∃ ks tail, copies (.cons (a, cap) hs rest) depth delta donation (count + 1) phase =
      .cons (shift a cap delta phase) ks tail ∧
      ∀ ds, donation = some ds → ks = ascendForests ds .nil none delta (phase - 1) := by
  cases rest with
  | nil =>
    cases depth with
    | zero => exact False.elim (safe.elim (fun h => h rfl) (fun h => h rfl))
    | succ depth =>
      cases donation with
      | none =>
        simp only [copies, ascendReplace, Option.some_beq_some, show (depth + 1 == 0) = false by simp,
          Bool.and_false, Bool.false_eq_true, if_false, if_true, Option.map_some, Nat.add_sub_cancel]
        exact ⟨_, _, rfl, by intro ds impossible; cases impossible⟩
      | some ds =>
        simp only [copies, ascendReplace, Option.some_beq_some, show (depth + 1 == 0) = false by simp,
          Bool.and_false, Bool.false_eq_true, if_false, if_true, Option.map_some, Nat.add_sub_cancel, setFirstForests]
        exact ⟨_, _, rfl, by intro other same; cases Option.some.inj same; rfl⟩
  | cons b js tail =>
    cases donation with
    | none =>
      simp only [copies, ascendReplace, Bool.false_and, Bool.false_eq_true, if_false]
      exact ⟨_, _, rfl, by intro ds impossible; cases impossible⟩
    | some ds =>
      simp only [copies, ascendReplace, Bool.false_and, Bool.false_eq_true, if_false, setFirstForests]
      exact ⟨_, _, rfl, by intro other same; cases Option.some.inj same; rfl⟩

theorem marked_root_copies_first_head {d cap depth : Nat} {context : ParentContext}
    (a : List Nat) (hs : Forests (List Nat)) (rest : NumericalExpr)
    (delta : List Nat) (donation : Option (Forests (List Nat × Nat))) (count phase : Nat)
    (safe : rest ≠ .nil ∨ depth ≠ 0) :
    ∃ ks tail, copies (mark cap context.length (List.replicate context.length 0)
        (Parents.annotate d context (.cons a hs rest))) depth delta donation (count + 1) phase =
      .cons (shift a cap delta phase) ks tail ∧
      ∀ ds, donation = some ds → ks = ascendForests ds .nil none delta (phase - 1) := by
  simp only [Parents.annotate, mark, List.length_replicate, Nat.lt_irrefl, if_false, if_true,
    Parents.label]
  apply copies_first_head
  rcases safe with nonempty | positive
  · left
    cases rest with
    | nil => exact False.elim (nonempty rfl)
    | cons b js tail => simp [Parents.annotate, mark]
  · exact Or.inr positive

theorem holeSite_root_not_terminal {d depth : Nat} {context : ParentContext} {owner : Option Nat}
    {a : List Nat} {hs : Forests (List Nat)} {rest : NumericalExpr} {site : HoleSite}
    (found : holeSite d context owner depth (.cons a hs rest) = some site)
    (earlier : context.length < site.context.length) : rest ≠ .nil ∨ depth ≠ 0 := by
  by_cases nonempty : rest ≠ .nil
  · exact Or.inl nonempty
  right
  intro zero
  have empty : rest = .nil := Classical.byContradiction nonempty
  rw [empty, zero, holeSite] at found
  have same := Option.some.inj found
  cases same
  exact Nat.lt_irrefl _ earlier

end BTnSSBMS.Source
