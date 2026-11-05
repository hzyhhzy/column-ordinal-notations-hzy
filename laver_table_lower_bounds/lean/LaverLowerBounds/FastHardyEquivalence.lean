import LaverLowerBounds.HardySigmaCompiler

set_option autoImplicit false

namespace LaverLowerBounds.ParentBMS

theorem hardyNext_positive {s : Matrix} (hs : PositiveTail s) (x : Nat) :
    hardyNext s x = (expand s x, x) := by
  obtain ⟨stem, last, rfl, hl⟩ := hs
  rw [hardyNext_append, if_neg hl]

theorem stackCode_nonempty {stack : List Matrix} (hs : stack ≠ []) : stackCode stack ≠ [] := by
  cases stack with
  | nil => contradiction
  | cons s rest => exact attached_nonempty _ (liftW_nonempty s)

theorem stackCode_zero (rest : List Matrix) : stackCode ([] :: rest) = stackCode rest ++ [[]] := by
  simp [stackCode, liftW, attached, translated]

theorem hardyNext_stack_successor (s : Matrix) (rest : List Matrix) (x : Nat) :
    hardyNext (stackCode ((s ++ [[]]) :: rest)) x =
      (stackCode (List.replicate (x + 1) s ++ rest), x) := by
  have hp : PositiveTail (stackCode ((s ++ [[]]) :: rest)) :=
    positive_attached _ (positive_liftW (by simp))
  rw [hardyNext_positive hp, stackCode_successor]

theorem hardyNext_stack_limit {s : Matrix} (hs : PositiveTail s) (rest : List Matrix) (x : Nat) :
    hardyNext (stackCode (s :: rest)) x = (stackCode (expand s x :: rest), x) := by
  have hp : PositiveTail (stackCode (s :: rest)) := positive_attached _ (positive_liftW hs.nonempty)
  rw [hardyNext_positive hp, stackCode_limit hs]

/-- No extra Hardy computation is introduced by W: encoded stacks have
exactly the corresponding FGH machine step at every nonempty state. -/
theorem HardyEval.to_fast_stack {state : Matrix} {x y : Nat} (h : HardyEval state x y) :
    ∀ stack, state = stackCode stack → FastRun stack x y := by
  induction h with
  | done x =>
      intro stack he
      by_cases hz : stack = []
      · subst stack; exact .done x
      · exact False.elim (stackCode_nonempty hz he.symm)
  | @step state x y hs _ ih =>
      intro stack he
      cases stack with
      | nil => exact False.elim (hs he)
      | cons s rest =>
          by_cases hz : s = []
          · subst s
            have hnext : hardyNext state x = (stackCode rest, x + 1) := by
              rw [he, stackCode_zero, hardyNext_append]
              rfl
            rw [hnext] at ih
            exact .zero (ih rest rfl)
          · obtain ⟨stem, last, rfl⟩ := exists_last hz
            by_cases hlast : last = []
            · subst last
              rw [he, hardyNext_stack_successor] at ih
              exact .successor (ih _ rfl)
            · have hp : PositiveTail (stem ++ [last]) := ⟨stem, last, rfl, hlast⟩
              rw [he, hardyNext_stack_limit hp] at ih
              exact .limit hp (ih _ rfl)

theorem HardyEval.to_fast {s : Matrix} {x y : Nat} (h : HardyEval (liftW s) x y) : FastEval s x y :=
  h.to_fast_stack [s] (by simp [stackCode])

theorem fast_hardy_iff (s : Matrix) (x y : Nat) : FastEval s x y ↔ HardyEval (liftW s) x y :=
  ⟨FastEval.to_hardy, HardyEval.to_fast⟩

theorem FastEval.unique {s : Matrix} {x y z : Nat} (hy : FastEval s x y) (hz : FastEval s x z) : y = z :=
  hy.to_hardy.unique hz.to_hardy

theorem FastRun.growth {stack : List Matrix} {x y : Nat} (h : FastRun stack x y) : x + stack.length ≤ y := by
  induction h with
  | done x => simp
  | zero _ ih => simp only [List.length_cons] at *; omega
  | successor _ ih =>
      simp only [List.length_cons, List.length_append, List.length_replicate] at *
      omega
  | limit _ _ ih => exact ih

theorem FastEval.growth {s : Matrix} {x y : Nat} (h : FastEval s x y) : x + 1 ≤ y :=
  FastRun.growth h

#print axioms fast_hardy_iff
#print axioms FastEval.unique

end LaverLowerBounds.ParentBMS
