import LaverLowerBounds.BlockIndependence

set_option autoImplicit false

namespace LaverLowerBounds.ParentBMS

def PositiveTail (s : Matrix) : Prop := ∃ stem last, s = stem ++ [last] ∧ last ≠ []

theorem PositiveTail.nonempty {s : Matrix} (hs : PositiveTail s) : s ≠ [] := by
  obtain ⟨stem, last, rfl, _⟩ := hs
  simp

def hardyNext (s : Matrix) (x : Nat) : Matrix × Nat :=
  match s.reverse with
  | [] => ([], x)
  | last :: rest => if last = [] then (rest.reverse, x + 1) else (expand s x, x)

theorem hardyNext_append (stem : Matrix) (last : Column) (x : Nat) :
    hardyNext (stem ++ [last]) x =
      if last = [] then (stem, x + 1) else (expand (stem ++ [last]) x, x) := by
  simp [hardyNext]

/-- Finite evaluation, with no unproved global termination hidden in a
function definition. This is the ordinary Hardy successor/limit recursion. -/
inductive HardyEval : Matrix → Nat → Nat → Prop
  | done (x) : HardyEval [] x x
  | step {s x y} : s ≠ [] →
      HardyEval (hardyNext s x).1 (hardyNext s x).2 y → HardyEval s x y

namespace HardyEval

theorem successor {s : Matrix} {x y : Nat} (h : HardyEval s (x + 1) y) :
    HardyEval (s ++ [[]]) x y := by
  apply HardyEval.step (by simp)
  simpa only [hardyNext_append, ↓reduceIte, Prod.fst, Prod.snd] using h

theorem limit {s : Matrix} {x y : Nat} (hs : PositiveTail s) (h : HardyEval (expand s x) x y) :
    HardyEval s x y := by
  obtain ⟨stem, last, rfl, hl⟩ := hs
  apply HardyEval.step (by simp)
  simpa only [hardyNext_append, if_neg hl, Prod.fst, Prod.snd] using h

theorem unique {s : Matrix} {x y z : Nat} (hy : HardyEval s x y) (hz : HardyEval s x z) : y = z := by
  induction hy generalizing z with
  | done x =>
      cases hz with
      | done => rfl
      | step hne _ => exact False.elim (hne rfl)
  | step hne _ ih =>
      cases hz with
      | done => exact False.elim (hne rfl)
      | step _ hnext => exact ih hnext

end HardyEval

/-- A stack evaluator for the usual FGH: F_empty(x)=x+1, a successor applies
its predecessor x+1 times, and a limit takes its x-th fundamental-sequence term.
The first stack entry is evaluated first. -/
inductive FastRun : List Matrix → Nat → Nat → Prop
  | done (x) : FastRun [] x x
  | zero {rest x y} : FastRun rest (x + 1) y → FastRun ([] :: rest) x y
  | successor {s rest x y} :
      FastRun (List.replicate (x + 1) s ++ rest) x y → FastRun ((s ++ [[]]) :: rest) x y
  | limit {s rest x y} : PositiveTail s →
      FastRun (expand s x :: rest) x y → FastRun (s :: rest) x y

def FastEval (s : Matrix) (x y : Nat) : Prop := FastRun [s] x y

def stackCode : List Matrix → Matrix
  | [] => []
  | s :: rest => attached (stackCode rest) (liftW s)

theorem liftW_nonempty (s : Matrix) : liftW s ≠ [] := by simp [liftW]

theorem raiseColumn_nonempty (c : Column) : raiseColumn c ≠ [] := by
  by_cases hc : c = [] <;> simp [raiseColumn, hc]

theorem positive_liftW {s : Matrix} (hs : s ≠ []) : PositiveTail (liftW s) := by
  obtain ⟨stem, last, rfl⟩ := exists_last hs
  refine ⟨liftW stem, raiseColumn last, ?_, raiseColumn_nonempty last⟩
  simp only [liftW_append, List.map_cons, List.map_nil]

theorem positive_attached (front : Matrix) {s : Matrix} (hs : PositiveTail s) :
    PositiveTail (attached front s) := by
  obtain ⟨stem, last, rfl, hl⟩ := hs
  refine ⟨attached front stem, last.map (fun p => p + front.length), ?_, by simpa using hl⟩
  simp [attached, translated, List.append_assoc]

theorem stackCode_replicate (s : Matrix) (rest : List Matrix) (n : Nat) :
    stackCode (List.replicate n s ++ rest) = attached (stackCode rest) (blockCopies (liftW s) n) := by
  induction n with
  | zero => simp [blockCopies]
  | succ n ih =>
      simp only [List.replicate_succ, List.cons_append, stackCode, ih]
      rw [attached_assoc, blockCopies_succ]

theorem stackCode_successor (s : Matrix) (rest : List Matrix) (x : Nat) :
    expand (stackCode ((s ++ [[]]) :: rest)) x =
      stackCode (List.replicate (x + 1) s ++ rest) := by
  change expand (attached (stackCode rest) (liftW (s ++ [[]]))) x = _
  rw [attached_expand _ _ (liftW_nonempty _) x, liftW_expand_successor, stackCode_replicate]

theorem stackCode_limit {s : Matrix} (hs : PositiveTail s) (rest : List Matrix) (x : Nat) :
    expand (stackCode (s :: rest)) x = stackCode (expand s x :: rest) := by
  obtain ⟨stem, last, rfl, hl⟩ := hs
  simp only [stackCode]
  rw [attached_expand _ _ (liftW_nonempty _) x, liftW_expand_nonzero_all hl x]

/-- Exact compilation of each finite FGH evaluation into the Hardy hierarchy.
This is proved about actual expansion rules, not just ordinal arithmetic. -/
theorem FastRun.to_hardy {stack : List Matrix} {x y : Nat} (h : FastRun stack x y) :
    HardyEval (stackCode stack) x y := by
  induction h with
  | done x => exact .done x
  | @zero rest x y _ ih =>
      have he : stackCode ([] :: rest) = stackCode rest ++ [[]] := by simp [stackCode, liftW, attached, translated]
      rw [he]
      exact .successor ih
  | @successor s rest x y _ ih =>
      apply HardyEval.limit (positive_attached _ (positive_liftW (by simp)))
      change HardyEval (expand (stackCode ((s ++ [[]]) :: rest)) x) x y
      rw [stackCode_successor]
      exact ih
  | @limit s rest x y hs _ ih =>
      apply HardyEval.limit (positive_attached _ (positive_liftW hs.nonempty))
      change HardyEval (expand (stackCode (s :: rest)) x) x y
      rw [stackCode_limit hs]
      exact ih

theorem FastEval.to_hardy {s : Matrix} {x y : Nat} (h : FastEval s x y) : HardyEval (liftW s) x y := by
  have he := FastRun.to_hardy h
  simpa only [stackCode, empty_attached] using he

#print axioms HardyEval.unique
#print axioms FastEval.to_hardy

end LaverLowerBounds.ParentBMS
