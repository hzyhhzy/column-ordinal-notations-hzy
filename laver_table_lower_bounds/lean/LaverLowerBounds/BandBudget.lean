import Std

/-!
A local replacement for the four-class global step count in the paper.

For a band representation with at least three rows, use
    endpoint - 2 * columns + ready,
where ready is 1 precisely for a full-height, width-one bad block.
The representation/copying lemmas must still supply the local conditions below.
This file proves the arithmetic consequences, not those structural lemmas.
-/

set_option autoImplicit false

namespace LaverLowerBounds.BandBudget

structure State where
  endpoint : Nat
  columns : Nat
  ready : Bool
  room : 2 * columns ≤ endpoint

def rank (s : State) : Nat := s.endpoint - 2 * s.columns + if s.ready then 1 else 0

/-- These are exactly the local resource inequalities to be verified by the
actual band-copy implementation. Narrow positive steps always clear `ready`. -/
inductive Step : State → State → Prop
  | delete {old next} : old.columns = next.columns + 1 →
      next.endpoint + 4 ≤ old.endpoint → Step old next
  | narrow {old next} : next.columns = old.columns → next.ready = false →
      next.endpoint ≤ old.endpoint →
      (old.ready = false → next.endpoint < old.endpoint) → Step old next
  | wide {old next} : old.columns < next.columns →
      next.endpoint ≤ old.endpoint → Step old next

theorem rank_decreases {old next : State} (h : Step old next) : rank next < rank old := by
  have hold := old.room
  have hnext := next.room
  cases h with
  | delete hw he =>
      unfold rank
      cases old.ready <;> cases next.ready <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  | narrow hw hn he hd =>
      unfold rank
      rw [hn]
      cases ho : old.ready with
      | false =>
          have hs := hd ho
          simp only [Bool.false_eq_true, ↓reduceIte]
          omega
      | true =>
          simp only [↓reduceIte, Bool.false_eq_true]
          omega
  | wide hw he =>
      unfold rank
      cases old.ready <;> cases next.ready <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

inductive Run : State → State → Nat → Prop
  | refl (s) : Run s s 0
  | cons {s t u n} : Step s t → Run t u n → Run s u (n + 1)

theorem run_budget {s t : State} {n : Nat} (h : Run s t n) : n + rank t ≤ rank s := by
  induction h with
  | refl s => omega
  | cons hstep _ ih =>
      have hdec := rank_decreases hstep
      omega

theorem triple_rank_lt_endpoint {s : State} (hs : s.columns = 3) : rank s < s.endpoint := by
  have hroom := s.room
  unfold rank
  rw [hs]
  rw [hs] at hroom
  split <;> omega

/-- A three-column start has at least five units of strict surplus. -/
theorem triple_run_lt_endpoint {s t : State} {n : Nat} (h : Run s t n)
    (hs : s.columns = 3) : n < s.endpoint := by
  exact Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right _ _) (run_budget h))
    (triple_rank_lt_endpoint hs)

/-- The arithmetic update conditions themselves prohibit an infinite run. -/
theorem no_infinite_run (states : Nat → State)
    (h : ∀ n, Step (states n) (states (n + 1))) : False := by
  have hbound : ∀ n, n + rank (states n) ≤ rank (states 0) := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
        have hd := rank_decreases (h n)
        omega
  have hbad := hbound (rank (states 0) + 1)
  omega

#print axioms rank_decreases
#print axioms triple_run_lt_endpoint
#print axioms no_infinite_run

end LaverLowerBounds.BandBudget
