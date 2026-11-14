import BTnSSBMS.SearchGeometry
import BTnSSBMS.BMSDescent

/-!
Numerical legality is a finite check on the actual parent table: each
coordinate is zero without a parent, and is its parent's value plus one
otherwise. It is not defined using accessibility or the desired upper bound.
-/
namespace BTnSSBMS.Parents

def UnitSteps (d : Nat) (context : ParentContext) : Prop :=
  ∀ position, position < context.length → ∀ row, row < d →
    reading context row position =
      ((parent context row position).map fun p => reading context row p + 1).getD 0

theorem UnitSteps.at_parent {d : Nat} {context : ParentContext}
    (unit : UnitSteps d context) {row p q : Nat} (room : row < d)
    (edge : parent context row q = some p) :
    reading context row q = reading context row p + 1 := by
  obtain ⟨a, lookup, _⟩ := Option.bind_eq_some_iff.mp edge
  have inside := (List.getElem?_eq_some_iff.mp lookup).choose
  simpa only [edge, Option.map_some, Option.getD_some] using unit q inside row room

theorem UnitSteps.positive_has_parent {d : Nat} {context : ParentContext}
    (unit : UnitSteps d context) {row q : Nat} (room : row < d)
    (inside : q < context.length) (positive : 0 < reading context row q) :
    ∃ p, parent context row q = some p := by
  cases edge : parent context row q with
  | some p => exact ⟨p, rfl⟩
  | none => have zero := unit q inside row room; simp [edge] at zero; omega

theorem parent_next_of_gt {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context)
    {row g q : Nat} (room : row + 1 < d) (edge : parent context row q = some g)
    (larger : reading context (row + 1) g < reading context (row + 1) q) :
    parent context (row + 1) q = some g := by
  obtain ⟨a, atQ, _⟩ := Option.bind_eq_some_iff.mp edge
  have qBound := (List.getElem?_eq_some_iff.mp atQ).choose
  have before := parent_earlier valid edge
  have gBound : g < context.length := by omega
  rw [parent_next_search coherent valid room qBound, edge]
  simp only [Option.map_some, Option.getD_some]
  rw [search]
  simp only [List.getElem?_eq_getElem gBound]
  have small : context[g].coordinates[row + 1]?.getD 0 < reading context (row + 1) q := by
    simpa only [reading, List.getElem?_eq_getElem gBound, Option.getD_some] using larger
  simp only [small, if_true]

theorem child_next_le {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context) (unit : UnitSteps d context)
    {row g q : Nat} (room : row + 1 < d) (edge : parent context row q = some g) :
    reading context (row + 1) q ≤ reading context (row + 1) g + 1 := by
  by_cases larger : reading context (row + 1) g < reading context (row + 1) q
  · exact Nat.le_of_eq (unit.at_parent room (parent_next_of_gt coherent valid room edge larger))
  · omega

theorem saturated_parents {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context)
    {lower upper g q : Nat} (room : upper < d) (rows : lower ≤ upper)
    (edge : parent context lower q = some g)
    (saturated : ∀ j, lower < j → j ≤ upper →
      reading context j q = reading context j g + 1) :
    parent context upper q = some g := by
  induction upper generalizing lower with
  | zero =>
    have same : lower = 0 := by omega
    subst lower
    exact edge
  | succ upper ih =>
    by_cases same : lower = upper + 1
    · subst lower; exact edge
    · have previous := ih (by omega) (by omega) edge (fun j hj hk => saturated j hj (by omega))
      apply parent_next_of_gt coherent valid room previous
      rw [saturated (upper + 1) (by omega) (by omega)]
      omega

/-- At the first coordinate not already saturated, a child cannot exceed
the parent's coordinate plus one. This is the lexicographic child bound. -/
theorem child_coordinate_ceiling {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context) (unit : UnitSteps d context)
    {lower row g q : Nat} (room : row < d) (rows : lower ≤ row)
    (edge : parent context lower q = some g)
    (common : ∀ j, lower ≤ j → j < row → reading context j q = reading context j g + 1) :
    reading context row q ≤ reading context row g + 1 := by
  by_cases same : lower = row
  · subst lower; exact Nat.le_of_eq (unit.at_parent room edge)
  · cases row with
    | zero => omega
    | succ row =>
      have previous := saturated_parents coherent valid (by omega : row < d) (by omega) edge
        (fun j hj hk => common j (by omega) (by omega))
      exact child_next_le coherent valid unit room previous

/-- Extract the first lower-row edge below a higher-row parent. The
extracted child has the same parent in both rows, with both values +1. -/
theorem lower_child_of_higher_parent {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context) (unit : UnitSteps d context)
    {row g q : Nat} (room : row + 1 < d) (edge : parent context (row + 1) q = some g) :
    ∃ child, parent context row child = some g ∧
      parent context (row + 1) child = some g ∧ Ancestor context row child q := by
  have lower := higher_parent_path coherent room edge
  have before := parent_earlier valid edge
  obtain ⟨child, first, tail⟩ := lower.first_child (by omega)
  have after := parent_earlier valid first
  have barrier := parent_chain_barrier coherent valid room edge tail after
  have terminal := unit.at_parent room edge
  refine ⟨child, first, parent_next_of_gt coherent valid room first (by omega), tail⟩

/-- A direct row-zero child forces the immediately following column to
be a row-zero child too. No block sorting assumption is needed. -/
theorem immediate_zero_child {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context) (positive : 0 < d)
    {g q : Nat} (edge : parent context 0 q = some g) :
    g + 1 ≤ q ∧ parent context 0 (g + 1) = some g := by
  have before := parent_earlier valid edge
  obtain ⟨a, atQ, _⟩ := Option.bind_eq_some_iff.mp edge
  have qBound := (List.getElem?_eq_some_iff.mp atQ).choose
  have cBound : g + 1 < context.length := by omega
  have gBound : g < context.length := by omega
  have terminal := parent_reading_lt coherent edge
  have larger : reading context 0 g < reading context 0 (g + 1) := by
    by_cases same : g + 1 = q
    · simpa only [same] using terminal
    · have barrier := parent_zero_barrier coherent positive edge (by omega : g < g + 1) (by omega)
      omega
  refine ⟨by omega, ?_⟩
  rw [parent_zero_search coherent positive (g + 1) cBound, search]
  simp only [List.getElem?_eq_getElem gBound]
  have small : context[g].coordinates[0]?.getD 0 < reading context 0 (g + 1) := by
    simpa only [reading, List.getElem?_eq_getElem gBound, Option.getD_some] using larger
  simp only [small, if_true]

end BTnSSBMS.Parents

namespace BTnSSBMS.BMS

def NumericallyLegal (d : Nat) (m : Matrix) : Prop :=
  (∀ col ∈ m, col.length = d) ∧ Parents.UnitSteps d (parentTable d m)

theorem lastPositive_positive (start : Nat) (xs : List Nat) (row : Nat)
    (found : lastPositive start xs = some row) : 0 < xs[row - start]?.getD 0 := by
  induction xs generalizing start with
  | nil => simp [lastPositive] at found
  | cons x xs ih =>
    cases tail : lastPositive (start + 1) xs with
    | some r =>
      have same : r = row := by simpa [lastPositive, tail] using found
      subst r
      have bound := (lastPositive_bounds (start + 1) xs row tail).1
      have difference : row - start = (row - (start + 1)) + 1 := by omega
      simpa only [difference, List.getElem?_cons_succ] using ih (start + 1) tail
    | none =>
      by_cases positive : 0 < x
      · have same : start = row := by simpa [lastPositive, tail, positive] using found
        subst row
        simpa using positive
      · simp [lastPositive, tail, positive] at found

/-- No option failure occurs on numerically legal matrices. Preservation
of numerical legality under expansion is a separate obligation. -/
theorem expand_total (d : Nat) (m : Matrix) (index : Nat)
    (legal : NumericallyLegal d m) : ∃ result, expand? d m index = some result := by
  cases lastFound : m.getLast? with
  | none => exact ⟨[], by simp [expand?, lastFound]⟩
  | some last =>
    cases topFound : lastPositive 0 last with
    | none => exact ⟨m.dropLast, by simp [expand?, lastFound, topFound]⟩
    | some top =>
      have lastLookup : m[m.length - 1]? = some last := by
        rw [← List.getLast?_eq_getElem?]; exact lastFound
      have lastWidth := legal.1 last (List.mem_of_getElem? lastLookup)
      have room : top < d := by
        have bound := lastPositive_bounds 0 last top topFound
        omega
      have position := (List.getElem?_eq_some_iff.mp lastLookup).choose
      have inside : m.length - 1 < (parentTable d m).length := by
        simpa only [parentTable_length] using position
      have positive : 0 < Parents.reading (parentTable d m) top (m.length - 1) := by
        simpa only [parentTable_reading, lastLookup, Option.getD_some, Nat.sub_zero] using
          lastPositive_positive 0 last top topFound
      obtain ⟨root, edge⟩ := legal.2.positive_has_parent room inside positive
      obtain ⟨final, atFinal, hit⟩ := Option.bind_eq_some_iff.mp edge
      have finalFound : (parentTable d m).getLast? = some final := by
        rw [List.getLast?_eq_getElem?, parentTable_length]; exact atFinal
      have earlier := Parents.parent_earlier (parentTable_valid d m) edge
      have rootBound : root < m.length := by omega
      simp only [expand?, lastFound, topFound, finalFound, hit,
        List.getElem?_eq_getElem rootBound, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      exact ⟨_, rfl⟩

end BTnSSBMS.BMS
