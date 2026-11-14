import BTnSSBMS.ParentChains
import Init.Data.List.TakeDrop

/-!
The activation threshold computed by the frozen BMS copy algorithm is
exactly bounded row ancestry. This is proved for every raw parent table
produced by the actual search, not inferred from bounded experiments.
-/
namespace BTnSSBMS.Parents

theorem parent_getD (context : ParentContext) (row position : Nat) :
    (context[position]?.getD default).parents[row]?.join = parent context row position := by
  cases lookup : context[position]? with
  | none => simp [parent, lookup]; rfl
  | some a => simp [parent, lookup]

theorem Ancestor.iff_parent {context : ParentContext} {row root position : Nat}
    (different : root ≠ position) :
    Ancestor context row root position ↔
      ∃ p, parent context row position = some p ∧ Ancestor context row root p := by
  constructor
  · intro path
    cases path with
    | refl => exact False.elim (different rfl)
    | up edge previous => exact ⟨_, edge, previous⟩
  · rintro ⟨p, edge, previous⟩
    exact .up edge previous

end BTnSSBMS.Parents

namespace BTnSSBMS.BMS

theorem takeWhile_long (xs : List α) (predicate : α → Bool) (j : Nat) :
    j < (xs.takeWhile predicate).length ↔
      ∀ k, k ≤ j → ∃ x, xs[k]? = some x ∧ predicate x = true := by
  induction xs generalizing j with
  | nil =>
    constructor
    · simp
    · intro h
      obtain ⟨x, impossible, _⟩ := h 0 (by omega)
      simp at impossible
  | cons a xs ih =>
    by_cases first : predicate a = true
    · rw [List.takeWhile_cons_of_pos first, List.length_cons]
      cases j with
      | zero =>
        constructor
        · intro _ k hk
          have same : k = 0 := by omega
          subst k
          exact ⟨a, rfl, first⟩
        · intro _; omega
      | succ j =>
        rw [Nat.succ_lt_succ_iff, ih]
        constructor
        · intro tail k hk
          cases k with
          | zero => exact ⟨a, rfl, first⟩
          | succ k => simpa only [List.getElem?_cons_succ] using tail k (by omega)
        · intro all k hk
          simpa only [List.getElem?_cons_succ] using all (k + 1) (by omega)
    · rw [List.takeWhile_cons_of_neg first]
      constructor
      · simp
      · intro h
        obtain ⟨x, lookup, yes⟩ := h 0 (by omega)
        have same : a = x := by simpa using lookup
        exact False.elim (first (same ▸ yes))

theorem range_takeWhile_long (cap : Nat) (predicate : Nat → Bool) (j : Nat) :
    j < ((List.range cap).takeWhile predicate).length ↔
      j < cap ∧ ∀ k, k ≤ j → predicate k = true := by
  rw [takeWhile_long]
  constructor
  · intro h
    obtain ⟨x, lookup, _⟩ := h j (Nat.le_refl _)
    have bound : j < cap := by simpa using (List.getElem?_eq_some_iff.mp lookup).choose
    refine ⟨bound, ?_⟩
    intro k hk
    obtain ⟨a, lookup, yes⟩ := h k hk
    have inside : k < cap := by omega
    have same : k = a := by simpa [inside] using lookup
    exact same ▸ yes
  · rintro ⟨bound, all⟩ k hk
    exact ⟨k, by simp [show k < cap by omega], all k hk⟩

def HistoryCorrect (table : ParentContext) (root cap : Nat) (history : List Nat) : Prop :=
  ∀ i, i < history.length → ∀ j,
    j < history[i]?.getD 0 ↔ j < cap ∧ Parents.Ancestor table j root i

private theorem test_iff_ancestry {table : ParentContext}
    (valid : Parents.ContextValid table) {root cap i k : Nat} {history : List Nat}
    (correct : HistoryCorrect table root cap history) (length : history.length = i)
    (different : root ≠ i) (row : k < cap) :
    (match (table[i]?.getD default).parents[k]?.join with
      | none => false
      | some p => decide (root ≤ p ∧ k < history[p]?.getD 0)) = true ↔
      Parents.Ancestor table k root i := by
  rw [Parents.parent_getD, Parents.Ancestor.iff_parent different]
  cases edge : Parents.parent table k i with
  | none => simp
  | some p =>
    have earlier := Parents.parent_earlier valid edge
    have ih := correct p (by omega) k
    simp only [decide_eq_true_eq, Option.some.injEq, exists_eq_left']
    constructor
    · rintro ⟨_, active⟩
      exact (ih.mp active).2
    · intro path
      exact ⟨path.le valid, ih.mpr ⟨row, path⟩⟩

theorem activation_correct {d : Nat} {table : ParentContext}
    (valid : Parents.ContextValid table) (coherent : Parents.Coherent d table)
    (root cap : Nat) (capBound : cap ≤ d) (history : List Nat) (i : Nat)
    (length : history.length = i) (correct : HistoryCorrect table root cap history) (j : Nat) :
    j < activation table root cap history i ↔
      j < cap ∧ Parents.Ancestor table j root i := by
  by_cases before : i < root
  · simp only [activation, before, if_true, Nat.not_lt_zero, false_iff, not_and]
    intro _ path
    have impossible := path.le valid
    omega
  · by_cases atRoot : i = root
    · rw [activation, if_neg before, if_pos atRoot]
      exact ⟨fun h => ⟨h, by rw [atRoot]; exact .refl _⟩, And.left⟩
    · simp only [activation, before, if_false, atRoot]
      rw [range_takeWhile_long]
      constructor
      · rintro ⟨row, tests⟩
        exact ⟨row, (test_iff_ancestry valid correct length (Ne.symm atRoot) row).mp
          (tests j (Nat.le_refl _))⟩
      · rintro ⟨row, path⟩
        refine ⟨row, ?_⟩
        intro k hk
        apply (test_iff_ancestry valid correct length (Ne.symm atRoot) (by omega)).mpr
        exact path.lower_row coherent (by omega) hk

def thresholdPrefix (table : ParentContext) (root cap count : Nat) : List Nat :=
  (List.range count).foldl
    (fun history i => history ++ [activation table root cap history i]) []

theorem thresholdPrefix_succ (table : ParentContext) (root cap count : Nat) :
    thresholdPrefix table root cap (count + 1) = thresholdPrefix table root cap count ++
      [activation table root cap (thresholdPrefix table root cap count) count] := by
  simp only [thresholdPrefix, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem thresholdPrefix_length (table : ParentContext) (root cap count : Nat) :
    (thresholdPrefix table root cap count).length = count := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [thresholdPrefix_succ, List.length_append,
      List.length_cons, List.length_nil, ih]

theorem thresholdPrefix_correct {d : Nat} {table : ParentContext}
    (valid : Parents.ContextValid table) (coherent : Parents.Coherent d table)
    (root cap : Nat) (capBound : cap ≤ d) (count : Nat) :
    HistoryCorrect table root cap (thresholdPrefix table root cap count) := by
  induction count with
  | zero => intro i bound; simp [thresholdPrefix] at bound
  | succ count ih =>
    intro i bound j
    have inside : i < count + 1 := by simpa only [thresholdPrefix_length] using bound
    rw [thresholdPrefix_succ]
    by_cases old : i < count
    · rw [List.getElem?_append_left (by simpa only [thresholdPrefix_length] using old)]
      exact ih i (by simpa only [thresholdPrefix_length] using old) j
    · have atEnd : i = count := by omega
      subst i
      have lookup : (thresholdPrefix table root cap count ++
          [activation table root cap (thresholdPrefix table root cap count) count])[count]? =
          some (activation table root cap (thresholdPrefix table root cap count) count) := by
        have atLength : (thresholdPrefix table root cap count ++
            [activation table root cap (thresholdPrefix table root cap count) count])[(thresholdPrefix table root cap count).length]? =
            some (activation table root cap (thresholdPrefix table root cap count) count) :=
          List.getElem?_concat_length
        simpa only [thresholdPrefix_length] using atLength
      rw [lookup, Option.getD_some]
      exact activation_correct valid coherent root cap capBound _ count
        (thresholdPrefix_length ..) ih j

/-- Exact meaning of the activation values used by `BMS.expand?`. -/
theorem thresholds_ancestry (d : Nat) (m : Matrix) (root cap : Nat) (capBound : cap ≤ d)
    (i : Nat) (inside : i < m.length) (j : Nat) :
    j < (thresholds (parentTable d m) root cap)[i]?.getD 0 ↔
      j < cap ∧ Parents.Ancestor (parentTable d m) j root i := by
  have correct := thresholdPrefix_correct (parentTable_valid d m) (parentTable_coherent d m)
    root cap capBound (parentTable d m).length
  exact correct i (by simpa only [thresholdPrefix_length, parentTable_length] using inside) j

end BTnSSBMS.BMS
