import LaverLowerBounds.PrefixDescent

/-!
The concrete parent-coordinate copying algorithm from the paper.

The exact coordinate conversion from numerical BM4 is proved in
NumericExpansionFidelity.lean. This does not identify arbitrary lists of
parents with valid/standard numerical BMS arrays.
-/

set_option autoImplicit false

namespace LaverLowerBounds.ParentBMS

abbrev Column := List Nat
abbrev Matrix := List Column

def shift (root offset p : Nat) : Nat := if p < root then p else p + offset

/-- Copy numbered b+1. The first column inherits lower parents from the old
last column and upper parents from the root. All other columns are translated. -/
def copy (stem : Matrix) (last : Column) (row root width b : Nat) : Matrix :=
  (List.range width).map fun i =>
    if i = 0 then
      (last.take row).map (shift root (b * width)) ++
        ((stem[root]?).getD []).drop row
    else
      ((stem[root + i]?).getD []).map (shift root ((b + 1) * width))

def expandTail (stem : Matrix) (last : Column) (index : Nat) : Matrix :=
  match last.getLast? with
  | none => stem
  | some root =>
      let row := last.length - 1
      let width := stem.length - root
      stem ++ (List.range index).flatMap (copy stem last row root width)

def expand (s : Matrix) (index : Nat) : Matrix :=
  match s.reverse with
  | [] => []
  | last :: rest => expandTail rest.reverse last index

@[simp] theorem expand_empty (n : Nat) : expand [] n = [] := rfl

@[simp] theorem expand_append (stem : Matrix) (last : Column) (n : Nat) :
    expand (stem ++ [last]) n = expandTail stem last n := by
  simp [expand]

@[simp] theorem expandTail_zero (stem : Matrix) (last : Column) :
    expandTail stem last 0 = stem := by
  unfold expandTail
  split <;> simp

@[simp] theorem expandTail_empty (stem : Matrix) (n : Nat) :
    expandTail stem [] n = stem := rfl

theorem stem_prefix_expandTail (stem : Matrix) (last : Column) (n : Nat) :
    stem.IsPrefix (expandTail stem last n) := by
  unfold expandTail
  split
  · exact ⟨[], by simp⟩
  · exact ⟨_, rfl⟩

theorem expand_preserves_stem (n : Nat) :
    PrefixDescent.PreservesStem (fun s => expand s n) := by
  intro s
  change s.dropLast.IsPrefix (expand s n)
  cases hs : s.reverse with
  | nil =>
      have he : s = [] := by simpa using congrArg List.reverse hs
      subst s
      simp [expand]
  | cons last rest =>
      have he : s = rest.reverse ++ [last] := by
        simpa using congrArg List.reverse hs
      rw [he, expand_append]
      simpa using stem_prefix_expandTail rest.reverse last n

theorem expand_zero (s : Matrix) : expand s 0 = s.dropLast := by
  cases hs : s.reverse with
  | nil =>
      have he : s = [] := by simpa using congrArg List.reverse hs
      subst s
      rfl
  | cons last rest =>
      have he : s = rest.reverse ++ [last] := by
        simpa using congrArg List.reverse hs
      simp [he]

theorem expandTail_prefix (stem : Matrix) (last : Column) {n k : Nat} (hnk : n ≤ k) :
    (expandTail stem last n).IsPrefix (expandTail stem last k) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnk
  unfold expandTail
  split
  · exact ⟨[], by simp⟩
  · simp only [List.range_add, List.flatMap_append]
    rw [← List.append_assoc]
    exact ⟨_, rfl⟩

theorem expand_prefix (s : Matrix) {n k : Nat} (hnk : n ≤ k) :
    (expand s n).IsPrefix (expand s k) := by
  unfold expand
  split
  · exact ⟨[], rfl⟩
  · exact expandTail_prefix _ _ hnk

def seed (height : Nat) : Matrix := [[], List.replicate height 0]

def triple (height : Nat) : Matrix :=
  [[], List.replicate height 0, List.replicate height 0]

/-- Each [i], i <= n, is a permitted truncation of the fixed-[n] step. -/
theorem smaller_index_is_mixed_step (s : Matrix) {i n : Nat} (hi : i ≤ n)
    (hne : s ≠ []) :
    PrefixDescent.MixedRun (fun a => expand a n) s (expand s i) 1 :=
  .step hne (expand_prefix s hi) (.refl _)

#print axioms expand_preserves_stem
#print axioms expand_prefix
#print axioms smaller_index_is_mixed_step

end LaverLowerBounds.ParentBMS
