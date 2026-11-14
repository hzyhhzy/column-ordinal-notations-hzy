import BTnSSBMS.Parents
import Init.Data.List.MapIdx
import Init.Data.List.Zip

/-!
Fixed-width BM4 short expansion. This file spells out the parent search,
activation thresholds, and copy phases; there is no special seed-expansion
branch. Trailing zero rows are retained until an explicit projection.

`none` records an undefined root on malformed raw input. Standardness and
root existence are not built into this definition and must be proved.
Natural subtraction agrees with the numerical rule when the root is an
ancestor; the required nonnegativity is a separate legality obligation.
-/
namespace BTnSSBMS.BMS

def parentTableAux (rows : Nat) : ParentContext → Matrix → ParentContext
  | context, [] => context
  | context, col :: rest =>
    parentTableAux rows (context ++ [Parents.label rows context col]) rest

def parentTable (rows : Nat) (m : Matrix) : ParentContext := parentTableAux rows [] m

def lastPositive (start : Nat) : List Nat → Option Nat
  | [] => none
  | x :: xs =>
    match lastPositive (start + 1) xs with
    | some i => some i
    | none => if 0 < x then some start else none

def activation (table : ParentContext) (root row : Nat) (history : List Nat)
    (i : Nat) : Nat :=
  if i < root then 0
  else if i = root then row
  else ((List.range row).takeWhile fun j =>
    match (table[i]?.getD default).parents[j]?.join with
    | none => false
    | some p => decide (root ≤ p ∧ j < history[p]?.getD 0)).length

def thresholds (table : ParentContext) (root row : Nat) : List Nat :=
  (List.range table.length).foldl
    (fun history i => history ++ [activation table root row history i]) []

def copy (m : Matrix) (a : List Nat) (delta : List Nat)
    (root endIndex phase : Nat) : Matrix :=
  ((List.range (endIndex - root)).map fun k => root + k).map fun i =>
    (m[i]?.getD []).mapIdx fun j v =>
      if j < a[i]?.getD 0 then v + delta[j]?.getD 0 * phase else v

def expand? (rows : Nat) (m : Matrix) (index : Nat) : Option Matrix := do
  match m.getLast? with
  | none => return []
  | some last =>
    match lastPositive 0 last with
    | none => return m.dropLast
    | some row =>
      let table := parentTable rows m
      let final ← table.getLast?
      let root ← final.parents[row]?.join
      let rootCol ← m[root]?
      let a := thresholds table root row
      let delta := last.zipWith (· - ·) rootCol
      let copies := (List.range index).flatMap fun k => copy m a delta root (m.length - 1) (k + 1)
      return m.dropLast ++ copies

def seed (rows : Nat) : Matrix := [List.replicate rows 0, List.replicate rows 1]

theorem parentTableAux_length (rows : Nat) (context : ParentContext) (m : Matrix) :
    (parentTableAux rows context m).length = context.length + m.length := by
  induction m generalizing context with
  | nil => simp [parentTableAux]
  | cons c m ih => simp only [parentTableAux, ih, List.length_append,
      List.length_cons, List.length_nil]; omega

theorem parentTable_length (rows : Nat) (m : Matrix) :
    (parentTable rows m).length = m.length := by
  simpa [parentTable] using parentTableAux_length rows [] m

theorem parentTableAux_valid (rows : Nat) (context : ParentContext)
    (valid : Parents.ContextValid context) (m : Matrix) :
    Parents.ContextValid (parentTableAux rows context m) := by
  induction m generalizing context with
  | nil => exact valid
  | cons c m ih =>
    exact ih _ (Parents.context_valid_append_label rows context valid c)

theorem parentTable_valid (rows : Nat) (m : Matrix) :
    Parents.ContextValid (parentTable rows m) :=
  parentTableAux_valid rows [] Parents.empty_context_valid m

theorem parentTableAux_extends (rows : Nat) (context : ParentContext) (m : Matrix) :
    ∃ added, parentTableAux rows context m = context ++ added := by
  induction m generalizing context with
  | nil => exact ⟨[], by simp [parentTableAux]⟩
  | cons c m ih =>
    obtain ⟨added, h⟩ := ih (context ++ [Parents.label rows context c])
    exact ⟨Parents.label rows context c :: added, by simpa [parentTableAux, List.append_assoc] using h⟩

theorem parents_at_zero_cursor (context : ParentContext) (coordinates : List Nat)
    (row remaining : Nat) :
    Parents.rows context coordinates row remaining 0 = List.replicate remaining none := by
  induction remaining generalizing row with
  | zero => rfl
  | succ k ih => simp [Parents.rows, Parents.search, ih, List.replicate_succ]

theorem zero_seed_label (rows : Nat) :
    Parents.label rows [] (List.replicate rows 0) =
      ⟨List.replicate rows 0, List.replicate rows none⟩ := by
  simp [Parents.label, parents_at_zero_cursor]

private theorem replicate_zero_getD (rows j : Nat) :
    (List.replicate rows 0)[j]?.getD 0 = 0 := by
  simp only [List.getElem?_replicate]
  split <;> rfl

theorem one_seed_parents (rows row remaining : Nat) (bound : row + remaining ≤ rows) :
    Parents.rows [⟨List.replicate rows 0, List.replicate rows none⟩]
      (List.replicate rows 1) row remaining 1 = List.replicate remaining (some 0) := by
  induction remaining generalizing row with
  | zero => rfl
  | succ k ih =>
    have small : row < rows := by omega
    have search : Parents.search [⟨List.replicate rows 0, List.replicate rows none⟩]
        row ((List.replicate rows 1)[row]?.getD 0) 1 = some 0 := by
      rw [Parents.search]
      simp [small]
    rw [Parents.rows, search]
    simp only [List.replicate_succ, Option.map_some, Option.getD_some]
    rw [ih (row + 1) (by omega)]

theorem seed_parentTable (rows : Nat) :
    parentTable rows (seed rows) =
      [⟨List.replicate rows 0, List.replicate rows none⟩,
       ⟨List.replicate rows 1, List.replicate rows (some 0)⟩] := by
  simp only [parentTable, seed, parentTableAux, zero_seed_label, List.nil_append]
  simp only [Parents.label, List.length_cons, List.length_nil]
  rw [one_seed_parents rows 0 rows (by omega)]
  rfl

theorem lastPositive_zeros (start rows : Nat) :
    lastPositive start (List.replicate rows 0) = none := by
  induction rows generalizing start with
  | zero => rfl
  | succ rows ih => simp [List.replicate_succ, lastPositive, ih]

theorem lastPositive_ones (start rows : Nat) :
    lastPositive start (List.replicate (rows + 1) 1) = some (start + rows) := by
  induction rows generalizing start with
  | zero => simp [List.replicate_succ, lastPositive]
  | succ rows ih =>
    rw [List.replicate_succ, lastPositive, ih]
    simp [Nat.add_assoc, Nat.add_comm 1 rows]

theorem thresholds_seed_zero (rows top : Nat) :
    (thresholds (parentTable rows (seed rows)) 0 top)[0]? = some top := by
  rw [seed_parentTable]
  simp [thresholds, activation, List.range_succ]

theorem shifted_zero_column (rows phase : Nat) :
    (List.replicate (rows + 1) 0).mapIdx
      (fun j v => if j < rows then v + (List.replicate (rows + 1) 1)[j]?.getD 0 * phase else v) =
    List.replicate rows phase ++ [0] := by
  apply List.ext_getElem
  · simp
  · intro j hj hk
    have hj' : j < rows + 1 := by simpa using hj
    by_cases lower : j < rows
    · simp [List.getElem_mapIdx, lower, hj', List.getElem_append_left]
    · have same : j = rows := by omega
      subst j
      simp [List.getElem_mapIdx, List.getElem_append_right]

theorem seed_copy (rows phase : Nat) :
    copy (seed (rows + 1)) (thresholds (parentTable (rows + 1) (seed (rows + 1))) 0 rows)
      (List.replicate (rows + 1) 1) 0 1 phase = [List.replicate rows phase ++ [0]] := by
  simp only [copy, Nat.sub_zero, List.range_succ, List.range_zero, List.nil_append,
    List.map_cons, List.map_nil, Nat.add_zero]
  have look : (seed (rows + 1))[0]? = some (List.replicate (rows + 1) 0) := rfl
  simp only [look, thresholds_seed_zero, Option.getD_some, shifted_zero_column]

/-- The entire short fundamental sequence of the diagonal seed, for every
dimension and index, proved from the general copy algorithm. -/
theorem expand_seed (rows index : Nat) :
    expand? (rows + 1) (seed (rows + 1)) index =
      some ((List.range (index + 1)).map fun k => List.replicate rows k ++ [0]) := by
  have lastP : (parentTable (rows + 1) (seed (rows + 1))).getLast? =
      some ⟨List.replicate (rows + 1) 1, List.replicate (rows + 1) (some 0)⟩ := by
    rw [seed_parentTable]
    rfl
  unfold expand?
  simp only [seed, List.getLast?_cons_cons, List.getLast?_singleton]
  rw [lastPositive_ones]
  simp only [Nat.zero_add]
  change (do
    let final ← (parentTable (rows + 1) (seed (rows + 1))).getLast?
    let root ← final.parents[rows]?.join
    let rootCol ← (seed (rows + 1))[root]?
    let a := thresholds (parentTable (rows + 1) (seed (rows + 1))) root rows
    let delta := (List.replicate (rows + 1) 1).zipWith (· - ·) rootCol
    return (seed (rows + 1)).dropLast ++
      (List.range index).flatMap (fun k => copy (seed (rows + 1)) a delta root 1 (k + 1))) = _
  rw [lastP]
  simp only [Option.bind_eq_bind, Option.bind_some, List.getElem?_replicate, Nat.lt_succ_self, if_true,
    Option.join, id_eq]
  have look : (seed (rows + 1))[0]? = some (List.replicate (rows + 1) 0) := rfl
  simp only [look, Option.bind_some, Option.pure_def, List.zipWith_replicate', Nat.sub_zero]
  change some ((seed (rows + 1)).dropLast ++
    (List.range index).flatMap (fun k => copy (seed (rows + 1))
      (thresholds (parentTable (rows + 1) (seed (rows + 1))) 0 rows)
      (List.replicate (rows + 1) 1) 0 1 (k + 1))) = _
  simp only [seed_copy, ← List.map_eq_flatMap]
  congr 1
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map]
  have zeros : List.replicate (rows + 1) 0 = List.replicate rows 0 ++ [0] := by
    simpa using (List.replicate_append_replicate (n := rows) (m := 1) (a := 0)).symm
  simp [seed, zeros]

theorem expand_seed_projected (rows index : Nat) :
    (expand? (rows + 1) (seed (rows + 1)) index).map (List.map (List.take rows)) =
      some (diagonalMatrix rows (index + 1)) := by
  rw [expand_seed]
  simp [diagonalMatrix, List.map_map]

/-- This is the paper's `U_r = B_(r+1)[3]`, with the padded zero row
explicitly projected away rather than silently equating different matrices. -/
theorem ceiling_is_seed_child (d : Nat) :
    (expand? (d + 3) (seed (d + 3)) 3).map (List.map (List.take (d + 2))) =
      some (ceiling d) := by
  exact expand_seed_projected (d + 2) 3

end BTnSSBMS.BMS
