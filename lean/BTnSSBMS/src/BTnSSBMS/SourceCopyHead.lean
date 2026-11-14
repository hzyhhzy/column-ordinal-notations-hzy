import BTnSSBMS.SourcePruning

/-!
The first-copy head in a low numerical branch. All parents below are
computed by the real search. No source block inequalities are needed for
this part of the ordinary-copy transport table.
-/
namespace BTnSSBMS.Parents

/-- Lowering a successful query to at most its answer's value skips
exactly the old corridor before reaching that answer again. -/
theorem search_lower_at_selected (context : ParentContext) (row large small cursor root : Nat)
    (selected : search context row large cursor = some root)
    (lower : small ≤ reading context row root) :
    search context row small cursor = search context row small (root + 1) := by
  induction cursor using Nat.strongRecOn with
  | ind cursor ih =>
    cases cursor with
    | zero => simp [search] at selected
    | succ k =>
      obtain ⟨r, atRoot, rootSmall⟩ := search_smaller context row large (k + 1) root selected
      have ordered : small < large := by
        have readRoot : reading context row root = r.coordinates[row]?.getD 0 := by
          simp [reading, atRoot]
        omega
      rw [search] at selected
      cases atK : context[k]? with
      | none => simp [atK] at selected
      | some a =>
        by_cases hit : a.coordinates[row]?.getD 0 < large
        · have same : k = root := by simpa only [atK, hit, if_true, Option.some.injEq] using selected
          subst k
          rfl
        · have noHit : ¬ a.coordinates[row]?.getD 0 < small := by omega
          simp only [atK, hit, if_false] at selected
          rw [search]
          simp only [atK, noHit, if_false]
          cases row with
          | zero => exact ih k (by omega) selected
          | succ row =>
            cases parent : a.parents[row]?.join with
            | none => simp [parent] at selected
            | some p =>
              by_cases before : p < k
              · simp only [parent, before, if_true] at selected ⊢
                exact ih (p + 1) (by omega) selected
              · simp [parent, before] at selected

/-- Querying a column's own value starting at that column bypasses it
and returns its actual parent, including the no-parent case. -/
theorem search_own_value {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context)
    {row root : Nat} (room : row < d) (inside : root < context.length) :
    search context row (reading context row root) (root + 1) = parent context row root := by
  have atRoot : context[root]? = some context[root] := List.getElem?_eq_getElem inside
  have value : reading context row root = context[root].coordinates[row]?.getD 0 := by
    simp only [reading, atRoot, Option.getD_some]
  rw [search]
  simp only [atRoot, ← value, Nat.lt_irrefl, if_false]
  cases row with
  | zero => exact (parent_zero_search coherent room root inside).symm
  | succ row =>
    have next := parent_next_search coherent valid room inside
    cases edge : context[root].parents[row]?.join with
    | none =>
      have missing : parent context row root = none := by simp [parent, atRoot, edge]
      simpa only [edge, missing, Option.map_none, Option.getD_none, search] using next.symm
    | some p =>
      have found : parent context row root = some p := by simp [parent, atRoot, edge]
      have earlier := parent_earlier valid found
      simpa only [edge, earlier, if_true, found, Option.map_some, Option.getD_some] using next.symm

theorem label_parents_congr_through (d : Nat) (context : ParentContext) (a b : List Nat)
    (row : Nat) (room : row < d)
    (same : ∀ j, j ≤ row → a[j]?.getD 0 = b[j]?.getD 0) :
    (label d context a).parents[row]?.join = (label d context b).parents[row]?.join := by
  induction row with
  | zero => rw [label_zero d context a room, label_zero d context b room, same 0 (by omega)]
  | succ row ih =>
    rw [label_next d context a row room, label_next d context b row room,
      same (row + 1) (by omega), ih (by omega) (fun j hj => same j (by omega))]

/-- The complete first-copy input table: lower rows inherit the removed
terminal's parents, and all other rows inherit the old root's parents. -/
theorem first_copy_head_parents {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context)
    (terminal head : List Nat) {branch root : Nat} (room : branch < d)
    (selected : (label d context terminal).parents[branch]?.join = some root)
    (low : ∀ j, j < branch → head[j]?.getD 0 = terminal[j]?.getD 0)
    (high : ∀ j, branch ≤ j → j < d → head[j]?.getD 0 = reading context j root)
    (row : Nat) (inside : row < d) :
    (label d context head).parents[row]?.join =
      if row < branch then (label d context terminal).parents[row]?.join else parent context row root := by
  have rootBound := label_parent_bound d context terminal branch root selected
  by_cases below : row < branch
  · simp only [below, if_true]
    exact label_parents_congr_through d context head terminal row inside (fun j hj => low j (by omega))
  · simp only [below, if_false]
    have base : (label d context head).parents[branch]?.join = parent context branch root := by
      cases branch with
      | zero =>
        rw [label_zero d context terminal room] at selected
        rw [label_zero d context head room, high 0 (by omega) room]
        exact (search_lower_at_selected context 0 _ _ _ root selected (Nat.le_refl _)).trans
          (search_own_value coherent valid room rootBound)
      | succ branch =>
        rw [label_next d context terminal branch room] at selected
        have previous := label_parents_congr_through d context head terminal branch (by omega)
          (fun j hj => low j (by omega))
        rw [label_next d context head branch room, previous, high (branch + 1) (by omega) room]
        exact (search_lower_at_selected context (branch + 1) _ _ _ root selected (Nat.le_refl _)).trans
          (search_own_value coherent valid room rootBound)
    induction row with
    | zero =>
      have same : branch = 0 := by omega
      subst branch
      exact base
    | succ row ih =>
      by_cases same : branch = row + 1
      · subst branch; exact base
      · rw [label_next d context head row inside, ih (by omega) (by omega),
          high (row + 1) (by omega) inside]
        exact (parent_next_search coherent valid inside rootBound).symm

theorem first_copy_head_unitSteps {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context)
    (unit : UnitSteps d context) (terminal head : List Nat)
    (terminalUnit : UnitSteps d (context ++ [label d context terminal]))
    {branch root : Nat} (room : branch < d)
    (selected : (label d context terminal).parents[branch]?.join = some root)
    (low : ∀ j, j < branch → head[j]?.getD 0 = terminal[j]?.getD 0)
    (high : ∀ j, branch ≤ j → j < d → head[j]?.getD 0 = reading context j root) :
    UnitSteps d (context ++ [label d context head]) := by
  have rootBound := label_parent_bound d context terminal branch root selected
  apply unit.extend_one (context_valid_append_label d context valid head) (List.prefix_append _ _)
    (by simp)
  intro j inside
  rw [reading_append_label, append_label_parent,
    first_copy_head_parents coherent valid terminal head room selected low high j inside]
  by_cases below : j < branch
  · rw [if_pos below, low j below]
    have equation := terminalUnit context.length (by simp) j inside
    rw [reading_append_label, append_label_parent] at equation
    rw [equation]
    cases edge : (label d context terminal).parents[j]?.join with
    | none => rfl
    | some p =>
      simp only [Option.map_some, Option.getD_some]
      have bound := label_parent_bound d context terminal j p edge
      rw [← reading_prefix (List.prefix_append context [label d context terminal]) j p bound,
        ← reading_prefix (List.prefix_append context [label d context head]) j p bound]
  · rw [if_neg below, high j (by omega) inside, unit root rootBound j inside]
    cases edge : parent context j root with
    | none => rfl
    | some p =>
      simp only [Option.map_some, Option.getD_some]
      have before := parent_earlier valid edge
      exact congrArg (· + 1) (reading_prefix (List.prefix_append _ _) j p (by omega))

theorem label_root_lower_value {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context)
    (terminal : List Nat) {branch root : Nat} (room : branch < d)
    (selected : (label d context terminal).parents[branch]?.join = some root)
    {j : Nat} (below : j ≤ branch) : reading context j root < terminal[j]?.getD 0 := by
  let next := context ++ [label d context terminal]
  have edge : parent next branch context.length = some root := by
    rw [append_label_parent]
    exact selected
  have nextCoherent := coherent_append_label coherent terminal
  have nextValid := context_valid_append_label d context valid terminal
  have earlier := parent_earlier nextValid edge
  have path : Ancestor next branch root context.length := .up edge (.refl _)
  have smaller := (path.lower_row nextCoherent room below).reading_lt nextCoherent (by omega)
  rw [reading_append_label,
    ← reading_prefix (List.prefix_append context [label d context terminal]) j root earlier] at smaller
  exact smaller

end BTnSSBMS.Parents

namespace BTnSSBMS.Source

theorem shift_value (a delta : List Nat) (threshold phase j : Nat) (inside : j < a.length) :
    (shift a threshold delta phase)[j]?.getD 0 =
      a[j]?.getD 0 + if j < threshold then delta[j]?.getD 0 * phase else 0 := by
  simp only [shift, List.getElem?_mapIdx, List.getElem?_eq_getElem inside, Option.map_some, Option.getD_some]

theorem shift_width (a delta : List Nat) (threshold phase : Nat) :
    (shift a threshold delta phase).length = a.length := by simp [shift]

/-- Exactly the low-branch first copy's `shift` and `delta` expressions
from Source.expand?, with real Nat differences justified by ancestry. -/
theorem shifted_copy_head_values {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    (terminal : List Nat) {branch root : Nat} (room : branch < d)
    (selected : (Parents.label d context terminal).parents[branch]?.join = some root)
    (width : (context[root]?.getD default).coordinates.length = d) :
    let rootCoordinates := (context[root]?.getD default).coordinates
    let delta := (List.range branch).map (fun j => terminal[j]?.getD 0 - rootCoordinates[j]?.getD 0)
    let head := shift rootCoordinates branch delta 1
    (∀ j, j < branch → head[j]?.getD 0 = terminal[j]?.getD 0) ∧
    (∀ j, branch ≤ j → j < d → head[j]?.getD 0 = Parents.reading context j root) := by
  dsimp only
  constructor
  · intro j below
    rw [shift_value _ _ branch 1 j (by omega), if_pos below]
    simp only [List.getElem?_map, List.getElem?_range below, Option.map_some, Option.getD_some, Nat.mul_one]
    have smaller := Parents.label_root_lower_value coherent valid terminal room selected (by omega : j ≤ branch)
    change (context[root]?.getD default).coordinates[j]?.getD 0 < terminal[j]?.getD 0 at smaller
    omega
  · intro j above inside
    rw [shift_value _ _ branch 1 j (by omega), if_neg (by omega), Nat.add_zero]
    rfl

theorem shifted_copy_head_parents {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    (terminal : List Nat) {branch root : Nat} (room : branch < d)
    (selected : (Parents.label d context terminal).parents[branch]?.join = some root)
    (width : (context[root]?.getD default).coordinates.length = d) :
    let rootCoordinates := (context[root]?.getD default).coordinates
    let delta := (List.range branch).map (fun j => terminal[j]?.getD 0 - rootCoordinates[j]?.getD 0)
    let head := shift rootCoordinates branch delta 1
    ∀ j, j < d → (Parents.label d context head).parents[j]?.join =
      if j < branch then (Parents.label d context terminal).parents[j]?.join
      else Parents.parent context j root := by
  have values := shifted_copy_head_values coherent valid terminal room selected width
  exact Parents.first_copy_head_parents coherent valid terminal _ room selected values.1 values.2

theorem shifted_copy_head_unitSteps {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    (unit : Parents.UnitSteps d context) (terminal : List Nat)
    (terminalUnit : Parents.UnitSteps d (context ++ [Parents.label d context terminal]))
    {branch root : Nat} (room : branch < d)
    (selected : (Parents.label d context terminal).parents[branch]?.join = some root)
    (width : (context[root]?.getD default).coordinates.length = d) :
    let rootCoordinates := (context[root]?.getD default).coordinates
    let delta := (List.range branch).map (fun j => terminal[j]?.getD 0 - rootCoordinates[j]?.getD 0)
    let head := shift rootCoordinates branch delta 1
    Parents.UnitSteps d (context ++ [Parents.label d context head]) := by
  have values := shifted_copy_head_values coherent valid terminal room selected width
  exact Parents.first_copy_head_unitSteps coherent valid unit terminal _ terminalUnit room selected values.1 values.2

end BTnSSBMS.Source
