import BTnSSBMS.ParentValues

/-!
Geometry of the actual parent search: prefix locality, skipped-value
barriers, and extraction of the first edge of a finite ancestor path.
These are search theorems, not assumed properties of a parent relation.
-/
namespace BTnSSBMS.Parents

theorem search_prefix {small large : ParentContext} (initial : small <+: large)
    (row value cursor : Nat) (inside : cursor ≤ small.length) :
    search small row value cursor = search large row value cursor := by
  obtain ⟨tail, rfl⟩ := initial
  induction cursor using Nat.strongRecOn with
  | ind cursor ih =>
    cases cursor with
    | zero => simp only [search]
    | succ k =>
      have bound : k < small.length := by omega
      rw [search, search, List.getElem?_append_left bound]
      cases lookup : small[k]? with
      | none => rfl
      | some a =>
        by_cases smaller : a.coordinates[row]?.getD 0 < value
        · simp only [smaller, if_true]
        · simp only [smaller, if_false]
          cases row with
          | zero => exact ih k (by omega) (by omega)
          | succ row =>
            simp only []
            cases edge : a.parents[row]?.join with
            | none => rfl
            | some p =>
              by_cases earlier : p < k
              · simp only [earlier, if_true]
                exact ih (p + 1) (by omega) (by omega)
              · simp only [earlier, if_false]

theorem parent_zero_search {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (positive : 0 < d) (q : Nat)
    (inside : q < context.length) :
    parent context 0 q = search context 0 (reading context 0 q) q := by
  have computed := coherent q context[q] (List.getElem?_eq_getElem inside)
  have first : (label d (context.take q) context[q].coordinates).parents[0]?.join =
      search (context.take q) 0 (context[q].coordinates[0]?.getD 0) q := by
    cases d with
    | zero => omega
    | succ d => simp [label, rows, List.length_take, Nat.min_eq_left (Nat.le_of_lt inside)]
  have locality := search_prefix (List.take_prefix q context) 0
    (context[q].coordinates[0]?.getD 0) q (by simp [List.length_take]; omega)
  simpa only [parent, reading, List.getElem?_eq_getElem inside, Option.bind_some,
    Option.getD_some, computed, first] using locality

theorem parent_next_search {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context)
    {row q : Nat} (room : row + 1 < d) (inside : q < context.length) :
    parent context (row + 1) q = search context (row + 1) (reading context (row + 1) q)
      ((parent context row q).map (· + 1) |>.getD 0) := by
  let a := context[q]
  have lookup : context[q]? = some a := List.getElem?_eq_getElem inside
  have computed := coherent q a lookup
  have next := label_next d (context.take q) a.coordinates row room
  rw [← computed] at next
  cases lower : a.parents[row]?.join with
  | none => simpa only [parent, reading, lookup, Option.bind_some, Option.getD_some,
      lower, Option.map_none, Option.getD_none, search] using next
  | some p =>
    have edge : parent context row q = some p := by simp [parent, lookup, lower]
    have earlier := parent_earlier valid edge
    have locality := search_prefix (List.take_prefix q context) (row + 1)
      (a.coordinates[row + 1]?.getD 0) (p + 1) (by simp [List.length_take]; omega)
    simp only [lower, Option.map_some, Option.getD_some] at next
    simpa only [parent, reading, lookup, Option.bind_some, Option.getD_some,
      lower, Option.map_some] using next.trans locality

theorem Ancestor.first_child {context : ParentContext} {row root endpoint : Nat}
    (path : Ancestor context row root endpoint) (different : root ≠ endpoint) :
    ∃ child, parent context row child = some root ∧ Ancestor context row child endpoint := by
  induction path with
  | refl => exact False.elim (different rfl)
  | @up p q edge previous ih =>
    by_cases same : root = p
    · subst p
      exact ⟨q, edge, .refl _⟩
    · obtain ⟨child, first, tail⟩ := ih same
      exact ⟨child, first, .up edge tail⟩

theorem search_zero_barrier (context : ParentContext) (value cursor root position : Nat)
    (found : search context 0 value cursor = some root)
    (after : root < position) (before : position < cursor) :
    value ≤ reading context 0 position := by
  induction cursor with
  | zero => omega
  | succ cursor ih =>
    rw [search] at found
    cases lookup : context[cursor]? with
    | none => simp [lookup] at found
    | some a =>
      by_cases smaller : a.coordinates[0]?.getD 0 < value
      · have same : cursor = root := by simpa [lookup, smaller] using found
        omega
      · have next : search context 0 value cursor = some root := by
          simpa only [lookup, smaller, if_false] using found
        by_cases same : position = cursor
        · subst position
          simpa only [reading, lookup, Option.getD_some] using Nat.le_of_not_gt smaller
        · exact ih next (by omega)

theorem search_chain_barrier {context : ParentContext} (valid : ContextValid context)
    (row value start root position : Nat)
    (found : search context (row + 1) value (start + 1) = some root)
    (path : Ancestor context row position start) (after : root < position) :
    value ≤ reading context (row + 1) position := by
  induction start using Nat.strongRecOn with
  | ind start ih =>
    rw [search] at found
    cases lookup : context[start]? with
    | none => simp [lookup] at found
    | some a =>
      by_cases smaller : a.coordinates[row + 1]?.getD 0 < value
      · have same : start = root := by simpa [lookup, smaller] using found
        have bound := path.le valid
        omega
      · simp only [lookup, smaller, if_false] at found
        by_cases same : position = start
        · subst position
          simpa only [reading, lookup, Option.getD_some] using Nat.le_of_not_gt smaller
        · obtain ⟨p, edge, previous⟩ := (Ancestor.iff_parent same).mp path
          have selected : a.parents[row]?.join = some p := by simpa [parent, lookup] using edge
          have earlier := parent_earlier valid edge
          have next : search context (row + 1) value (p + 1) = some root := by
            simpa only [selected, earlier, if_true] using found
          exact ih p earlier next previous

theorem parent_chain_barrier {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context)
    {row root endpoint position : Nat} (room : row + 1 < d)
    (edge : parent context (row + 1) endpoint = some root)
    (path : Ancestor context row position endpoint) (after : root < position) :
    reading context (row + 1) endpoint ≤ reading context (row + 1) position := by
  by_cases same : position = endpoint
  · subst position; exact Nat.le_refl _
  · obtain ⟨p, lower, previous⟩ := (Ancestor.iff_parent same).mp path
    obtain ⟨a, lookup, _⟩ := Option.bind_eq_some_iff.mp edge
    have inside := (List.getElem?_eq_some_iff.mp lookup).choose
    have next := parent_next_search coherent valid room inside
    rw [edge, lower] at next
    exact search_chain_barrier valid row _ p root position (by simpa using next.symm) previous after

theorem parent_zero_barrier {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (positive : 0 < d)
    {root endpoint position : Nat} (edge : parent context 0 endpoint = some root)
    (after : root < position) (before : position < endpoint) :
    reading context 0 endpoint ≤ reading context 0 position := by
  obtain ⟨a, lookup, _⟩ := Option.bind_eq_some_iff.mp edge
  have inside := (List.getElem?_eq_some_iff.mp lookup).choose
  rw [parent_zero_search coherent positive endpoint inside] at edge
  exact search_zero_barrier context _ endpoint root position edge after before

theorem search_zero_exists_above (context : ParentContext) (value cursor root : Nat)
    (inside : cursor ≤ context.length) (before : root < cursor)
    (smaller : reading context 0 root < value) :
    ∃ found, root ≤ found ∧ search context 0 value cursor = some found := by
  induction cursor with
  | zero => omega
  | succ cursor ih =>
    have bound : cursor < context.length := by omega
    rw [search, List.getElem?_eq_getElem bound]
    by_cases small : context[cursor].coordinates[0]?.getD 0 < value
    · exact ⟨cursor, by omega, by simp only [small, if_true]⟩
    · have rootBefore : root < cursor := by
        by_cases same : root = cursor
        · subst root
          have contradiction : context[cursor].coordinates[0]?.getD 0 < value := by
            simpa only [reading, List.getElem?_eq_getElem bound, Option.getD_some] using smaller
          exact False.elim (small contradiction)
        · omega
      simp only [small, if_false]
      exact ih (by omega) rootBefore

theorem Ancestor.zero_interval {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context) (positive : 0 < d)
    {root endpoint : Nat} (path : Ancestor context 0 root endpoint) :
    root ≤ endpoint ∧ ∀ position, root < position → position ≤ endpoint →
      reading context 0 root < reading context 0 position := by
  induction path with
  | refl => exact ⟨Nat.le_refl _, by intro position after before; omega⟩
  | @up p q edge previous ih =>
    have earlier := parent_earlier valid edge
    have lower := previous.reading_le coherent
    have last := parent_reading_lt coherent edge
    refine ⟨by omega, ?_⟩
    intro position after before
    by_cases old : position ≤ p
    · exact ih.2 position after old
    · by_cases atEnd : position = q
      · subst position; omega
      · have barrier := parent_zero_barrier coherent positive edge
          (by omega : p < position) (by omega)
        omega

theorem ancestor_zero_of_interval {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context) (positive : 0 < d)
    {root endpoint : Nat} (inside : endpoint < context.length) (before : root ≤ endpoint)
    (interval : ∀ position, root < position → position ≤ endpoint →
      reading context 0 root < reading context 0 position) :
    Ancestor context 0 root endpoint := by
  induction endpoint using Nat.strongRecOn with
  | ind endpoint ih =>
    by_cases same : root = endpoint
    · subst endpoint; exact .refl _
    · obtain ⟨p, above, found⟩ := search_zero_exists_above context (reading context 0 endpoint)
        endpoint root (by omega) (by omega) (interval endpoint (by omega) (Nat.le_refl _))
      have edge : parent context 0 endpoint = some p := by
        rw [parent_zero_search coherent positive endpoint inside]
        exact found
      have earlier := parent_earlier valid edge
      exact .up edge (ih p earlier (by omega) above (fun position h1 h2 => interval position h1 (by omega)))

/-- In the actual row-zero parent forest, descendants occupy exactly
the uninterrupted interval of columns whose zero-coordinate exceeds root. -/
theorem ancestor_zero_iff_interval {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context) (positive : 0 < d)
    {root endpoint : Nat} (inside : endpoint < context.length) :
    Ancestor context 0 root endpoint ↔ root ≤ endpoint ∧
      ∀ position, root < position → position ≤ endpoint →
        reading context 0 root < reading context 0 position :=
  ⟨fun path => path.zero_interval coherent valid positive,
    fun interval => ancestor_zero_of_interval coherent valid positive inside interval.1 interval.2⟩

end BTnSSBMS.Parents
