import BTnSSBMS.SearchGeometry

/-!
Record-chain geometry of computed parents. A higher parent is an ancestor
in that higher row of every lower-row candidate skipped on the way to it.
This is needed when a source parent edge is stretched into target edges:
value bounds then follow from actual ancestry, not merely from pointer tags.
-/
namespace BTnSSBMS.Parents

theorem Ancestor.comparable {context : ParentContext} {row a b endpoint : Nat}
    (left : Ancestor context row a endpoint) (right : Ancestor context row b endpoint) :
    Ancestor context row a b ∨ Ancestor context row b a := by
  induction left generalizing b with
  | refl => exact Or.inr right
  | @up p q edge previous ih =>
    by_cases same : b = q
    · subst b
      exact Or.inl (.up edge previous)
    · obtain ⟨r, other, path⟩ := (Ancestor.iff_parent same).mp right
      have equal : r = p := Option.some.inj (other.symm.trans edge)
      subst r
      exact ih path

theorem Ancestor.between {context : ParentContext} (valid : ContextValid context)
    {row a b endpoint : Nat} (left : Ancestor context row a endpoint)
    (right : Ancestor context row b endpoint) (before : a ≤ b) :
    Ancestor context row a b := by
  rcases left.comparable right with forward | backward
  · exact forward
  · have reverse := backward.le valid
    have same : a = b := by omega
    subst b
    exact .refl _

theorem search_chain_exists_above {context : ParentContext} (valid : ContextValid context)
    (row value start root : Nat) (inside : start < context.length)
    (path : Ancestor context row root start) (smaller : reading context (row + 1) root < value) :
    ∃ found, Ancestor context row root found ∧
      search context (row + 1) value (start + 1) = some found := by
  induction start using Nat.strongRecOn with
  | ind start ih =>
    rw [search, List.getElem?_eq_getElem inside]
    by_cases small : context[start].coordinates[row + 1]?.getD 0 < value
    · exact ⟨start, path, by simp only [small, if_true]⟩
    · have different : root ≠ start := by
        intro same
        subst root
        have contradiction : context[start].coordinates[row + 1]?.getD 0 < value := by
          simpa only [reading, List.getElem?_eq_getElem inside, Option.getD_some] using smaller
        exact small contradiction
      obtain ⟨p, edge, previous⟩ := (Ancestor.iff_parent different).mp path
      have selected : context[start].parents[row]?.join = some p := by
        simpa only [parent, List.getElem?_eq_getElem inside, Option.bind_some] using edge
      have earlier := parent_earlier valid edge
      simp only [small, if_false, selected, earlier, if_true]
      exact ih p earlier (by omega) previous

/-- A lower-row ancestor whose next-row value is smaller is never passed
by the next-row parent search. -/
theorem higher_parent_within {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context)
    {row root endpoint : Nat} (room : row + 1 < d) (inside : endpoint < context.length)
    (path : Ancestor context row root endpoint) (strict : root ≠ endpoint)
    (smaller : reading context (row + 1) root < reading context (row + 1) endpoint) :
    ∃ p, parent context (row + 1) endpoint = some p ∧ Ancestor context row root p := by
  obtain ⟨p, edge, previous⟩ := (Ancestor.iff_parent strict).mp path
  have earlier := parent_earlier valid edge
  obtain ⟨found, above, result⟩ := search_chain_exists_above valid row _ p root (by omega) previous smaller
  refine ⟨found, ?_, above⟩
  rw [parent_next_search coherent valid room inside, edge]
  simpa only [Option.map_some, Option.getD_some] using result

/-- A strict value barrier on the lower-row path forces higher-row
ancestry. This is derived from the executable search, not postulated. -/
theorem higher_ancestor_of_barrier {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context)
    {row root endpoint : Nat} (room : row + 1 < d) (inside : endpoint < context.length)
    (path : Ancestor context row root endpoint)
    (barrier : ∀ position, root < position → Ancestor context row position endpoint →
      reading context (row + 1) root < reading context (row + 1) position) :
    Ancestor context (row + 1) root endpoint := by
  induction endpoint using Nat.strongRecOn with
  | ind endpoint ih =>
    by_cases same : root = endpoint
    · subst endpoint
      exact .refl _
    · have before : root < endpoint := by have bound := path.le valid; omega
      obtain ⟨p, edge, above⟩ := higher_parent_within coherent valid room inside path same
        (barrier endpoint before (.refl _))
      have earlier := parent_earlier valid edge
      have lower : Ancestor context row p endpoint := higher_parent_path coherent room edge
      apply Ancestor.up edge
      apply ih p earlier (by omega) above
      intro position after tail
      exact barrier position after (tail.trans lower)

theorem Ancestor.higher_barrier {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context)
    {row root endpoint : Nat} (room : row + 1 < d)
    (path : Ancestor context (row + 1) root endpoint) :
    ∀ position, root < position → Ancestor context row position endpoint →
      reading context (row + 1) root < reading context (row + 1) position := by
  induction path with
  | refl =>
    intro position after tail
    have before := tail.le valid
    omega
  | @up p q edge previous ih =>
    intro position after tail
    have lower : Ancestor context row p q := higher_parent_path coherent room edge
    by_cases before : position ≤ p
    · exact ih position after (tail.between valid lower before)
    · have barrier := parent_chain_barrier coherent valid room edge tail (by omega : p < position)
      have start := previous.reading_le coherent
      have last := parent_reading_lt coherent edge
      omega

theorem higher_ancestor_iff_barrier {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context)
    {row root endpoint : Nat} (room : row + 1 < d) (inside : endpoint < context.length) :
    Ancestor context (row + 1) root endpoint ↔
      Ancestor context row root endpoint ∧
      ∀ position, root < position → Ancestor context row position endpoint →
        reading context (row + 1) root < reading context (row + 1) position :=
  ⟨fun path => ⟨path.previous_row coherent room, path.higher_barrier coherent valid room⟩,
    fun h => higher_ancestor_of_barrier coherent valid room inside h.1 h.2⟩

/-- Every skipped lower-row candidate belongs to the higher-row cone of
the selected parent. Thus stretched higher-row parent edges preserve the
strict value barrier needed by the target search. -/
theorem selected_parent_covers_path {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context)
    {row root endpoint position : Nat} (room : row + 1 < d)
    (edge : parent context (row + 1) endpoint = some root)
    (path : Ancestor context row position endpoint) (after : root ≤ position) :
    Ancestor context (row + 1) root position := by
  have lower := higher_parent_path coherent room edge
  have above : Ancestor context row root position := lower.between valid path after
  obtain ⟨a, lookup, _⟩ := Option.bind_eq_some_iff.mp edge
  have endpointBound := (List.getElem?_eq_some_iff.mp lookup).choose
  have positionBound : position < context.length := by have bound := path.le valid; omega
  apply higher_ancestor_of_barrier coherent valid room positionBound above
  intro q strictly tail
  have barrier := parent_chain_barrier coherent valid room edge (tail.trans path) strictly
  have first := parent_reading_lt coherent edge
  omega

theorem parent_prefix_eq {small large : ParentContext} (initial : small <+: large)
    (row position : Nat) (inside : position < small.length) :
    parent small row position = parent large row position := by
  obtain ⟨tail, rfl⟩ := initial
  simp only [parent, List.getElem?_append_left inside]

theorem Ancestor.restrict {small large : ParentContext} (initial : small <+: large)
    (valid : ContextValid large) {row root endpoint : Nat}
    (path : Ancestor large row root endpoint) (inside : endpoint < small.length) :
    Ancestor small row root endpoint := by
  induction path with
  | refl => exact .refl _
  | @up p q edge previous ih =>
    have earlier := parent_earlier valid edge
    exact .up ((parent_prefix_eq initial row q inside).trans edge) (ih (by omega))

/-- Querying one above an ancestor's value returns that very ancestor.
The source-to-target numerical parent bridge uses this for stretched paths. -/
theorem search_ancestor_successor {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context)
    {row root endpoint : Nat} (room : row < d) (inside : endpoint < context.length)
    (path : Ancestor context row root endpoint) :
    search context row (reading context row root + 1) (endpoint + 1) = some root := by
  cases row with
  | zero =>
    have before := path.le valid
    obtain ⟨found, above, result⟩ := search_zero_exists_above context (reading context 0 root + 1)
      (endpoint + 1) root (by omega) (by omega) (by omega)
    have foundBound := (search_bounds context 0 _ (endpoint + 1) found result).1
    obtain ⟨a, lookup, smaller⟩ := search_smaller context 0 _ (endpoint + 1) found result
    have foundSmall : reading context 0 found < reading context 0 root + 1 := by
      simpa only [reading, lookup, Option.getD_some] using smaller
    have same : found = root := by
      by_cases strict : root < found
      · have barrier := (path.zero_interval coherent valid (by omega)).2 found strict (by omega)
        omega
      · omega
    simpa only [same] using result
  | succ row =>
    have lower := path.previous_row coherent room
    obtain ⟨found, above, result⟩ := search_chain_exists_above valid row
      (reading context (row + 1) root + 1) endpoint root inside lower (by omega)
    have previous := search_path context row _ endpoint found result
    obtain ⟨a, lookup, smaller⟩ := search_smaller context (row + 1) _ (endpoint + 1) found result
    have foundSmall : reading context (row + 1) found < reading context (row + 1) root + 1 := by
      simpa only [reading, lookup, Option.getD_some] using smaller
    have before := above.le valid
    have same : found = root := by
      by_cases strict : root < found
      · have barrier := path.higher_barrier coherent valid room found strict previous
        omega
      · omega
    simpa only [same] using result

theorem selected_zero_parent_covers_interval {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context) (positive : 0 < d)
    {root endpoint position : Nat} (edge : parent context 0 endpoint = some root)
    (after : root ≤ position) (before : position < endpoint) :
    Ancestor context 0 root position := by
  obtain ⟨a, lookup, _⟩ := Option.bind_eq_some_iff.mp edge
  have endpointBound := (List.getElem?_eq_some_iff.mp lookup).choose
  apply ancestor_zero_of_interval coherent valid positive (by omega) after
  intro q strictly bounded
  have barrier := parent_zero_barrier coherent positive edge strictly (by omega : q < endpoint)
  have head := parent_reading_lt coherent edge
  omega

theorem append_label_parent (d : Nat) (context : ParentContext) (coordinates : List Nat) (row : Nat) :
    parent (context ++ [label d context coordinates]) row context.length =
      (label d context coordinates).parents[row]?.join := by
  simp only [parent, List.getElem?_concat_length, Option.bind_some]

/-- Before appending a numerical source label, its row-zero selected
parent is already an ancestor of the current frontier. -/
theorem label_zero_parent_frontier {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context) (positive : 0 < d)
    (coordinates : List Nat) {root : Nat}
    (selected : (label d context coordinates).parents[0]?.join = some root) :
    Ancestor context 0 root (context.length - 1) := by
  have edge : parent (context ++ [label d context coordinates]) 0 context.length = some root := by
    rw [append_label_parent]; exact selected
  have nextValid := context_valid_append_label d context valid coordinates
  have before := parent_earlier nextValid edge
  have path := selected_zero_parent_covers_interval (coherent_append_label coherent coordinates)
    nextValid positive edge (by omega : root ≤ context.length - 1) (by omega)
  exact path.restrict (List.prefix_append _ _) nextValid (by omega)

/-- If the new source label selects root at row j+1, the preceding-row
candidate exists and is already a row-(j+1) descendant of root. -/
theorem label_higher_parent_frontier {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context)
    (coordinates : List Nat) {row root : Nat} (room : row + 1 < d)
    (selected : (label d context coordinates).parents[row + 1]?.join = some root) :
    ∃ previous, (label d context coordinates).parents[row]?.join = some previous ∧
      Ancestor context (row + 1) root previous := by
  have next := label_next d context coordinates row room
  rw [selected] at next
  cases lower : (label d context coordinates).parents[row]?.join with
  | none => simp [lower, search] at next
  | some previous =>
    have result : search context (row + 1) (coordinates[row + 1]?.getD 0)
        (previous + 1) = some root := by simpa only [lower, Option.map_some, Option.getD_some] using next.symm
    have previousBound : previous < context.length :=
      label_parents_earlier d context coordinates previous (by
        cases lookup : (label d context coordinates).parents[row]? with
        | none => simp [lookup] at lower
        | some entry =>
          have same : entry = some previous := by simpa only [lookup, Option.join_some] using lower
          exact same ▸ List.mem_of_getElem? lookup)
    have nextValid := context_valid_append_label d context valid coordinates
    have nextCoherent := coherent_append_label coherent coordinates
    have highEdge : parent (context ++ [label d context coordinates]) (row + 1) context.length = some root := by
      rw [append_label_parent]; exact selected
    have lowEdge : parent (context ++ [label d context coordinates]) row context.length = some previous := by
      rw [append_label_parent]; exact lower
    have startPath := search_path context row _ previous root result
    have path := selected_parent_covers_path nextCoherent nextValid room highEdge
      (Ancestor.up lowEdge (.refl _)) (startPath.le valid)
    exact ⟨previous, rfl, path.restrict (List.prefix_append _ _) nextValid previousBound⟩

end BTnSSBMS.Parents
