import BTnSSBMS.BMS

/-!
Finite parent-chain inclusion for the actual numerical search. Every higher
parent edge expands into a nonempty path in the previous row. No block
invariant, standardness or well-foundedness assumption is used.
-/
namespace BTnSSBMS.Parents

def parent (context : ParentContext) (row position : Nat) : Option Nat :=
  (context[position]?).bind fun a => a.parents[row]?.join

inductive Ancestor (context : ParentContext) (row : Nat) : Nat → Nat → Prop
  | refl (p : Nat) : Ancestor context row p p
  | up {root p q : Nat} : parent context row q = some p →
      Ancestor context row root p → Ancestor context row root q

theorem Ancestor.trans {context : ParentContext} {row a b c : Nat}
    (ab : Ancestor context row a b) (bc : Ancestor context row b c) :
    Ancestor context row a c := by
  induction bc with
  | refl => exact ab
  | up edge _ ih => exact .up edge ih

theorem parent_earlier {context : ParentContext} (valid : ContextValid context)
    {row p q : Nat} (found : parent context row q = some p) : p < q := by
  obtain ⟨a, lookup, hit⟩ := Option.bind_eq_some_iff.mp found
  have member : some p ∈ a.parents := by
    cases atRow : a.parents[row]? with
    | none => simp [atRow] at hit
    | some entry =>
      have same : entry = some p := by simpa [atRow] using hit
      exact same ▸ List.mem_of_getElem? atRow
  exact valid q a lookup p member

theorem Ancestor.le {context : ParentContext} (valid : ContextValid context)
    {row a b : Nat} (path : Ancestor context row a b) : a ≤ b := by
  induction path with
  | refl => exact Nat.le_refl _
  | up edge _ ih => have strict := parent_earlier valid edge; omega

theorem parent_prefix {small large : ParentContext} (initial : small <+: large)
    {row p q : Nat} (edge : parent small row q = some p) :
    parent large row q = some p := by
  obtain ⟨tail, rfl⟩ := initial
  obtain ⟨a, lookup, hit⟩ := Option.bind_eq_some_iff.mp edge
  have bound := (List.getElem?_eq_some_iff.mp lookup).choose
  simp only [parent, List.getElem?_append_left bound, lookup, Option.bind_some, hit]

theorem Ancestor.prefix {small large : ParentContext} (initial : small <+: large)
    {row a b : Nat} (path : Ancestor small row a b) : Ancestor large row a b := by
  induction path with
  | refl => exact .refl _
  | up edge _ ih => exact .up (parent_prefix initial edge) ih

theorem search_path (context : ParentContext) (row value start found : Nat)
    (hit : search context (row + 1) value (start + 1) = some found) :
    Ancestor context row found start := by
  induction start using Nat.strongRecOn with
  | ind start ih =>
    rw [search] at hit
    cases lookup : context[start]? with
    | none => simp [lookup] at hit
    | some a =>
      by_cases smaller : a.coordinates[row + 1]?.getD 0 < value
      · have same : found = start := by simpa [lookup, smaller] using hit.symm
        subst found
        exact .refl _
      · simp only [lookup, smaller, if_false] at hit
        cases edge : a.parents[row]?.join with
        | none => simp [edge] at hit
        | some p =>
          by_cases earlier : p < start
          · have next : search context (row + 1) value (p + 1) = some found := by
              simpa only [edge, earlier, if_true] using hit
            exact .up (by simp only [parent, lookup, Option.bind_some, edge]) (ih p earlier next)
          · simp [edge, earlier] at hit

theorem search_smaller (context : ParentContext) (row value cursor found : Nat)
    (hit : search context row value cursor = some found) :
    ∃ a, context[found]? = some a ∧ a.coordinates[row]?.getD 0 < value := by
  induction cursor using Nat.strongRecOn with
  | ind cursor ih =>
    cases cursor with
    | zero => simp [search] at hit
    | succ k =>
      rw [search] at hit
      cases lookup : context[k]? with
      | none => simp [lookup] at hit
      | some a =>
        by_cases smaller : a.coordinates[row]?.getD 0 < value
        · have same : found = k := by simpa [lookup, smaller] using hit.symm
          subst found
          exact ⟨a, lookup, smaller⟩
        · simp only [lookup, smaller, if_false] at hit
          cases row with
          | zero => exact ih k (by omega) hit
          | succ row =>
            cases edge : a.parents[row]?.join with
            | none => simp [edge] at hit
            | some p =>
              by_cases earlier : p < k
              · have next : search context (row + 1) value (p + 1) = some found := by
                  simpa only [edge, earlier, if_true] using hit
                exact ih (p + 1) (by omega) next
              · simp [edge, earlier] at hit

theorem search_zero (context : ParentContext) (row cursor : Nat) :
    search context row 0 cursor = none := by
  cases result : search context row 0 cursor with
  | none => rfl
  | some found => obtain ⟨_, _, impossible⟩ := search_smaller context row 0 cursor found result; omega

theorem rows_next (context : ParentContext) (coordinates : List Nat)
    (row remaining cursor offset : Nat) (room : offset + 1 < remaining) :
    (rows context coordinates row remaining cursor)[offset + 1]?.join =
      search context (row + offset + 1) (coordinates[row + offset + 1]?.getD 0)
        (((rows context coordinates row remaining cursor)[offset]?.join).map (· + 1) |>.getD 0) := by
  induction offset generalizing row remaining cursor with
  | zero =>
    cases remaining with
    | zero => omega
    | succ remaining =>
      cases remaining with
      | zero => omega
      | succ remaining => simp [rows]
  | succ offset ih =>
    cases remaining with
    | zero => omega
    | succ remaining =>
      simpa only [rows, List.getElem?_cons_succ, Nat.add_assoc, Nat.add_left_comm] using
        ih (row + 1) remaining
          ((search context row (coordinates[row]?.getD 0) cursor).map (· + 1) |>.getD 0)
          (by omega)

theorem label_next (d : Nat) (context : ParentContext) (coordinates : List Nat)
    (j : Nat) (room : j + 1 < d) :
    (label d context coordinates).parents[j + 1]?.join =
      search context (j + 1) (coordinates[j + 1]?.getD 0)
        (((label d context coordinates).parents[j]?.join).map (· + 1) |>.getD 0) := by
  simpa only [label, Nat.zero_add] using rows_next context coordinates 0 d context.length j room

/-- Each position stores the annotation computed in its actual prefix. -/
def Coherent (d : Nat) (context : ParentContext) : Prop :=
  ∀ i a, context[i]? = some a →
    a.parents = (label d (context.take i) a.coordinates).parents

theorem empty_coherent (d : Nat) : Coherent d [] := by
  intro i a lookup
  simp at lookup

theorem coherent_append_label {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (coordinates : List Nat) :
    Coherent d (context ++ [label d context coordinates]) := by
  intro i a lookup
  by_cases old : i < context.length
  · rw [List.getElem?_append_left old] at lookup
    rw [List.take_append_of_le_length (by omega)]
    exact coherent i a lookup
  · have bound := (List.getElem?_eq_some_iff.mp lookup).choose
    have atEnd : i = context.length := by
      simp only [List.length_append, List.length_cons, List.length_nil] at bound
      omega
    subst i
    have same : a = label d context coordinates := by simpa using lookup.symm
    subst a
    simp only [List.take_left, label]

theorem higher_parent_path {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) {row p q : Nat} (room : row + 1 < d)
    (higher : parent context (row + 1) q = some p) : Ancestor context row p q := by
  obtain ⟨a, lookup, hit⟩ := Option.bind_eq_some_iff.mp higher
  have computation := coherent q a lookup
  have next := label_next d (context.take q) a.coordinates row room
  rw [← computation] at next
  rw [hit] at next
  cases lower : a.parents[row]?.join with
  | none => simp [lower, search] at next
  | some r =>
    have result : search (context.take q) (row + 1) (a.coordinates[row + 1]?.getD 0)
        (r + 1) = some p := by simpa only [lower, Option.map_some, Option.getD_some] using next.symm
    have older := (search_path (context.take q) row _ r p result).prefix (List.take_prefix ..)
    exact .up (by simp only [parent, lookup, Option.bind_some, lower]) older

theorem Ancestor.previous_row {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) {row a b : Nat} (room : row + 1 < d)
    (path : Ancestor context (row + 1) a b) : Ancestor context row a b := by
  induction path with
  | refl => exact .refl _
  | up edge _ ih => exact ih.trans (higher_parent_path coherent room edge)

theorem Ancestor.lower_row {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) {lower upper a b : Nat} (room : upper < d)
    (rows : lower ≤ upper) (path : Ancestor context upper a b) : Ancestor context lower a b := by
  induction upper generalizing lower with
  | zero =>
    have same : lower = 0 := by omega
    subst lower
    exact path
  | succ upper ih =>
    by_cases same : lower = upper + 1
    · subst lower; exact path
    · exact ih (by omega) (by omega) (path.previous_row coherent room)

end BTnSSBMS.Parents

namespace BTnSSBMS.BMS

theorem parentTableAux_coherent (d : Nat) (context : ParentContext) (m : Matrix)
    (coherent : Parents.Coherent d context) : Parents.Coherent d (parentTableAux d context m) := by
  induction m generalizing context with
  | nil => exact coherent
  | cons a m ih => exact ih _ (Parents.coherent_append_label coherent a)

theorem parentTable_coherent (d : Nat) (m : Matrix) : Parents.Coherent d (parentTable d m) :=
  parentTableAux_coherent d [] m (Parents.empty_coherent d)

/-- Every actual computed high-row ancestry is an ancestry in every lower row. -/
theorem parentTable_ancestor_lower (d : Nat) (m : Matrix) (lower upper a b : Nat)
    (room : upper < d) (rows : lower ≤ upper)
    (path : Parents.Ancestor (parentTable d m) upper a b) :
    Parents.Ancestor (parentTable d m) lower a b :=
  path.lower_row (parentTable_coherent d m) room rows

end BTnSSBMS.BMS
