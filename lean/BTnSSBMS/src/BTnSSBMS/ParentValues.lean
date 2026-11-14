import BTnSSBMS.Activation

/-!
Every computed parent has strictly smaller value in its own row. Together
with lower-row inclusion, this proves that the differences used by a BMS
copy are nonnegative; Nat subtraction is not silently changing the rule.
-/
namespace BTnSSBMS.Parents

def reading (context : ParentContext) (row position : Nat) : Nat :=
  (context[position]?.getD default).coordinates[row]?.getD 0

theorem rows_found (context : ParentContext) (coordinates : List Nat)
    (row remaining cursor offset found : Nat)
    (hit : (rows context coordinates row remaining cursor)[offset]?.join = some found) :
    ∃ start, search context (row + offset) (coordinates[row + offset]?.getD 0) start = some found := by
  induction remaining generalizing row cursor offset with
  | zero => simp [rows] at hit
  | succ remaining ih =>
    cases offset with
    | zero => exact ⟨cursor, by simpa only [rows, List.getElem?_cons_zero, Option.join_some, Nat.add_zero] using hit⟩
    | succ offset =>
      obtain ⟨start, next⟩ := ih (row + 1)
        ((search context row (coordinates[row]?.getD 0) cursor).map (· + 1) |>.getD 0)
        offset (by simpa only [rows, List.getElem?_cons_succ] using hit)
      exact ⟨start, by simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using next⟩

theorem parent_reading_lt {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) {row p q : Nat}
    (edge : parent context row q = some p) : reading context row p < reading context row q := by
  obtain ⟨a, lookup, hit⟩ := Option.bind_eq_some_iff.mp edge
  have computed := coherent q a lookup
  rw [computed] at hit
  obtain ⟨start, result⟩ := rows_found (context.take q) a.coordinates 0 d (context.take q).length row p hit
  have result' : search (context.take q) row (a.coordinates[row]?.getD 0) start = some p := by
    simpa only [Nat.zero_add] using result
  obtain ⟨b, atParent, smaller⟩ := search_smaller (context.take q) row _ start p result'
  have before : p < q := by
    have bound := (List.getElem?_eq_some_iff.mp atParent).choose
    simp only [List.length_take] at bound
    omega
  rw [List.getElem?_take_of_lt before] at atParent
  simpa only [reading, lookup, atParent, Option.getD_some] using smaller

theorem Ancestor.reading_le {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) {row a b : Nat}
    (path : Ancestor context row a b) : reading context row a ≤ reading context row b := by
  induction path with
  | refl => exact Nat.le_refl _
  | up edge _ ih => have strict := parent_reading_lt coherent edge; omega

theorem Ancestor.reading_lt {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) {row a b : Nat}
    (path : Ancestor context row a b) (different : a ≠ b) :
    reading context row a < reading context row b := by
  obtain ⟨p, edge, previous⟩ := (Ancestor.iff_parent different).mp path
  have lower := previous.reading_le coherent
  have last := parent_reading_lt coherent edge
  omega

end BTnSSBMS.Parents

namespace BTnSSBMS.BMS

theorem parentTableAux_coordinates (d : Nat) (context : ParentContext) (m : Matrix) :
    (parentTableAux d context m).map ParentLabel.coordinates = context.map ParentLabel.coordinates ++ m := by
  induction m generalizing context with
  | nil => simp [parentTableAux]
  | cons a m ih => simp only [parentTableAux, ih, List.map_append,
      List.map_cons, List.map_nil, Parents.label, List.append_assoc, List.cons_append, List.nil_append]

theorem parentTable_coordinates (d : Nat) (m : Matrix) :
    (parentTable d m).map ParentLabel.coordinates = m := by
  simpa only [parentTable, List.map_nil, List.nil_append] using parentTableAux_coordinates d [] m

theorem parentTable_reading (d : Nat) (m : Matrix) (row position : Nat) :
    Parents.reading (parentTable d m) row position = (m[position]?.getD [])[row]?.getD 0 := by
  have same := congrArg (fun xs : Matrix => xs[position]?) (parentTable_coordinates d m)
  rw [List.getElem?_map] at same
  cases lookup : (parentTable d m)[position]? with
  | none =>
    have absent : m[position]? = none := by simpa only [lookup, Option.map_none] using same.symm
    simp only [Parents.reading, lookup, absent, Option.getD_none]
    rfl
  | some a =>
    have output : m[position]? = some a.coordinates := by
      simpa only [lookup, Option.map_some] using same.symm
    simp only [Parents.reading, lookup, output, Option.getD_some]

theorem root_reading_lt (d : Nat) (m : Matrix) (root endpoint top row : Nat)
    (room : top < d) (below : row ≤ top)
    (edge : Parents.parent (parentTable d m) top endpoint = some root) :
    (m[root]?.getD [])[row]?.getD 0 < (m[endpoint]?.getD [])[row]?.getD 0 := by
  have strict := Parents.parent_earlier (parentTable_valid d m) edge
  have high : Parents.Ancestor (parentTable d m) top root endpoint := .up edge (.refl _)
  have low := high.lower_row (parentTable_coherent d m) room below
  simpa only [parentTable_reading] using low.reading_lt (parentTable_coherent d m) (by omega)

/-- Every lower-row difference really reconstructs the terminal value.
No numerical-legality or source-standardness assumption is being hidden. -/
theorem root_difference_reconstruct (d : Nat) (m : Matrix) (root endpoint top row : Nat)
    (room : top < d) (below : row ≤ top)
    (edge : Parents.parent (parentTable d m) top endpoint = some root) :
    (m[root]?.getD [])[row]?.getD 0 +
      ((m[endpoint]?.getD [])[row]?.getD 0 - (m[root]?.getD [])[row]?.getD 0) =
      (m[endpoint]?.getD [])[row]?.getD 0 := by
  have smaller := root_reading_lt d m root endpoint top row room below edge
  omega

end BTnSSBMS.BMS
