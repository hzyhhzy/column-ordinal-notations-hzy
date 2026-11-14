import BTnSSBMS.ViewExtension

/-!
Actual numerical parents of auxiliary columns. A row-zero fence suffices:
once the first parent is fixed, adding one in each numerical coordinate
selects that same parent in every remaining numerical row. The statement
does not presuppose any key-row or tag-row parent table.
-/
namespace BTnSSBMS.Parents

theorem constant_numerical_parents {d rows : Nat} {context : ParentContext}
    (coherent : Coherent rows context) (valid : ContextValid context) (room : d ≤ rows)
    (parentPosition frontier : Nat) (frontierBound : frontier < context.length)
    (atEnd : frontier + 1 = context.length)
    (fence : Ancestor context 0 parentPosition frontier)
    (coordinates : List Nat)
    (values : ∀ j, j < d → coordinates[j]?.getD 0 = reading context j parentPosition + 1)
    (j : Nat) (inside : j < d) :
    (label rows context coordinates).parents[j]?.join = some parentPosition := by
  have before := fence.le valid
  have parentBound : parentPosition < context.length := by omega
  induction j with
  | zero =>
    rw [label_zero rows context coordinates (by omega), values 0 inside]
    have hit := search_ancestor_successor coherent valid (by omega : 0 < rows) frontierBound fence
    simpa only [atEnd] using hit
  | succ j ih =>
    rw [label_next rows context coordinates j (by omega), ih (by omega), values (j + 1) inside]
    simp only [Option.map_some, Option.getD_some]
    rw [search, List.getElem?_eq_getElem parentBound]
    have small : context[parentPosition].coordinates[j + 1]?.getD 0 <
        reading context (j + 1) parentPosition + 1 := by
      simp only [reading, List.getElem?_eq_getElem parentBound, Option.getD_some]
      omega
    simp only [small, if_true]

end BTnSSBMS.Parents

namespace BTnSSBMS.Encoder

theorem table_length (state : State d) :
    (BMS.parentTable (d + 2) (matrix state)).length = state.length := by
  simp only [BMS.parentTable_length, matrix, List.length_map]

theorem emitted_parent (state : State d) (u : Nat → Nat) (height tag : Nat) (frame : List Binding) (j : Nat) :
    Parents.parent (BMS.parentTable (d + 2) (matrix (emit state u height tag frame))) j state.length =
      (Parents.label (d + 2) (BMS.parentTable (d + 2) (matrix state)) (row d u height tag)).parents[j]?.join := by
  rw [matrix_emit, BMS.parentTable_snoc, ← table_length state]
  exact Parents.append_label_parent (d + 2) (BMS.parentTable (d + 2) (matrix state)) _ j

theorem emitted_numerical_value (state : State d) (u : Nat → Nat) (height tag : Nat)
    (frame : List Binding) (j : Nat) (inside : j < d) :
    Parents.reading (BMS.parentTable (d + 2) (matrix (emit state u height tag frame))) j state.length = u j := by
  rw [BMS.parentTable_reading, matrix_lookup]
  simp only [emit, List.getElem?_concat_length, Option.map_some, Option.getD_some]
  exact row_numerical_reading d u height tag j inside

theorem table_emit_prefix (state : State d) (u : Nat → Nat) (height tag : Nat) (frame : List Binding) :
    BMS.parentTable (d + 2) (matrix state) <+:
      BMS.parentTable (d + 2) (matrix (emit state u height tag frame)) := by
  rw [matrix_emit, BMS.parentTable_snoc]
  exact List.prefix_append _ _

theorem table_prefix {state next : State d} (initial : state <+: next) :
    BMS.parentTable (d + 2) (matrix state) <+: BMS.parentTable (d + 2) (matrix next) := by
  obtain ⟨tail, rfl⟩ := initial
  simp only [matrix, List.map_append, BMS.parentTable_append]
  obtain ⟨added, shape⟩ := BMS.parentTableAux_extends (d + 2)
    (BMS.parentTable (d + 2) (matrix state)) (matrix tail)
  exact ⟨added, shape.symm⟩

theorem emitted_source_parent_path {d : Nat} {source : ParentContext} {visible : List Nat}
    (state : State d) (sourceCoherent : Parents.Coherent d source)
    (sourceValid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (coordinates : List Nat) (height tag : Nat) (frame : List Binding)
    (j p : Nat) (room : j < d) (selected : (Parents.label d source coordinates).parents[j]?.join = some p) :
    Parents.Ancestor (BMS.parentTable (d + 2) (matrix
      (emit state (vector state visible (Parents.label d source coordinates)) height tag frame))) j
      (Parents.point visible p) state.length := by
  apply Parents.Ancestor.up ?_ (.refl _)
  rw [emitted_parent, emitted_head_numerical_parents state sourceCoherent sourceValid view coordinates height tag j room,
    representative_eq_point view, selected]
  rfl

/-- An auxiliary column +1 above a fenced parent has that exact parent in
every numerical row. Fences refer to actual computed row-zero ancestry. -/
theorem auxiliary_numerical_parents (state : State d) (u : Nat → Nat) (height tag : Nat)
    (frame : List Binding) (parentPosition : Nat) (nonempty : 0 < state.length)
    (fence : Parents.Ancestor (BMS.parentTable (d + 2) (matrix state)) 0 parentPosition (state.length - 1))
    (values : ∀ j, j < d → u j =
      Parents.reading (BMS.parentTable (d + 2) (matrix state)) j parentPosition + 1)
    (j : Nat) (inside : j < d) :
    Parents.parent (BMS.parentTable (d + 2) (matrix (emit state u height tag frame))) j state.length =
      some parentPosition := by
  rw [emitted_parent]
  apply Parents.constant_numerical_parents (BMS.parentTable_coherent _ _)
    (BMS.parentTable_valid _ _) (by omega) parentPosition (state.length - 1)
    (by rw [table_length]; omega) (by rw [table_length]; omega) fence _ _ j inside
  intro k room
  rw [row_numerical_reading d u height tag k room, values k room]

/-- In the real D,H emission pair, every numerical parent of H is D.
This holds for every incoming state and does not need a source invariant. -/
theorem guard_numerical_parents (state : State d) (u : Nat → Nat) (c : Nat) (j : Nat) (inside : j < d) :
    Parents.parent (BMS.parentTable (d + 2) (matrix
      (emit (emit state u (c + 1) 1 []) (fun k => u k + 1) (c + 2) 2 []))) j (state.length + 1) =
      some state.length := by
  have fence : Parents.Ancestor (BMS.parentTable (d + 2) (matrix (emit state u (c + 1) 1 [])))
      0 state.length ((emit state u (c + 1) 1 []).length - 1) := by
    rw [emit_length, Nat.add_sub_cancel]
    exact .refl _
  have result := auxiliary_numerical_parents (emit state u (c + 1) 1 [])
    (fun k => u k + 1) (c + 2) 2 [] state.length (by rw [emit_length]; omega) fence
    (by intro k room; rw [emitted_numerical_value state u (c + 1) 1 [] k room]) j inside
  simpa only [emit_length] using result

end BTnSSBMS.Encoder
