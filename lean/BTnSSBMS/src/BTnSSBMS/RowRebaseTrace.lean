import BTnSSBMS.EntryRebaseNumerics

/-!
One numerical row of an actual output, with an ancestry-sensitive shift.
This is a proof-side finite relation, not a replacement encoder or FS.
The ancestry test can equivalently be evaluated by the BMS thresholds.
-/
namespace BTnSSBMS.Encoder

noncomputable def rowBump (state : State d) (j root amount p : Nat) : Nat := by
  classical
  exact if Parents.Ancestor (BMS.parentTable (d + 2) (matrix state)) j root p then amount else 0

theorem rowBump_prefix {state next : State d} (extended : state <+: next)
    (j root amount p : Nat) (inside : p < state.length) :
    rowBump next j root amount p = rowBump state j root amount p := by
  classical
  have same : Parents.Ancestor (BMS.parentTable (d + 2) (matrix next)) j root p ↔
      Parents.Ancestor (BMS.parentTable (d + 2) (matrix state)) j root p :=
    ⟨fun h => h.restrict (table_prefix extended) (BMS.parentTable_valid _ _) (by rw [table_length]; exact inside),
      fun h => h.prefix (table_prefix extended)⟩
  simp only [rowBump, same]

theorem rowBump_parent {state : State d} {j root amount p q : Nat}
    (different : root ≠ p)
    (edge : Parents.parent (BMS.parentTable (d + 2) (matrix state)) j p = some q) :
    rowBump state j root amount p = rowBump state j root amount q := by
  classical
  have same : Parents.Ancestor (BMS.parentTable (d + 2) (matrix state)) j root p ↔
      Parents.Ancestor (BMS.parentTable (d + 2) (matrix state)) j root q := by
    rw [Parents.Ancestor.iff_parent different, edge]
    simp only [Option.some.injEq, exists_eq_left']
  simp only [rowBump, same]

theorem rowBump_missing {state : State d} {j root amount p : Nat}
    (different : root ≠ p)
    (edge : Parents.parent (BMS.parentTable (d + 2) (matrix state)) j p = none) :
    rowBump state j root amount p = 0 := by
  classical
  have absent : ¬ Parents.Ancestor (BMS.parentTable (d + 2) (matrix state)) j root p := by
    rw [Parents.Ancestor.iff_parent different, edge]
    simp
  simp only [rowBump, absent, if_false]

theorem rowBump_threshold (state : State d) (j root amount p : Nat)
    (room : j < d) (inside : p < state.length) :
    rowBump state j root amount p =
      if j < (BMS.thresholds (BMS.parentTable (d + 2) (matrix state)) root (j + 1))[p]?.getD 0
      then amount else 0 := by
  classical
  have same := BMS.thresholds_ancestry (d + 2) (matrix state) root (j + 1) (by omega)
    p (by simpa only [matrix, List.length_map] using inside) j
  simp only [Nat.lt_succ_self, true_and] at same
  simp only [rowBump, same]

structure RowRebaseTrace (j root amount : Nat) (state next result newResult : State d) : Prop where
  oldPrefix : state <+: result
  newPrefix : next <+: newResult
  length : result.length + next.length = newResult.length + state.length
  values : ∀ k, k < result.length - state.length →
    Parents.reading (BMS.parentTable (d + 2) (matrix newResult)) j (next.length + k) =
      Parents.reading (BMS.parentTable (d + 2) (matrix result)) j (state.length + k) +
        rowBump result j root amount (state.length + k)

theorem RowRebaseTrace.refl (j root amount : Nat) (state next : State d) :
    RowRebaseTrace j root amount state next state next :=
  ⟨List.prefix_refl _, List.prefix_refl _, Nat.add_comm _ _, by intro k impossible; omega⟩

theorem RowRebaseTrace.trans {j root amount : Nat} {state next middle newMiddle result newResult : State d}
    (first : RowRebaseTrace j root amount state next middle newMiddle)
    (second : RowRebaseTrace j root amount middle newMiddle result newResult) :
    RowRebaseTrace j root amount state next result newResult := by
  have oldLength := first.oldPrefix.length_le
  have newLength := first.newPrefix.length_le
  have finalLength := second.oldPrefix.length_le
  refine ⟨first.oldPrefix.trans second.oldPrefix, first.newPrefix.trans second.newPrefix,
    by have := first.length; have := second.length; omega, ?_⟩
  intro k inside
  by_cases before : k < middle.length - state.length
  · have oldBound : state.length + k < middle.length := by omega
    have newBound : next.length + k < newMiddle.length := by have := first.length; omega
    rw [← Parents.reading_prefix (table_prefix second.newPrefix) j (next.length + k)
        (by rw [table_length]; exact newBound),
      ← Parents.reading_prefix (table_prefix second.oldPrefix) j (state.length + k)
        (by rw [table_length]; exact oldBound),
      rowBump_prefix second.oldPrefix j root amount (state.length + k) oldBound]
    exact first.values k before
  · have offsetBound : k - (middle.length - state.length) < result.length - middle.length := by omega
    have oldPosition : middle.length + (k - (middle.length - state.length)) = state.length + k := by omega
    have newPosition : newMiddle.length + (k - (middle.length - state.length)) = next.length + k := by
      have := first.length; omega
    simpa only [oldPosition, newPosition] using second.values _ offsetBound

theorem RowRebaseTrace.emit (state next : State d) (u v : Nat → Nat)
    (height tag newHeight newTag : Nat) (frame newFrame : List Binding)
    (j root amount : Nat) (room : j < d)
    (value : v j = u j + rowBump (Encoder.emit state u height tag frame) j root amount state.length) :
    RowRebaseTrace j root amount state next
      (Encoder.emit state u height tag frame) (Encoder.emit next v newHeight newTag newFrame) := by
  refine ⟨emit_extends .., emit_extends .., by simp only [emit_length]; omega, ?_⟩
  intro k inside
  have zero : k = 0 := by rw [emit_length] at inside; omega
  subst k
  simp only [Nat.add_zero]
  rw [emitted_numerical_value next v newHeight newTag newFrame j room,
    emitted_numerical_value state u height tag frame j room]
  exact value

theorem RowRebaseTrace.last {j root amount : Nat} {state next result newResult : State d}
    (trace : RowRebaseTrace j root amount state next result newResult)
    (nonempty : state.length < result.length) :
    Parents.reading (BMS.parentTable (d + 2) (matrix newResult)) j (newResult.length - 1) =
      Parents.reading (BMS.parentTable (d + 2) (matrix result)) j (result.length - 1) +
        rowBump result j root amount (result.length - 1) := by
  have gap := trace.length
  have oldPosition : state.length + (result.length - state.length - 1) = result.length - 1 := by omega
  have newPosition : next.length + (result.length - state.length - 1) = newResult.length - 1 := by omega
  simpa only [oldPosition, newPosition] using trace.values (result.length - state.length - 1) (by omega)

end BTnSSBMS.Encoder
