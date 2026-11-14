import BTnSSBMS.RootedHeadComparison
import BTnSSBMS.ShiftComparison

/-!
When a fresh query has matched the copied first column, every delimiter
it emits matches too. The argument uses the old computed parents even
after arbitrary forest output; it does not assume equal forest lengths.
-/
namespace BTnSSBMS.Encoder

structure FreshShift (state : State d) (u v : Nat → Nat) (c newC root : Nat) (delta : Nat → Nat) : Prop where
  numerical : ∀ j, j < d → v j = u j +
    rowBump (emit state u (c + 1) 1 []) j root (delta j) state.length
  key : newC = c + rowBump (emit state u (c + 1) 1 []) d root (delta d) state.length

theorem FreshShift.of_first_column {d : Nat} {state : State d} {u v : Nat → Nat} {c newC root : Nat}
    {delta : Nat → Nat}
    (same : row d v (newC + 1) 1 = shiftedColumn (emit state u (c + 1) 1 []) root delta state.length) :
    FreshShift state u v c newC root delta := by
  rw [shiftedColumn_emit] at same
  constructor
  · intro j room
    have value := congrArg (fun col : List Nat => col[j]?.getD 0) same
    simpa only [row_numerical_reading d _ _ _ j room] using value
  · have value := congrArg (fun col : List Nat => col[d]?.getD 0) same
    simp only [row_key_reading] at value
    omega

private theorem rows_equal (d : Nat) (u v : Nat → Nat) (a b tag : Nat)
    (numbers : ∀ j, j < d → u j = v j) (key : a = b) : row d u a tag = row d v b tag := by
  rw [key]
  unfold row
  congr 1
  apply List.map_congr_left
  intro j member
  exact numbers j (List.mem_range.mp member)

theorem FreshShift.guard {d : Nat} {state : State d} {u v : Nat → Nat} {c newC root : Nat} {delta : Nat → Nat}
    (shift : FreshShift state u v c newC root delta) (positive : 0 < d) (rootBefore : root ≤ state.length) :
    row d (fun j => v j + 1) (newC + 2) 2 =
      shiftedColumn (emit (emit state u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 [])
        root delta (state.length + 1) := by
  rw [← emit_length state u (c + 1) 1 [], shiftedColumn_emit]
  apply rows_equal
  · intro j room
    rw [emit_length, rowBump_guard state u c j root (delta j) room rootBefore, shift.numerical j room]
    omega
  · rw [emit_length, rowBump_key_guard state u c root (delta d) positive rootBefore, shift.key]
    omega

theorem FreshShift.slot {d : Nat} {source : ParentContext} {coordinates visible : List Nat}
    {original state : State d} {u v : Nat → Nat} {c newC root : Nat} {delta : Nat → Nat} {below : List Binding}
    (shift : FreshShift original u v c newC root delta)
    (scope : KeyGate d source coordinates visible original state u c below)
    (positive : 0 < d) (rootBefore : root ≤ original.length) :
    row d (fun j => v j + 2) (newC + 2) 0 =
      shiftedColumn (emit state (fun j => u j + 2) (c + 2) 0 below) root delta state.length := by
  rw [shiftedColumn_emit]
  apply rows_equal
  · intro j room
    rw [scope.rowBump_numerical_slot j root (delta j) room rootBefore, shift.numerical j room]
    omega
  · rw [scope.rowBump_key_slot positive root (delta d) rootBefore, shift.key]
    omega

theorem FreshShift.closing {d : Nat} {source : ParentContext} {coordinates visible : List Nat}
    {original state : State d} {u v : Nat → Nat} {c newC root : Nat} {delta : Nat → Nat} {below : List Binding}
    (shift : FreshShift original u v c newC root delta)
    (scope : KeyGate d source coordinates visible original state u c below)
    (positive : 0 < d) (rootBefore : root ≤ original.length) (frame : List Binding) :
    row d (fun j => v j + 1) (newC + 2) 0 =
      shiftedColumn (emit state (fun j => u j + 1) (c + 2) 0 frame) root delta state.length := by
  rw [shiftedColumn_emit]
  apply rows_equal
  · intro j room
    rw [scope.rowBump_numerical_closing positive j root (delta j) room rootBefore frame, shift.numerical j room]
    omega
  · rw [scope.rowBump_key_closing positive root (delta d) rootBefore frame, shift.key]
    omega

end BTnSSBMS.Encoder
