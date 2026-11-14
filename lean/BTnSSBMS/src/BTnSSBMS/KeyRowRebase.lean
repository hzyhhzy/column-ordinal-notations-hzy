import BTnSSBMS.RowRebaseValues
import BTnSSBMS.KeyForestScope

/-!
The key-row increment at fresh auxiliary columns is determined by the
same old definition column. These are equalities about computed BMS
parents, including after arbitrarily much intervening forest output.
-/
namespace BTnSSBMS.Encoder

theorem rowBump_key_guard (state : State d) (u : Nat → Nat) (c root amount : Nat)
    (positive : 0 < d) (rootBefore : root ≤ state.length) :
    rowBump (emit (emit state u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 [])
      d root amount (state.length + 1) =
    rowBump (emit state u (c + 1) 1 []) d root amount state.length := by
  rw [rowBump_parent (by omega) (guard_key_parent state u c positive)]
  exact rowBump_prefix (emit_extends ..) d root amount state.length (by rw [emit_length]; omega)

theorem KeyGate.rowBump_definition {d : Nat} {source : ParentContext} {coordinates visible : List Nat}
    {original state : State d} {u : Nat → Nat} {c : Nat} {below : List Binding}
    (scope : KeyGate d source coordinates visible original state u c below) (j root amount : Nat) :
    rowBump state j root amount original.length =
      rowBump (emit original u (c + 1) 1 []) j root amount original.length :=
  rowBump_prefix ((emit_extends ..).trans scope.headed) j root amount original.length
    (by rw [emit_length]; omega)

theorem KeyGate.rowBump_key_slot {d : Nat} {source : ParentContext} {coordinates visible : List Nat}
    {original state : State d} {u : Nat → Nat} {c : Nat} {below : List Binding}
    (scope : KeyGate d source coordinates visible original state u c below)
    (positive : 0 < d) (root amount : Nat) (rootBefore : root ≤ original.length) :
    rowBump (emit state (fun j => u j + 2) (c + 2) 0 below) d root amount state.length =
      rowBump (emit original u (c + 1) 1 []) d root amount original.length := by
  have length := scope.headed.length_le
  simp only [emit_length] at length
  rw [rowBump_parent (by omega) (scope.slot_key_parent positive),
    rowBump_prefix (emit_extends ..) d root amount original.length (by omega)]
  exact scope.rowBump_definition d root amount

theorem KeyGate.rowBump_key_closing {d : Nat} {source : ParentContext} {coordinates visible : List Nat}
    {original state : State d} {u : Nat → Nat} {c : Nat} {below : List Binding}
    (scope : KeyGate d source coordinates visible original state u c below)
    (positive : 0 < d) (root amount : Nat) (rootBefore : root ≤ original.length)
    (frame : List Binding) :
    rowBump (emit state (fun j => u j + 1) (c + 2) 0 frame) d root amount state.length =
      rowBump (emit original u (c + 1) 1 []) d root amount original.length := by
  have length := scope.headed.length_le
  simp only [emit_length] at length
  rw [rowBump_parent (by omega) (scope.closing_key_parent positive frame),
    rowBump_prefix (emit_extends ..) d root amount original.length (by omega)]
  exact scope.rowBump_definition d root amount

theorem KeyGate.rowBump_numerical_slot {d : Nat} {source : ParentContext} {coordinates visible : List Nat}
    {original state : State d} {u : Nat → Nat} {c : Nat} {below : List Binding}
    (scope : KeyGate d source coordinates visible original state u c below)
    (j root amount : Nat) (room : j < d) (rootBefore : root ≤ original.length) :
    rowBump (emit state (fun k => u k + 2) (c + 2) 0 below) j root amount state.length =
      rowBump (emit original u (c + 1) 1 []) j root amount original.length := by
  have length := scope.headed.length_le
  simp only [emit_length] at length
  rw [scope.numerical.rowBump_slot (c + 2) below j root amount room (by omega),
    rowBump_prefix scope.headed j root amount (original.length + 1) (by simp only [emit_length]; omega)]
  exact rowBump_guard original u c j root amount room rootBefore

theorem KeyGate.rowBump_numerical_closing {d : Nat} {source : ParentContext} {coordinates visible : List Nat}
    {original state : State d} {u : Nat → Nat} {c : Nat} {below : List Binding}
    (scope : KeyGate d source coordinates visible original state u c below)
    (positive : 0 < d) (j root amount : Nat) (room : j < d) (rootBefore : root ≤ original.length)
    (frame : List Binding) :
    rowBump (emit state (fun k => u k + 1) (c + 2) 0 frame) j root amount state.length =
      rowBump (emit original u (c + 1) 1 []) j root amount original.length := by
  have length := scope.headed.length_le
  simp only [emit_length] at length
  rw [rowBump_parent (by omega) (scope.closing_numerical_parent positive frame j room),
    rowBump_prefix (emit_extends ..) j root amount original.length (by omega)]
  exact scope.rowBump_definition j root amount

end BTnSSBMS.Encoder
