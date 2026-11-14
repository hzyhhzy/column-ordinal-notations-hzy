import BTnSSBMS.CoupledSaving

/-! The key and tag rows of actual output columns, not an abstract
execution or a mapped substitute for the real encoder state. -/
namespace BTnSSBMS.Encoder

def controlTrace (state : State d) : List (List Nat) :=
  state.map fun col => col.values.drop d

def SharedTrace (state next result newResult : State d) : Prop :=
  ∃ suffix, controlTrace result = controlTrace state ++ suffix ∧
    controlTrace newResult = controlTrace next ++ suffix

theorem SharedTrace.refl (state next : State d) : SharedTrace state next state next :=
  ⟨[], by simp, by simp⟩

theorem SharedTrace.trans {state next middle newMiddle result newResult : State d}
    (first : SharedTrace state next middle newMiddle)
    (second : SharedTrace middle newMiddle result newResult) : SharedTrace state next result newResult := by
  obtain ⟨a, oldA, newA⟩ := first
  obtain ⟨b, oldB, newB⟩ := second
  exact ⟨a ++ b, by rw [oldB, oldA, List.append_assoc], by rw [newB, newA, List.append_assoc]⟩

theorem controlTrace_emit (state : State d) (u : Nat → Nat) (height tag : Nat) (frame : List Binding) :
    controlTrace (emit state u height tag frame) = controlTrace state ++ [[height, tag]] := by
  simp [controlTrace, emit, row]

theorem SharedTrace.emit (state next : State d) (u v : Nat → Nat) (height tag : Nat)
    (frame newFrame : List Binding) :
    SharedTrace state next (Encoder.emit state u height tag frame) (Encoder.emit next v height tag newFrame) :=
  ⟨[[height, tag]], controlTrace_emit .., controlTrace_emit ..⟩

theorem SharedTrace.length {state next result newResult : State d}
    (same : SharedTrace state next result newResult) : result.length + next.length = newResult.length + state.length := by
  obtain ⟨suffix, old, new⟩ := same
  have a := congrArg List.length old
  have b := congrArg List.length new
  simp only [controlTrace, List.length_map, List.length_append] at a b
  omega

theorem SharedTrace.suffix {state next result newResult : State d}
    (same : SharedTrace state next result newResult) :
    (controlTrace result).drop state.length = (controlTrace newResult).drop next.length := by
  obtain ⟨suffix, old, new⟩ := same
  rw [old, new]
  have oldSize : (controlTrace state).length = state.length := List.length_map _
  have newSize : (controlTrace next).length = next.length := List.length_map _
  rw [← oldSize, List.drop_left, ← newSize, List.drop_left]

end BTnSSBMS.Encoder
