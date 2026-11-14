import BTnSSBMS.KeyEntries

/-! Upper-row control across the real D,H,forest-slot,closing-P scope. -/
namespace BTnSSBMS.Encoder

structure KeyGate (d : Nat) (source : ParentContext) (coordinates : List Nat)
    (visible : List Nat) (original state : State d) (u : Nat → Nat) (c : Nat)
    (below : List Binding) : Prop where
  numerical : NumericalGate d source coordinates visible original state u (original.length + 1)
  headed : emit (emit original u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 [] <+: state
  retained : FrameAncestral state original.length below

theorem KeyGate.definition_readout {d : Nat} {source : ParentContext} {coordinates : List Nat}
    {visible : List Nat} {original state : State d} {u : Nat → Nat} {c : Nat} {below : List Binding}
    (scope : KeyGate d source coordinates visible original state u c below) :
    Readout state original.length (c + 1) 1 :=
  readout_extends ((emit_extends ..).trans scope.headed) (readout_emit original u (c + 1) 1 [])

theorem KeyGate.guard_path {d : Nat} {source : ParentContext} {coordinates : List Nat}
    {visible : List Nat} {original state : State d} {u : Nat → Nat} {c : Nat} {below : List Binding}
    (scope : KeyGate d source coordinates visible original state u c below) (positive : 0 < d) :
    Parents.Ancestor (BMS.parentTable (d + 2) (matrix state)) d original.length (original.length + 1) :=
  (Parents.Ancestor.up (guard_key_parent original u c positive) (.refl _)).prefix (table_prefix scope.headed)

theorem KeyGate.slot_key_parent {d : Nat} {source : ParentContext} {coordinates : List Nat}
    {visible : List Nat} {original state : State d} {u : Nat → Nat} {c : Nat} {below : List Binding}
    (scope : KeyGate d source coordinates visible original state u c below) (positive : 0 < d) :
    Parents.parent (BMS.parentTable (d + 2) (matrix
      (emit state (fun j => u j + 2) (c + 2) 0 below))) d state.length = some original.length :=
  emitted_key_parent state _ (c + 2) 0 below positive (original.length + 1) original.length
    (scope.numerical.slot_parents (c + 2) below (d - 1) (by omega)) (scope.guard_path positive)
    (by rw [scope.definition_readout.key_reading])

theorem KeyGate.slot_ancestral {d : Nat} {source : ParentContext} {coordinates : List Nat}
    {visible : List Nat} {original state : State d} {u : Nat → Nat} {c : Nat} {below : List Binding}
    (scope : KeyGate d source coordinates visible original state u c below) (positive : 0 < d) :
    FrameAncestral (emit state (fun j => u j + 2) (c + 2) 0 below) state.length below :=
  (scope.retained.extends (emit_extends ..)).trans (.up (scope.slot_key_parent positive) (.refl _))

theorem KeyGate.after_forest {d : Nat} {source : ParentContext} {coordinates : List Nat}
    {visible finalVisible : List Nat} {original state next : State d} {u : Nat → Nat} {c : Nat} {below : List Binding}
    (scope : KeyGate d source coordinates visible original state u c below)
    (positive : 0 < d) (sourceCoherent : Parents.Coherent d source)
    (sourceValid : Parents.ContextValid source) (visibleLength : visible.length = source.length)
    (m : Matrix) (nextExtends : emit state (fun k => u k + 2) (c + 2) 0 below <+: next)
    (visibleExtends : visible ++ [state.length] <+: finalVisible)
    (above : ∀ col ∈ m, coordinates[0]?.getD 0 < col[0]?.getD 0)
    (view : Parents.NumericalView d
      (BMS.parentTableAux d (source ++ [Parents.label d source coordinates]) m)
      (BMS.parentTable (d + 2) (matrix next)) finalVisible) :
    KeyGate d source coordinates visible original next u c below :=
  ⟨scope.numerical.after_forest positive sourceCoherent sourceValid visibleLength
      (c + 2) below m nextExtends visibleExtends above view,
    scope.headed.trans ((emit_extends ..).trans nextExtends),
    scope.retained.extends ((emit_extends ..).trans nextExtends)⟩

theorem KeyGate.closing_numerical_parent {d : Nat} {source : ParentContext} {coordinates : List Nat}
    {visible : List Nat} {original state : State d} {u : Nat → Nat} {c : Nat} {below : List Binding}
    (scope : KeyGate d source coordinates visible original state u c below) (positive : 0 < d)
    (frame : List Binding) (j : Nat) (room : j < d) :
    Parents.parent (BMS.parentTable (d + 2) (matrix
      (emit state (fun j => u j + 1) (c + 2) 0 frame))) j state.length = some original.length := by
  have firstToGuard : Parents.Ancestor (BMS.parentTable (d + 2) (matrix state)) 0
      original.length (original.length + 1) :=
    (Parents.Ancestor.up (guard_numerical_parents original u c 0 positive) (.refl _)).prefix
      (table_prefix scope.headed)
  have dExtends := (emit_extends ..).trans scope.headed
  apply auxiliary_numerical_parents state _ (c + 2) 0 frame original.length scope.numerical.nonempty
    (firstToGuard.trans scope.numerical.fence) (fun k inside => ?_) j room
  rw [← Parents.reading_prefix (table_prefix dExtends) k original.length
    (by rw [table_length, emit_length]; omega), emitted_numerical_value original u (c + 1) 1 [] k inside]

theorem KeyGate.closing_key_parent {d : Nat} {source : ParentContext} {coordinates : List Nat}
    {visible : List Nat} {original state : State d} {u : Nat → Nat} {c : Nat} {below : List Binding}
    (scope : KeyGate d source coordinates visible original state u c below) (positive : 0 < d)
    (frame : List Binding) :
    Parents.parent (BMS.parentTable (d + 2) (matrix
      (emit state (fun j => u j + 1) (c + 2) 0 frame))) d state.length = some original.length :=
  emitted_key_parent state _ (c + 2) 0 frame positive original.length original.length
    (scope.closing_numerical_parent positive frame (d - 1) (by omega)) (.refl _)
    (by rw [scope.definition_readout.key_reading])

theorem KeyGate.closing_ancestral {d : Nat} {source : ParentContext} {coordinates : List Nat}
    {visible : List Nat} {original state : State d} {u : Nat → Nat} {c : Nat} {below : List Binding}
    (scope : KeyGate d source coordinates visible original state u c below) (positive : 0 < d) (key : Key) :
    let frame := below ++ [⟨key, c + 2, some state.length, some original.length⟩]
    FrameAncestral (emit state (fun j => u j + 1) (c + 2) 0 frame) state.length frame := by
  dsimp only
  have parent := scope.closing_key_parent positive
    (below ++ [⟨key, c + 2, some state.length, some original.length⟩])
  apply frame_ancestral_append
    ((scope.retained.extends (emit_extends ..)).trans (.up parent (.refl _))) _ rfl
  intro root found
  have same : root = original.length := by simpa only [Option.some.injEq] using found.symm
  subst root
  exact .up parent (.refl _)

end BTnSSBMS.Encoder
