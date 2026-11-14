import BTnSSBMS.KeyParentTypes

/-!
Numerical parent types separate source-entry columns from auxiliary columns.
Source entries have only tag-zero numerical parents; an auxiliary column
has one common parent in all numerical rows, of tag one or two. This local
classification excludes auxiliary endpoints from intermediate SB pairs.
-/
namespace BTnSSBMS.Encoder

def VisibleZero (state : State d) (visible : List Nat) : Prop :=
  ∀ p ∈ visible, ∃ h, Readout state p h 0

def NumericalHead (state : State d) (position : Nat) : Prop :=
  ∀ j, j < d → ∀ root,
    Parents.parent (BMS.parentTable (d + 2) (matrix state)) j position = some root →
    ∃ h, Readout state root h 0

def NumericalAuxiliary (state : State d) (position : Nat) : Prop :=
  ∃ root height tag, (tag = 1 ∨ tag = 2) ∧ Readout state root height tag ∧
    ∀ j, j < d → Parents.parent (BMS.parentTable (d + 2) (matrix state)) j position = some root

def NumericalClasses (state : State d) (heads : List Nat) : Prop :=
  ∀ position, position < state.length →
    (position ∈ heads ∧ NumericalHead state position) ∨ NumericalAuxiliary state position

theorem VisibleZero.extends {state next : State d} {visible : List Nat}
    (zero : VisibleZero state visible) (extended : state <+: next) : VisibleZero next visible := by
  intro p member
  obtain ⟨height, output⟩ := zero p member
  exact ⟨height, readout_extends extended output⟩

theorem visibleZero_emit {state : State d} {visible : List Nat}
    (zero : VisibleZero state visible) (u : Nat → Nat) (height : Nat) (frame : List Binding) :
    VisibleZero (emit state u height 0 frame) (visible ++ [state.length]) := by
  intro p member
  rcases List.mem_append.mp member with old | added
  · exact zero.extends (emit_extends ..) p old
  · have same : p = state.length := by simpa only [List.mem_singleton] using added
    subst p
    exact ⟨height, readout_emit ..⟩

theorem NumericalHead.extends {state next : State d} {position : Nat}
    (head : NumericalHead state position) (inside : position < state.length) (extended : state <+: next) :
    NumericalHead next position := by
  intro j room root edge
  have oldEdge := (Parents.parent_prefix_eq (table_prefix extended) j position
    (by rwa [table_length])).trans edge
  obtain ⟨height, output⟩ := head j room root oldEdge
  exact ⟨height, readout_extends extended output⟩

theorem NumericalAuxiliary.extends {state next : State d} {position : Nat}
    (aux : NumericalAuxiliary state position) (inside : position < state.length) (extended : state <+: next) :
    NumericalAuxiliary next position := by
  obtain ⟨root, height, tag, tagCase, output, parents⟩ := aux
  refine ⟨root, height, tag, tagCase, readout_extends extended output, ?_⟩
  intro j room
  rw [← Parents.parent_prefix_eq (table_prefix extended) j position (by rwa [table_length])]
  exact parents j room

theorem numericalClasses_emit {state : State d} {heads nextHeads : List Nat}
    (classes : NumericalClasses state heads) (u : Nat → Nat) (height tag : Nat) (frame : List Binding)
    (retained : ∀ p ∈ heads, p ∈ nextHeads)
    (added : (state.length ∈ nextHeads ∧ NumericalHead (emit state u height tag frame) state.length) ∨
      NumericalAuxiliary (emit state u height tag frame) state.length) :
    NumericalClasses (emit state u height tag frame) nextHeads := by
  intro position inside
  by_cases old : position < state.length
  · rcases classes position old with ⟨member, head⟩ | aux
    · exact .inl ⟨retained position member, head.extends old (emit_extends ..)⟩
    · exact .inr (aux.extends old (emit_extends ..))
  · have same : position = state.length := by rw [emit_length] at inside; omega
    subst position
    exact added

theorem numericalClasses_emit_head {state : State d} {heads : List Nat}
    (classes : NumericalClasses state heads) (u : Nat → Nat) (height tag : Nat) (frame : List Binding)
    (head : NumericalHead (emit state u height tag frame) state.length) :
    NumericalClasses (emit state u height tag frame) (heads ++ [state.length]) :=
  numericalClasses_emit classes u height tag frame (fun _ member => List.mem_append_left _ member)
    (.inl ⟨List.mem_append_right _ (by simp), head⟩)

theorem numericalClasses_emit_aux {state : State d} {heads : List Nat}
    (classes : NumericalClasses state heads) (u : Nat → Nat) (height tag : Nat) (frame : List Binding)
    (aux : NumericalAuxiliary (emit state u height tag frame) state.length) :
    NumericalClasses (emit state u height tag frame) heads :=
  numericalClasses_emit classes u height tag frame (fun _ member => member) (.inr aux)

theorem emitted_source_numericalHead {d : Nat} {source : ParentContext} {visible : List Nat}
    (state : State d) (sourceCoherent : Parents.Coherent d source)
    (sourceValid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (zero : VisibleZero state visible) (coordinates : List Nat) (height tag : Nat) (frame : List Binding) :
    NumericalHead (emit state (vector state visible (Parents.label d source coordinates)) height tag frame)
      state.length := by
  intro j room root edge
  rw [emitted_parent, emitted_head_numerical_parents state sourceCoherent sourceValid view
    coordinates height tag j room] at edge
  obtain ⟨p, _, lookup⟩ := Option.bind_eq_some_iff.mp edge
  obtain ⟨h, output⟩ := zero root (List.mem_of_getElem? lookup)
  exact ⟨h, readout_extends (emit_extends ..) output⟩

theorem guard_numericalAuxiliary (state : State d) (u : Nat → Nat) (c : Nat) :
    NumericalAuxiliary (emit (emit state u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 [])
      (state.length + 1) :=
  ⟨state.length, c + 1, 1, .inl rfl, readout_extends (emit_extends ..) (readout_emit ..),
    fun j room => guard_numerical_parents state u c j room⟩

theorem NumericalGate.slot_numericalAuxiliary {d : Nat} {source : ParentContext} {coordinates : List Nat}
    {visible : List Nat} {original state : State d} {u : Nat → Nat} {gate : Nat}
    (scope : NumericalGate d source coordinates visible original state u gate) (height : Nat)
    (guard : Readout state gate height 2) (slotHeight : Nat) (frame : List Binding) :
    NumericalAuxiliary (emit state (fun j => u j + 2) slotHeight 0 frame) state.length :=
  ⟨gate, height, 2, .inr rfl, readout_extends (emit_extends ..) guard,
    fun j room => scope.slot_parents slotHeight frame j room⟩

theorem NumericalGate.closing_numericalAuxiliary {d : Nat} {source : ParentContext} {coordinates : List Nat}
    {visible : List Nat} {original state : State d} {u : Nat → Nat} {c : Nat}
    (scope : NumericalGate d source coordinates visible original state u (original.length + 1))
    (headed : emit (emit original u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 [] <+: state)
    (positive : 0 < d) (height tag : Nat) (frame : List Binding) :
    NumericalAuxiliary (emit state (fun j => u j + 1) height tag frame) state.length := by
  have firstToGuard : Parents.Ancestor (BMS.parentTable (d + 2) (matrix state)) 0
      original.length (original.length + 1) :=
    (Parents.Ancestor.up (guard_numerical_parents original u c 0 positive) (.refl _)).prefix
      (table_prefix headed)
  have definitionExtends := (emit_extends ..).trans headed
  refine ⟨original.length, c + 1, 1, .inl rfl,
    readout_extends (definitionExtends.trans (emit_extends ..)) (readout_emit ..), ?_⟩
  intro j room
  apply auxiliary_numerical_parents state _ height tag frame original.length scope.nonempty
    (firstToGuard.trans scope.fence) (fun k inside => ?_) j room
  rw [← Parents.reading_prefix (table_prefix definitionExtends) k original.length
    (by rw [table_length, emit_length]; omega), emitted_numerical_value original u (c + 1) 1 [] k inside]

theorem numericalHead_auxiliary_distinct_parent {state : State d} {a b j : Nat}
    (head : NumericalHead state a) (aux : NumericalAuxiliary state b) (room : j < d) :
    Parents.parent (BMS.parentTable (d + 2) (matrix state)) j a ≠
      Parents.parent (BMS.parentTable (d + 2) (matrix state)) j b := by
  obtain ⟨root, height, tag, tagCase, output, parents⟩ := aux
  intro same
  obtain ⟨h, zero⟩ := head j room root (same.trans (parents j room))
  have tagZero := readout_tag_unique output zero
  rcases tagCase with one | two <;> omega

theorem numericalAuxiliary_same_parent_not_ancestor {state : State d} {a b j : Nat}
    (left : NumericalAuxiliary state a) (right : NumericalAuxiliary state b)
    (positive : 0 < j) (room : j < d) (different : a ≠ b)
    (same : Parents.parent (BMS.parentTable (d + 2) (matrix state)) j a =
      Parents.parent (BMS.parentTable (d + 2) (matrix state)) j b) :
    ¬ Parents.Ancestor (BMS.parentTable (d + 2) (matrix state)) (j - 1) a b := by
  obtain ⟨p, _, _, _, _, leftParents⟩ := left
  obtain ⟨q, _, _, _, _, rightParents⟩ := right
  have roots : p = q := Option.some.inj ((leftParents j room).symm.trans (same.trans (rightParents j room)))
  subst q
  intro path
  obtain ⟨r, edge, prior⟩ := (Parents.Ancestor.iff_parent different).mp path
  have root : r = p := Option.some.inj (edge.symm.trans (rightParents (j - 1) (by omega)))
  subst r
  have earlier := Parents.parent_earlier (BMS.parentTable_valid _ _) (leftParents (j - 1) (by omega))
  have after := prior.le (BMS.parentTable_valid _ _)
  omega

/-- The endpoints of every actual intermediate-row SB pair must both
come from the recorded source-entry positions. No block inequality is used. -/
theorem NumericalClasses.intermediate_pair {state : State d} {heads : List Nat}
    (classes : NumericalClasses state heads) {a b j : Nat}
    (positive : 0 < j) (room : j < d) (before : a < b) (inside : b < state.length)
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (matrix state)) (j - 1) a b)
    (same : Parents.parent (BMS.parentTable (d + 2) (matrix state)) j a =
      Parents.parent (BMS.parentTable (d + 2) (matrix state)) j b) :
    a ∈ heads ∧ b ∈ heads := by
  rcases classes a (by omega) with ⟨aMember, aHead⟩ | aAux
  · rcases classes b inside with ⟨bMember, _⟩ | bAux
    · exact ⟨aMember, bMember⟩
    · exact False.elim (numericalHead_auxiliary_distinct_parent aHead bAux room same)
  · rcases classes b inside with ⟨_, bHead⟩ | bAux
    · exact False.elim (numericalHead_auxiliary_distinct_parent bHead aAux room same.symm)
    · exact False.elim (numericalAuxiliary_same_parent_not_ancestor aAux bAux positive room (by omega) same path)

/-- Row-zero siblings cannot mix source entries with auxiliary columns.
In the auxiliary case every numerical parent is the same definition or
guard position. This is a parent-type reduction, not a BN inequality. -/
theorem NumericalClasses.sibling_pair {state : State d} {heads : List Nat}
    (classes : NumericalClasses state heads) (positive : 0 < d) {a b : Nat}
    (aBound : a < state.length) (bBound : b < state.length)
    (same : Parents.parent (BMS.parentTable (d + 2) (matrix state)) 0 a =
      Parents.parent (BMS.parentTable (d + 2) (matrix state)) 0 b) :
    (a ∈ heads ∧ b ∈ heads) ∨
      ∃ root height tag, (tag = 1 ∨ tag = 2) ∧ Readout state root height tag ∧
        ∀ j, j < d →
          Parents.parent (BMS.parentTable (d + 2) (matrix state)) j a = some root ∧
          Parents.parent (BMS.parentTable (d + 2) (matrix state)) j b = some root := by
  rcases classes a aBound with ⟨aMember, aHead⟩ | aAux
  · rcases classes b bBound with ⟨bMember, _⟩ | bAux
    · exact .inl ⟨aMember, bMember⟩
    · exact False.elim (numericalHead_auxiliary_distinct_parent aHead bAux positive same)
  · rcases classes b bBound with ⟨_, bHead⟩ | bAux
    · exact False.elim (numericalHead_auxiliary_distinct_parent bHead aAux positive same.symm)
    · obtain ⟨p, height, tag, tagCase, output, aParents⟩ := aAux
      obtain ⟨q, _, _, _, _, bParents⟩ := bAux
      have roots : p = q := Option.some.inj ((aParents 0 positive).symm.trans (same.trans (bParents 0 positive)))
      subst q
      exact .inr ⟨p, height, tag, tagCase, output, fun j room => ⟨aParents j room, bParents j room⟩⟩

end BTnSSBMS.Encoder
