import BTnSSBMS.EntryParentGeometry

/-!
The numerical path from a source entry's first output to its current
representative contains only auxiliary columns. Contracting this path
cannot introduce another source-entry ancestor. Bounds and computed
parents are explicit; no inverse ancestry premise is assumed.
-/
namespace BTnSSBMS.Encoder

structure NumericalFiber (state : State d) (first representative : Nat) : Prop where
  firstBound : first < state.length
  representativeBound : representative < state.length
  connected : ∀ j, j < d →
    Parents.Ancestor (BMS.parentTable (d + 2) (matrix state)) j first representative
  reduce : ∀ j, j < d → ∀ p,
    Parents.Ancestor (BMS.parentTable (d + 2) (matrix state)) j p representative →
      Parents.Ancestor (BMS.parentTable (d + 2) (matrix state)) j p first ∨
        NumericalAuxiliary state p

theorem NumericalFiber.refl (state : State d) (first : Nat) (inside : first < state.length) :
    NumericalFiber state first first :=
  ⟨inside, inside, fun _ _ => .refl _, fun _ _ _ path => .inl path⟩

theorem NumericalFiber.extends {state next : State d} {first representative : Nat}
    (fiber : NumericalFiber state first representative) (extended : state <+: next) :
    NumericalFiber next first representative := by
  have longer := extended.length_le
  refine ⟨by have := fiber.firstBound; omega, by have := fiber.representativeBound; omega,
    fun j room => (fiber.connected j room).prefix (table_prefix extended), ?_⟩
  intro j room p path
  have previous := path.restrict (table_prefix extended) (BMS.parentTable_valid _ _)
    (by rw [table_length]; exact fiber.representativeBound)
  rcases fiber.reduce j room p previous with prior | aux
  · exact .inl (prior.prefix (table_prefix extended))
  · have before := previous.le (BMS.parentTable_valid _ _)
    exact .inr (aux.extends (by have := fiber.representativeBound; omega) extended)

theorem NumericalFiber.auxiliary {state : State d} {first previous representative : Nat}
    (fiber : NumericalFiber state first previous) (inside : representative < state.length)
    (aux : NumericalAuxiliary state representative)
    (parents : ∀ j, j < d → Parents.parent (BMS.parentTable (d + 2) (matrix state)) j representative =
      some previous) : NumericalFiber state first representative := by
  refine ⟨fiber.firstBound, inside, fun j room => .up (parents j room) (fiber.connected j room), ?_⟩
  intro j room p path
  by_cases same : p = representative
  · subst p; exact .inr aux
  · obtain ⟨q, edge, prior⟩ := (Parents.Ancestor.iff_parent same).mp path
    have equalParent : q = previous := Option.some.inj (edge.symm.trans (parents j room))
    subst q
    exact fiber.reduce j room p prior

theorem NumericalFiber.head_ancestor {state : State d} {first representative p j : Nat}
    (fiber : NumericalFiber state first representative) (room : j < d)
    (head : NumericalHead state p)
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (matrix state)) j p representative) :
    Parents.Ancestor (BMS.parentTable (d + 2) (matrix state)) j p first := by
  rcases fiber.reduce j room p path with prior | aux
  · exact prior
  · exact False.elim (numericalHead_auxiliary_distinct_parent head aux room rfl)

theorem initial_guard_fiber (state : State d) (u : Nat → Nat) (c : Nat) :
    NumericalFiber (emit (emit state u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 [])
      state.length (state.length + 1) :=
  (NumericalFiber.refl _ state.length (by simp only [emit_length]; omega)).auxiliary
    (by simp only [emit_length]; omega) (guard_numericalAuxiliary state u c)
    (guard_numerical_parents state u c)

theorem NumericalGate.slot_fiber {d : Nat} {source : ParentContext} {coordinates visible : List Nat}
    {original state : State d} {u : Nat → Nat} {gate : Nat}
    (scope : NumericalGate d source coordinates visible original state u gate)
    (fiber : NumericalFiber state original.length gate) {height : Nat}
    (guard : Readout state gate height 2) (slotHeight : Nat) (frame : List Binding) :
    NumericalFiber (emit state (fun j => u j + 2) slotHeight 0 frame) original.length state.length :=
  (fiber.extends (emit_extends ..)).auxiliary (by rw [emit_length]; omega)
    (scope.slot_numericalAuxiliary height guard slotHeight frame) (scope.slot_parents slotHeight frame)

theorem headState_fiber {d : Nat} {source : ParentContext} {visible : List Nat}
    (state : State d) (positive : 0 < d) (coherent : Parents.Coherent d source)
    (valid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (coordinates : List Nat) (hs : Forests (List Nat))
    (separated : Source.ForestsAbove (coordinates[0]?.getD 0) hs) :
    let headed := headState d (Parents.label d source coordinates)
      (Parents.annotateForests d (source ++ [Parents.label d source coordinates]) hs) visible state
    NumericalFiber headed state.length (headed.length - 1) := by
  dsimp only
  simp only [headState, encode]
  split
  next bound found =>
    simp only [emit_length, Nat.add_sub_cancel]
    exact NumericalFiber.refl _ state.length (by rw [emit_length]; omega)
  next fresh =>
    let a := Parents.label d source coordinates
    let annotated := Parents.annotateForests d (source ++ [a]) hs
    let key := Keys.ofColumn d visible.length a annotated
    let below := smaller (frameAt state (representative visible a (d - 1))) key
    let c := (base below).height
    let u := vector state visible a
    let guarded := emit (emit state u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 []
    let forests := encodeForests d annotated visible u c below guarded
    let finalFrame := below ++ [⟨key, c + 2, some forests.length, some state.length⟩]
    let closed := emit forests (fun j => u j + 1) (c + 2) 0 finalFrame
    have scope := encodeForests_numerical_gate d hs source coordinates visible state guarded u
      (state.length + 1) c below positive coherent valid view
      (initial_numerical_gate state coherent valid view coordinates c) separated
    have guardPrefix : guarded <+: forests := encodeForests_extends ..
    have definitionPrefix : emit state u (c + 1) 1 [] <+: forests := (emit_extends ..).trans guardPrefix
    have firstToGuard : Parents.Ancestor (BMS.parentTable (d + 2) (matrix forests)) 0
        state.length (state.length + 1) :=
      (Parents.Ancestor.up (guard_numerical_parents state u c 0 positive) (.refl _)).prefix
        (table_prefix guardPrefix)
    have parents : ∀ j, j < d → Parents.parent (BMS.parentTable (d + 2) (matrix closed))
        j forests.length = some state.length := by
      intro j room
      apply auxiliary_numerical_parents forests _ (c + 2) 0 finalFrame state.length scope.nonempty
        (firstToGuard.trans scope.fence) (fun k inside => ?_) j room
      rw [← Parents.reading_prefix (table_prefix definitionPrefix) k state.length
        (by rw [table_length, emit_length]; omega), emitted_numerical_value state u (c + 1) 1 [] k inside]
    have before : state.length < closed.length := by
      have longer := definitionPrefix.length_le
      simp only [emit_length] at longer
      dsimp only [closed]
      rw [emit_length]
      omega
    have fiber : NumericalFiber closed state.length forests.length :=
      (NumericalFiber.refl closed state.length before).auxiliary
      (by dsimp only [closed]; rw [emit_length]; exact Nat.lt_succ_self _)
      (scope.closing_numericalAuxiliary guardPrefix positive (c + 2) 0 finalFrame) parents
    simpa only [emit_length, Nat.add_sub_cancel] using fiber

end BTnSSBMS.Encoder
