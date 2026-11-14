import BTnSSBMS.NumericalScope
import BTnSSBMS.NumericalLegality

/-!
Unit increments on the first d rows of every actual output column. This
module does not claim the same for the key and tag rows; those require the
additional environment/ownership analysis of the upper-bound argument.
-/
namespace BTnSSBMS.Parents

theorem UnitSteps.extend_one {d : Nat} {context next : ParentContext}
    (unit : UnitSteps d context) (valid : ContextValid next)
    (extended : context <+: next) (length : next.length = context.length + 1)
    (last : ∀ j, j < d → reading next j context.length =
      ((parent next j context.length).map fun p => reading next j p + 1).getD 0) :
    UnitSteps d next := by
  intro position bound j room
  by_cases old : position < context.length
  · rw [← reading_prefix extended j position old, ← parent_prefix_eq extended j position old]
    rw [unit position old j room]
    cases selected : parent context j position with
    | none => rfl
    | some p =>
      have earlier := parent_earlier valid (parent_prefix extended selected)
      simp only [Option.map_some, Option.getD_some]
      rw [reading_prefix extended j p (by omega)]
  · have same : position = context.length := by omega
    subst position
    exact last j room

theorem empty_unitSteps (d : Nat) : UnitSteps d [] := by
  intro position impossible
  simp at impossible

end BTnSSBMS.Parents

namespace BTnSSBMS.Encoder

theorem emit_unitSteps (state : State d) (u : Nat → Nat) (height tag : Nat) (frame : List Binding)
    (unit : Parents.UnitSteps d (BMS.parentTable (d + 2) (matrix state)))
    (newUnit : ∀ j, j < d → u j =
      ((Parents.parent (BMS.parentTable (d + 2) (matrix (emit state u height tag frame))) j state.length).map
        fun p => Parents.reading (BMS.parentTable (d + 2) (matrix (emit state u height tag frame))) j p + 1).getD 0) :
    Parents.UnitSteps d (BMS.parentTable (d + 2) (matrix (emit state u height tag frame))) := by
  apply unit.extend_one (BMS.parentTable_valid _ _) (table_emit_prefix ..)
    (by rw [table_length, table_length, emit_length])
  intro j room
  rw [table_length, emitted_numerical_value state u height tag frame j room]
  exact newUnit j room

theorem emit_represented_unitSteps {d : Nat} {source : ParentContext} {visible : List Nat}
    (state : State d) (sourceCoherent : Parents.Coherent d source)
    (sourceValid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (unit : Parents.UnitSteps d (BMS.parentTable (d + 2) (matrix state)))
    (coordinates : List Nat) (height tag : Nat) (frame : List Binding) :
    Parents.UnitSteps d (BMS.parentTable (d + 2) (matrix
      (emit state (vector state visible (Parents.label d source coordinates)) height tag frame))) := by
  apply emit_unitSteps state _ height tag frame unit
  intro j room
  rw [emitted_parent, emitted_head_numerical_parents state sourceCoherent sourceValid view coordinates height tag j room,
    representative_eq_point view, vector_eq_represented view]
  cases selected : (Parents.label d source coordinates).parents[j]?.join with
  | none => simp only [selected, Option.map_none, Option.getD_none, Parents.representedValue]
  | some p =>
    have sourceBound := Parents.label_parent_bound d source coordinates j p selected
    simp only [selected, Option.map_some, Option.getD_some, Parents.representedValue]
    rw [Parents.reading_prefix (table_emit_prefix ..) j (Parents.point visible p) (view.bounded p sourceBound)]

theorem emit_fenced_unitSteps (state : State d) (u : Nat → Nat) (height tag : Nat)
    (frame : List Binding) (root : Nat)
    (unit : Parents.UnitSteps d (BMS.parentTable (d + 2) (matrix state)))
    (nonempty : 0 < state.length)
    (fence : Parents.Ancestor (BMS.parentTable (d + 2) (matrix state)) 0 root (state.length - 1))
    (values : ∀ j, j < d → u j = Parents.reading (BMS.parentTable (d + 2) (matrix state)) j root + 1) :
    Parents.UnitSteps d (BMS.parentTable (d + 2) (matrix (emit state u height tag frame))) := by
  apply emit_unitSteps state u height tag frame unit
  intro j room
  rw [auxiliary_numerical_parents state u height tag frame root nonempty fence values j room]
  simp only [Option.map_some, Option.getD_some]
  have rootBound : root < (BMS.parentTable (d + 2) (matrix state)).length := by
    have before := fence.le (BMS.parentTable_valid _ _)
    rw [table_length]
    omega
  rw [← Parents.reading_prefix (table_emit_prefix ..) j root rootBound]
  exact values j room

theorem guard_unitSteps (state : State d) (u : Nat → Nat) (c : Nat)
    (unit : Parents.UnitSteps d (BMS.parentTable (d + 2) (matrix (emit state u (c + 1) 1 [])))) :
    Parents.UnitSteps d (BMS.parentTable (d + 2) (matrix
      (emit (emit state u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 []))) := by
  apply emit_fenced_unitSteps (emit state u (c + 1) 1 []) _ (c + 2) 2 [] state.length unit
    (by rw [emit_length]; omega)
    (by rw [emit_length, Nat.add_sub_cancel]; exact .refl _) ?_
  intro j room
  rw [emitted_numerical_value state u (c + 1) 1 [] j room]

theorem NumericalGate.slot_unitSteps {d : Nat} {source : ParentContext} {coordinates : List Nat}
    {visible : List Nat} {original state : State d} {u : Nat → Nat} {gate : Nat}
    (scope : NumericalGate d source coordinates visible original state u gate)
    (height : Nat) (frame : List Binding)
    (unit : Parents.UnitSteps d (BMS.parentTable (d + 2) (matrix state))) :
    Parents.UnitSteps d (BMS.parentTable (d + 2) (matrix
      (emit state (fun j => u j + 2) height 0 frame))) :=
  emit_fenced_unitSteps state _ height 0 frame gate unit scope.nonempty scope.fence
    (fun j room => by rw [scope.values j room])

theorem closing_unitSteps {d : Nat} {source : ParentContext} {visible : List Nat}
    (state next : State d) (coordinates : List Nat) (c : Nat) (frame : List Binding)
    (scope : NumericalGate d source coordinates visible state next
      (vector state visible (Parents.label d source coordinates)) (state.length + 1))
    (withGuardExtends :
      emit (emit state (vector state visible (Parents.label d source coordinates)) (c + 1) 1 [])
        (fun j => vector state visible (Parents.label d source coordinates) j + 1) (c + 2) 2 [] <+: next)
    (positive : 0 < d)
    (unit : Parents.UnitSteps d (BMS.parentTable (d + 2) (matrix next))) :
    Parents.UnitSteps d (BMS.parentTable (d + 2) (matrix (emit next
      (fun j => vector state visible (Parents.label d source coordinates) j + 1) (c + 2) 0 frame))) := by
  have dExtends := (emit_extends ..).trans withGuardExtends
  have dToH := (Parents.Ancestor.up (guard_numerical_parents state _ c 0 positive) (.refl _)).prefix
    (table_prefix withGuardExtends)
  apply emit_fenced_unitSteps next _ (c + 2) 0 frame state.length unit scope.nonempty
    (dToH.trans scope.fence)
  intro j room
  rw [← Parents.reading_prefix (table_prefix dExtends) j state.length
    (by rw [table_length, emit_length]; omega), emitted_numerical_value state _ (c + 1) 1 [] j room]

mutual
  theorem encode_unitSteps (d : Nat) (e : NumericalExpr)
      (source : ParentContext) (visible : List Nat) (state : State d)
      (positive : 0 < d) (sourceCoherent : Parents.Coherent d source)
      (sourceValid : Parents.ContextValid source)
      (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
      (separated : Source.ForestSeparated e)
      (unit : Parents.UnitSteps d (BMS.parentTable (d + 2) (matrix state))) :
      Parents.UnitSteps d
        (BMS.parentTable (d + 2) (matrix (encode d (Parents.annotate d source e) visible state))) := by
    cases e with
    | nil => exact unit
    | cons coordinates hs tail =>
      have nextCoherent := Parents.coherent_append_label sourceCoherent coordinates
      have nextValid := Parents.context_valid_append_label d source sourceValid coordinates
      simp only [Parents.annotate, encode]
      split
      next bound same =>
        apply encode_unitSteps d tail _ _ _ positive nextCoherent nextValid
          (emit_numerical_view state sourceCoherent sourceValid view coordinates bound.height 0 _) separated.2
        exact emit_represented_unitSteps state sourceCoherent sourceValid view unit coordinates bound.height 0 _
      next fresh =>
        let a := Parents.label d source coordinates
        let annotated := Parents.annotateForests d (source ++ [a]) hs
        let key := Keys.ofColumn d visible.length a annotated
        let below := smaller (frameAt state (representative visible a (d - 1))) key
        let c := (base below).height
        let u := vector state visible a
        let withGuard := emit (emit state u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 []
        let withForests := encodeForests d annotated visible u c below withGuard
        have gate := initial_numerical_gate state sourceCoherent sourceValid view coordinates c
        have gateAfter := encodeForests_numerical_gate d hs source coordinates visible state withGuard u
          (state.length + 1) c below positive sourceCoherent sourceValid view gate separated.1
        have unitD := emit_represented_unitSteps state sourceCoherent sourceValid view unit coordinates (c + 1) 1 []
        have unitH := guard_unitSteps state u c unitD
        have unitForests := encodeForests_unitSteps d hs source coordinates visible state withGuard u
          (state.length + 1) c below positive sourceCoherent sourceValid view gate separated.1 unitH
        have finalView := closing_numerical_view state withForests sourceValid view coordinates c
          (below ++ [⟨key, c + 2, some withForests.length, some state.length⟩]) gateAfter
          (encodeForests_extends d annotated visible u c below withGuard) positive sourceCoherent
        apply encode_unitSteps d tail _ _ _ positive nextCoherent nextValid finalView separated.2
        exact closing_unitSteps state withForests coordinates c _ gateAfter
          (encodeForests_extends d annotated visible u c below withGuard) positive unitForests

  theorem encodeForests_unitSteps (d : Nat) (hs : Forests (List Nat))
      (source : ParentContext) (coordinates : List Nat) (visible : List Nat)
      (original state : State d) (u : Nat → Nat) (gate c : Nat) (below : List Binding)
      (positive : 0 < d) (sourceCoherent : Parents.Coherent d source)
      (sourceValid : Parents.ContextValid source)
      (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix original)) visible)
      (scope : NumericalGate d source coordinates visible original state u gate)
      (separated : Source.ForestsAbove (coordinates[0]?.getD 0) hs)
      (unit : Parents.UnitSteps d (BMS.parentTable (d + 2) (matrix state))) :
      Parents.UnitSteps d (BMS.parentTable (d + 2) (matrix
        (encodeForests d (Parents.annotateForests d (source ++ [Parents.label d source coordinates]) hs)
          visible u c below state))) := by
    cases hs with
    | nil => exact unit
    | cons h hs =>
      let a := Parents.label d source coordinates
      let withSlot := emit state (fun j => u j + 2) (c + 2) 0 below
      have nextCoherent := Parents.coherent_append_label sourceCoherent coordinates
      have nextValid := Parents.context_valid_append_label d source sourceValid coordinates
      have slotView := scope.slot_view sourceValid view (c + 2) below
      obtain ⟨finalVisible, extended, forestView⟩ := encode_numerical_view d h (source ++ [a])
        (visible ++ [state.length]) withSlot positive nextCoherent nextValid slotView separated.2.1
      have nextScope := scope.after_forest positive sourceCoherent sourceValid view.length
        (c + 2) below (Source.labels h) (encode_extends d _ _ _) extended separated.1 forestView
      have forestUnit := encode_unitSteps d h (source ++ [a]) (visible ++ [state.length]) withSlot
        positive nextCoherent nextValid slotView separated.2.1 (scope.slot_unitSteps (c + 2) below unit)
      exact encodeForests_unitSteps d hs source coordinates visible original
        (encode d (Parents.annotate d (source ++ [a]) h) (visible ++ [state.length]) withSlot)
        u gate c below positive sourceCoherent sourceValid view nextScope separated.2.2 forestUnit
end

/-- Every output column has correct unit increments in the first d rows.
The other two rows are deliberately not included in this conclusion. -/
theorem source_unitSteps (d : Nat) (e : NumericalExpr) (positive : 0 < d)
    (separated : Source.ForestSeparated e) :
    Parents.UnitSteps d (BMS.parentTable (d + 2) (fromSource d e)) :=
  encode_unitSteps d e [] [] [] positive (Parents.empty_coherent d) Parents.empty_context_valid
    (Parents.empty_numerical_view d) separated (Parents.empty_unitSteps d)

end BTnSSBMS.Encoder
