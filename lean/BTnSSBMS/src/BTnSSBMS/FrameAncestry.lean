import BTnSSBMS.KeyParentGeometry

/-!
Anchoring saved bindings in computed BMS key-row ancestry. Realized pointer
values alone do not give this invariant. The lemmas below transport and cut
actual ancestor paths; preservation through the whole encoder is separate.
-/
namespace BTnSSBMS.Encoder

def FrameAncestral (state : State d) (position : Nat) (frame : List Binding) : Prop :=
  ∀ b ∈ frame, ∃ p, b.latest = some p ∧
    Parents.Ancestor (BMS.parentTable (d + 2) (matrix state)) d p position ∧
    (∀ q, b.definition = some q →
      Parents.Ancestor (BMS.parentTable (d + 2) (matrix state)) d q position)

def FramesAncestral (state : State d) : Prop :=
  ∀ position col, state[position]? = some col → FrameAncestral state position col.frame

theorem empty_frame_ancestral (state : State d) (position : Nat) : FrameAncestral state position [] := by
  intro b impossible; simp at impossible

theorem FrameAncestral.subset {state : State d} {position : Nat} {small large : List Binding}
    (paths : FrameAncestral state position large) (subset : ∀ b ∈ small, b ∈ large) :
    FrameAncestral state position small := fun b member => paths b (subset b member)

theorem FrameAncestral.extends {state next : State d} {position : Nat} {frame : List Binding}
    (paths : FrameAncestral state position frame) (extended : state <+: next) :
    FrameAncestral next position frame := by
  intro b member
  obtain ⟨p, latest, path, definitions⟩ := paths b member
  exact ⟨p, latest, path.prefix (table_prefix extended), fun q found =>
    (definitions q found).prefix (table_prefix extended)⟩

theorem FrameAncestral.trans {state : State d} {left right : Nat} {frame : List Binding}
    (paths : FrameAncestral state left frame)
    (advance : Parents.Ancestor (BMS.parentTable (d + 2) (matrix state)) d left right) :
    FrameAncestral state right frame := by
  intro b member
  obtain ⟨p, latest, path, definitions⟩ := paths b member
  exact ⟨p, latest, path.trans advance, fun q found => (definitions q found).trans advance⟩

/-- If a saved binding's height is no higher than another point on the
same key-row chain, its actual pointers are ancestors of that point too. -/
theorem FrameAncestral.cut {state : State d} {position root : Nat} {frame kept : List Binding}
    (paths : FrameAncestral state position frame) (realized : FrameRealized state frame)
    (subset : ∀ b ∈ kept, b ∈ frame)
    (rootPath : Parents.Ancestor (BMS.parentTable (d + 2) (matrix state)) d root position)
    (heights : ∀ b ∈ kept, b.height ≤ Parents.reading (BMS.parentTable (d + 2) (matrix state)) d root) :
    FrameAncestral state root kept := by
  intro b member
  obtain ⟨p, latest, path, definitions⟩ := paths b (subset b member)
  have known := realized b (subset b member)
  have output : Readout state p b.height 0 := by simpa only [latest] using known.1
  refine ⟨p, latest, path.of_reading_le (BMS.parentTable_coherent _ _) rootPath ?_, ?_⟩
  · rw [output.key_reading]; exact heights b member
  · intro q found
    have info := known.2.1
    rw [found] at info
    obtain ⟨h, height, output⟩ := info
    apply (definitions q found).of_reading_le (BMS.parentTable_coherent _ _) rootPath
    rw [output.key_reading]
    have bound := heights b member
    omega

theorem framesAncestral_emit {state : State d} (paths : FramesAncestral state)
    (u : Nat → Nat) (height tag : Nat) (frame : List Binding)
    (added : FrameAncestral (emit state u height tag frame) state.length frame) :
    FramesAncestral (emit state u height tag frame) := by
  intro position col lookup
  by_cases old : position < state.length
  · have original : state[position]? = some col := by
      simpa only [emit, List.getElem?_append_left old] using lookup
    exact (paths position col original).extends (emit_extends ..)
  · have bound := (List.getElem?_eq_some_iff.mp lookup).choose
    have same : position = state.length := by simp only [emit_length] at bound; omega
    subst position
    have column : col = ⟨row d u height tag, row_width d u height tag, frame⟩ := by
      simpa only [emit, List.getElem?_concat_length, Option.some.injEq] using lookup.symm
    subst col
    exact added

theorem queried_frame_ancestral {state : State d} (paths : FramesAncestral state)
    (position : Nat) (inside : position < state.length) :
    FrameAncestral state position (frameAt state (some position)) := by
  simpa only [frameAt, Option.bind_some, List.getElem?_eq_getElem inside] using
    paths position state[position] (List.getElem?_eq_getElem inside)

theorem base_member {frame : List Binding} (nonempty : frame ≠ []) : base frame ∈ frame := by
  simp only [base, List.getLast?_eq_some_getLast nonempty, Option.getD_some]
  exact List.getLast_mem nonempty

theorem smaller_height_lt_bound {frame : List Binding} (ordered : FrameOrdered frame)
    (key : Key) (bound : Binding) (found : equal frame key = some bound)
    (b : Binding) (member : b ∈ smaller frame key) : b.height < bound.height := by
  have boundMember : bound ∈ frame := List.mem_of_find?_eq_some found
  have same : bound.key = key := Keys.compare_eq_imp _ _
    (by simpa only [beq_iff_eq] using List.find?_some found)
  apply binding_height_lt ordered b bound (List.mem_filter.mp member).1 boundMember
  simpa only [same, beq_iff_eq] using (List.mem_filter.mp member).2

theorem smaller_empty_at_zero {frame : List Binding} (ordered : FrameOrdered frame)
    (key : Key) (bound : Binding) (found : equal frame key = some bound) (zero : bound.height = 0) :
    smaller frame key = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro b member
  have impossible := smaller_height_lt_bound ordered key bound found b member
  omega

theorem fresh_definition_anchor {state : State d} {position : Nat} {frame : List Binding}
    (paths : FrameAncestral state position frame) (realized : FrameRealized state frame)
    (ordered : FrameOrdered frame) (key : Key) (nonempty : smaller frame key ≠ []) :
    ∃ root, (base (smaller frame key)).latest = some root ∧
      Readout state root (base (smaller frame key)).height 0 ∧
      Parents.Ancestor (BMS.parentTable (d + 2) (matrix state)) d root position ∧
      FrameAncestral state root (smaller frame key) := by
  have member := base_member nonempty
  have original := (List.mem_filter.mp member).1
  obtain ⟨root, latest, path, _⟩ := paths _ original
  have output : Readout state root (base (smaller frame key)).height 0 := by
    simpa only [latest] using (realized _ original).1
  refine ⟨root, latest, output, path, paths.cut realized ?_ path ?_⟩
  · intro b hb; exact (List.mem_filter.mp hb).1
  · intro b hb
    rw [output.key_reading]
    exact member_height_le_base (smaller_ordered ordered key) b hb

theorem reused_definition_anchor {state : State d} {position : Nat} {frame : List Binding}
    (paths : FrameAncestral state position frame) (realized : FrameRealized state frame)
    (ordered : FrameOrdered frame) (key : Key) (bound : Binding)
    (found : equal frame key = some bound) (positive : 0 < bound.height) :
    ∃ root h, bound.definition = some root ∧ bound.height = h + 1 ∧ Readout state root h 1 ∧
      Parents.Ancestor (BMS.parentTable (d + 2) (matrix state)) d root position ∧
      FrameAncestral state root (smaller frame key) := by
  have member : bound ∈ frame := List.mem_of_find?_eq_some found
  have info := (realized bound member).2.1
  cases definition : bound.definition with
  | none => simp only [definition] at info; omega
  | some root =>
    simp only [definition] at info
    obtain ⟨h, height, output⟩ := info
    obtain ⟨_, _, _, definitions⟩ := paths bound member
    have path := definitions root definition
    refine ⟨root, h, rfl, height, output, path, paths.cut realized ?_ path ?_⟩
    · intro b hb; exact (List.mem_filter.mp hb).1
    · intro b hb
      rw [output.key_reading]
      have less := smaller_height_lt_bound ordered key bound found b hb
      omega

theorem frame_ancestral_append {state : State d} {position : Nat} {frame : List Binding}
    (paths : FrameAncestral state position frame) (bound : Binding)
    (latest : bound.latest = some position)
    (definition : ∀ root, bound.definition = some root →
      Parents.Ancestor (BMS.parentTable (d + 2) (matrix state)) d root position) :
    FrameAncestral state position (frame ++ [bound]) := by
  intro b member
  rcases List.mem_append.mp member with old | new
  · exact paths b old
  · have same : b = bound := by simpa only [List.mem_singleton] using new
    subst b
    exact ⟨position, latest, .refl _, definition⟩

end BTnSSBMS.Encoder
