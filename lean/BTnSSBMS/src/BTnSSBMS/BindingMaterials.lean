import BTnSSBMS.EncoderBindingSources
import BTnSSBMS.CrossEntryKeyTransport

/-!
The payload of a saved binding, not just its numerical source position.
The material list is a proof-side lexical context of actual attachment
lists. It is extended by the source column being encoded and restored
on a forest exit. It does not change the encoder or its keys.
-/
namespace BTnSSBMS.Keys

theorem atContext_prefix (d : Nat) {source target : ParentContext}
    (initial : source <+: target) {position : Nat} (inside : position < source.length)
    (hs : Forests (List Nat)) :
    atContext d target position hs = atContext d source position hs := by
  obtain ⟨extra, rfl⟩ := initial
  simp only [atContext, List.getElem?_append_left inside,
    List.take_append_of_le_length (by omega : position + 1 ≤ source.length)]

theorem atContext_append (d : Nat) (source : ParentContext) (coordinates : List Nat)
    (hs : Forests (List Nat)) :
    atContext d (source ++ [Parents.label d source coordinates]) source.length hs =
      ofColumn d source.length (Parents.label d source coordinates)
        (Parents.annotateForests d (source ++ [Parents.label d source coordinates]) hs) := by
  simp only [atContext, List.getElem?_concat_length, Option.getD_some]
  rw [show source.length + 1 = (source ++ [Parents.label d source coordinates]).length by simp,
    List.take_length]

end BTnSSBMS.Keys

namespace BTnSSBMS.Source

/-- Each entry is the whole attachment list actually carried by that
source column, checked in its own original numerical prefix. -/
structure MaterialContext (d : Nat) (source : ParentContext)
    (materials : List (Forests (List Nat))) : Prop where
  length : materials.length = source.length
  legal : ∀ i, i < source.length →
    (source[i]?.getD default).coordinates.length = d ∧
      FiniteLegalForests d (source.take (i + 1)) (Parents.reading source 0 i)
        (materials[i]?.getD .nil)

theorem empty_materialContext (d : Nat) : MaterialContext d [] [] :=
  ⟨rfl, by intro i inside; simp at inside⟩

theorem MaterialContext.append {d : Nat} {source : ParentContext}
    {materials : List (Forests (List Nat))} (known : MaterialContext d source materials)
    (coordinates : List Nat) (hs : Forests (List Nat)) (width : coordinates.length = d)
    (legal : FiniteLegalForests d (source ++ [Parents.label d source coordinates])
      (coordinates[0]?.getD 0) hs) :
    MaterialContext d (source ++ [Parents.label d source coordinates]) (materials ++ [hs]) := by
  refine ⟨by simp only [List.length_append, List.length_cons, List.length_nil, known.length], ?_⟩
  intro i inside
  by_cases old : i < source.length
  · have value := known.legal i old
    have matBound : i < materials.length := by rw [known.length]; exact old
    have reading := Parents.reading_prefix
      (List.prefix_append source [Parents.label d source coordinates]) 0 i old
    simpa only [List.getElem?_append_left old, List.getElem?_append_left matBound,
      List.take_append_of_le_length (by omega : i + 1 ≤ source.length), ← reading] using value
  · have same : i = source.length := by
      simp only [List.length_append, List.length_cons, List.length_nil] at inside
      omega
    subst i
    have full : source.length + 1 = (source ++ [Parents.label d source coordinates]).length := by simp
    rw [List.getElem?_concat_length, Option.getD_some, full, List.take_length,
      ← known.length, List.getElem?_concat_length, Option.getD_some, known.length]
    exact ⟨width, by simpa only [Parents.reading_append_label] using legal⟩

end BTnSSBMS.Source

namespace BTnSSBMS.Encoder

def BindingMaterial (d : Nat) (source : ParentContext) (visible : List Nat)
    (materials : List (Forests (List Nat))) (b : Binding) : Prop :=
  match b.latest with
  | none => b.key = .nil
  | some p => ∃ i, i < source.length ∧ p = Parents.point visible i ∧
      b.key = Keys.atContext d source i (materials[i]?.getD .nil)

def FrameMaterials (d : Nat) (source : ParentContext) (visible : List Nat)
    (materials : List (Forests (List Nat))) (frame : List Binding) : Prop :=
  ∀ b ∈ frame, BindingMaterial d source visible materials b

structure VisibleMaterials (d : Nat) (source : ParentContext) (visible owners : List Nat)
    (materials : List (Forests (List Nat))) (state : State d) : Prop where
  sources : VisibleSources d source visible owners state
  materialContext : Source.MaterialContext d source materials
  frames : ∀ i, i < source.length → ∃ col,
    state[Parents.point visible i]? = some col ∧ FrameMaterials d source visible materials col.frame

structure InheritedMaterials (d : Nat) (source : ParentContext) (coordinates visible owners : List Nat)
    (materials : List (Forests (List Nat))) (frame : List Binding) : Prop where
  sources : InheritedSources d source coordinates visible owners frame
  materialContext : Source.MaterialContext d source materials
  keys : FrameMaterials d source visible materials frame

theorem empty_visibleMaterials (d : Nat) : VisibleMaterials d [] [] [] [] [] :=
  ⟨empty_visibleSources d, Source.empty_materialContext d, by intro i inside; simp at inside⟩

theorem VisibleMaterials.extends {d : Nat} {source : ParentContext} {visible owners : List Nat}
    {materials : List (Forests (List Nat))} {state next : State d}
    (known : VisibleMaterials d source visible owners materials state) (extended : state <+: next) :
    VisibleMaterials d source visible owners materials next := by
  refine ⟨known.sources.extends extended, known.materialContext, ?_⟩
  intro i inside
  obtain ⟨col, lookup, payload⟩ := known.frames i inside
  obtain ⟨extra, rfl⟩ := extended
  have bounded := (List.getElem?_eq_some_iff.mp lookup).choose
  exact ⟨col, by rw [List.getElem?_append_left bounded]; exact lookup, payload⟩

theorem FrameMaterials.append {d : Nat} {source : ParentContext} {visible : List Nat}
    {materials : List (Forests (List Nat))} {frame : List Binding}
    (known : FrameMaterials d source visible materials frame)
    (length : visible.length = source.length) (materialLength : materials.length = source.length)
    (a : ParentLabel) (point : Nat) (hs : Forests (List Nat)) :
    FrameMaterials d (source ++ [a]) (visible ++ [point]) (materials ++ [hs]) frame := by
  intro b member
  have value := known b member
  cases latest : b.latest with
  | none => simpa only [BindingMaterial, latest] using value
  | some p =>
    simp only [BindingMaterial, latest] at value ⊢
    obtain ⟨i, inside, named, key⟩ := value
    refine ⟨i, by simp only [List.length_append, List.length_cons, List.length_nil]; omega, ?_, ?_⟩
    · rw [Parents.point_append_old visible i point (by omega)]
      exact named
    · rw [List.getElem?_append_left (by omega : i < materials.length),
        Keys.atContext_prefix d (List.prefix_append _ _) inside]
      exact key

theorem virtual_frame_materials (d : Nat) (source : ParentContext) (visible : List Nat)
    (materials : List (Forests (List Nat))) : FrameMaterials d source visible materials virtualFrame := by
  intro b member
  have same : b = zeroBinding := by simpa only [virtualFrame, List.mem_singleton] using member
  subst b
  rfl

theorem queried_frame_inheritedMaterials {d : Nat} {source : ParentContext}
    {visible owners : List Nat} {materials : List (Forests (List Nat))} {state : State d}
    (known : VisibleMaterials d source visible owners materials state)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (coordinates : List Nat) :
    InheritedMaterials d source coordinates visible owners materials
      (frameAt state (representative visible (Parents.label d source coordinates) (d - 1))) := by
  refine ⟨queried_frame_inheritedSources known.sources view coordinates, known.materialContext, ?_⟩
  rw [representative_eq_point view]
  cases selected : (Parents.label d source coordinates).parents[d - 1]?.join with
  | none =>
    simpa only [Option.map_none, frameAt, Option.bind_none] using
      virtual_frame_materials d source visible materials
  | some parent =>
    have inside := Parents.label_parent_bound d source coordinates (d - 1) parent selected
    obtain ⟨col, lookup, payload⟩ := known.frames parent inside
    simpa only [Option.map_some, frameAt, Option.bind_some, lookup] using payload

theorem smaller_inheritedMaterials {d : Nat} {source : ParentContext}
    {coordinates visible owners : List Nat} {materials : List (Forests (List Nat))}
    {frame : List Binding} (known : InheritedMaterials d source coordinates visible owners materials frame)
    (key : Key) : InheritedMaterials d source coordinates visible owners materials (smaller frame key) :=
  ⟨smaller_inheritedSources known.sources key, known.materialContext,
    fun b member => known.keys b (List.mem_filter.mp member).1⟩

theorem VisibleMaterials.append_emit {d : Nat} {source : ParentContext}
    {visible owners : List Nat} {materials : List (Forests (List Nat))} {state : State d}
    (known : VisibleMaterials d source visible owners materials state)
    (coordinates : List Nat) (hs : Forests (List Nat)) (width : coordinates.length = d)
    (legal : Source.FiniteLegalForests d (source ++ [Parents.label d source coordinates])
      (coordinates[0]?.getD 0) hs)
    (u : Nat → Nat) (height : Nat) (frame : List Binding) (nextOwners : List Nat)
    (sources : VisibleSources d (source ++ [Parents.label d source coordinates])
      (visible ++ [state.length]) nextOwners (emit state u height 0 frame))
    (added : FrameMaterials d (source ++ [Parents.label d source coordinates])
      (visible ++ [state.length]) (materials ++ [hs]) frame) :
    VisibleMaterials d (source ++ [Parents.label d source coordinates])
      (visible ++ [state.length]) nextOwners (materials ++ [hs]) (emit state u height 0 frame) := by
  refine ⟨sources, known.materialContext.append coordinates hs width legal, ?_⟩
  intro i inside
  by_cases old : i < source.length
  · obtain ⟨col, lookup, payload⟩ := known.frames i old
    refine ⟨col, ?_, payload.append known.sources.length known.materialContext.length _ state.length hs⟩
    rw [Parents.point_append_old visible i state.length (by rw [known.sources.length]; exact old)]
    have bound := (List.getElem?_eq_some_iff.mp lookup).choose
    simpa only [emit, List.getElem?_append_left bound] using lookup
  · have same : i = source.length := by
      simp only [List.length_append, List.length_cons, List.length_nil] at inside
      omega
    subst i
    refine ⟨⟨row d u height 0, row_width d u height 0, frame⟩, ?_, added⟩
    rw [← known.sources.length, Parents.point_append_last]
    exact List.getElem?_concat_length

theorem VisibleMaterials.inherit_slot {d : Nat} {source : ParentContext}
    {coordinates visible owners : List Nat} {materials : List (Forests (List Nat))}
    {frame : List Binding} {state : State d}
    (known : VisibleMaterials d source visible owners materials state)
    (inherited : InheritedMaterials d source coordinates visible owners materials frame)
    (hs : Forests (List Nat)) (width : coordinates.length = d)
    (legal : Source.FiniteLegalForests d (source ++ [Parents.label d source coordinates])
      (coordinates[0]?.getD 0) hs) (u : Nat → Nat) (height : Nat) :
    VisibleMaterials d (source ++ [Parents.label d source coordinates]) (visible ++ [state.length])
      (owners ++ [source.length]) (materials ++ [hs]) (emit state u height 0 frame) :=
  known.append_emit coordinates hs width legal u height frame (owners ++ [source.length])
    (known.sources.inherit_slot inherited.sources u height)
    (inherited.keys.append known.sources.length known.materialContext.length _ state.length hs)

theorem VisibleMaterials.save_latest {d : Nat} {source : ParentContext}
    {coordinates visible owners : List Nat} {materials : List (Forests (List Nat))}
    {frame : List Binding} {state : State d}
    (known : VisibleMaterials d source visible owners materials state)
    (inherited : InheritedMaterials d source coordinates visible owners materials frame)
    (hs : Forests (List Nat)) (width : coordinates.length = d)
    (legal : Source.FiniteLegalForests d (source ++ [Parents.label d source coordinates])
      (coordinates[0]?.getD 0) hs) (u : Nat → Nat) (height : Nat) (b : Binding)
    (latest : b.latest = some state.length)
    (key : b.key = Keys.ofColumn d source.length (Parents.label d source coordinates)
      (Parents.annotateForests d (source ++ [Parents.label d source coordinates]) hs)) :
    VisibleMaterials d (source ++ [Parents.label d source coordinates]) (visible ++ [state.length])
      owners (materials ++ [hs]) (emit state u height 0 (frame ++ [b])) := by
  apply known.append_emit coordinates hs width legal u height (frame ++ [b]) owners
    (known.sources.save_latest inherited.sources u height b latest)
  intro x member
  rcases List.mem_append.mp member with old | new
  · exact inherited.keys.append known.sources.length known.materialContext.length _ state.length hs x old
  · have same : x = b := by simpa only [List.mem_singleton] using new
    subst x
    simp only [BindingMaterial, latest]
    refine ⟨source.length, by simp, ?_, ?_⟩
    · rw [← known.sources.length, Parents.point_append_last]
    · rw [← known.materialContext.length, List.getElem?_concat_length, Option.getD_some,
        known.materialContext.length, Keys.atContext_append]
      exact key

/-- Reused bindings are certified by the actual complete-key equality
test. Their material origin becomes the current source column, even
though their definition pointer remains the older one. -/
theorem headState_materials {d : Nat} {source : ParentContext} {visible owners : List Nat}
    {materials : List (Forests (List Nat))} {state : State d}
    (known : VisibleMaterials d source visible owners materials state)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (coordinates : List Nat) (hs : Forests (List Nat)) (width : coordinates.length = d)
    (legal : Source.FiniteLegalForests d (source ++ [Parents.label d source coordinates])
      (coordinates[0]?.getD 0) hs) :
    VisibleMaterials d (source ++ [Parents.label d source coordinates])
      (visible ++ [(headState d (Parents.label d source coordinates)
        (Parents.annotateForests d (source ++ [Parents.label d source coordinates]) hs)
        visible state).length - 1]) owners (materials ++ [hs])
      (headState d (Parents.label d source coordinates)
        (Parents.annotateForests d (source ++ [Parents.label d source coordinates]) hs) visible state) := by
  have inherited := queried_frame_inheritedMaterials known view coordinates
  have belowKnown := smaller_inheritedMaterials inherited
    (Keys.ofColumn d visible.length (Parents.label d source coordinates)
      (Parents.annotateForests d (source ++ [Parents.label d source coordinates]) hs))
  simp only [headState, encode]
  split
  next bound found =>
    have keyEq := Keys.compare_eq_imp _ _
      (by simpa only [beq_iff_eq] using List.find?_some found)
    have result := known.save_latest belowKnown hs width legal
      (vector state visible (Parents.label d source coordinates)) bound.height
      {bound with latest := some state.length} rfl (by simpa only [known.sources.length] using keyEq)
    simpa only [encode, emit_length, Nat.add_sub_cancel] using result
  next fresh =>
    let a := Parents.label d source coordinates
    let annotated := Parents.annotateForests d (source ++ [a]) hs
    let key := Keys.ofColumn d visible.length a annotated
    let below := smaller (frameAt state (representative visible a (d - 1))) key
    let c := (base below).height
    let u := vector state visible a
    let guarded := emit (emit state u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 []
    let forests := encodeForests d annotated visible u c below guarded
    have extended : state <+: forests := (emit_extends ..).trans
      ((emit_extends ..).trans (encodeForests_extends d annotated visible u c below guarded))
    have result := (known.extends extended).save_latest belowKnown hs width legal
      (fun j => u j + 1) (c + 2) ⟨key, c + 2, some forests.length, some state.length⟩ rfl
      (by change Keys.ofColumn d visible.length a annotated = Keys.ofColumn d source.length a annotated
          rw [known.sources.length])
    simpa only [encode, emit_length, Nat.add_sub_cancel] using result

/-- Numerical provenance and payload provenance refer to the same unique
source index, because the real numerical view is strictly increasing. -/
theorem InheritedMaterials.origin {d : Nat} {source target : ParentContext}
    {coordinates visible owners : List Nat} {materials : List (Forests (List Nat))}
    {frame : List Binding} (known : InheritedMaterials d source coordinates visible owners materials frame)
    (view : Parents.NumericalView d source target visible)
    (b : Binding) (member : b ∈ frame) (p : Nat) (latest : b.latest = some p) :
    ∃ i, i < source.length ∧ i ∉ owners ∧ p = Parents.point visible i ∧
      Parents.Ancestor (source ++ [Parents.label d source coordinates]) (d - 1) i source.length ∧
      b.key = Keys.atContext d source i (materials[i]?.getD .nil) ∧
      (source[i]?.getD default).coordinates.length = d ∧
      Source.FiniteLegalForests d (source.take (i + 1)) (Parents.reading source 0 i)
        (materials[i]?.getD .nil) := by
  obtain ⟨i, inside, free, named, ancestry, unique⟩ :=
    inherited_source_unique known.sources view b member p latest
  have payload := known.keys b member
  simp only [BindingMaterial, latest] at payload
  obtain ⟨j, bounded, other, key⟩ := payload
  have same := unique j bounded other
  subst j
  exact ⟨i, inside, free, named, ancestry, key, known.materialContext.legal i inside⟩

end BTnSSBMS.Encoder
