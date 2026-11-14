import BTnSSBMS.EncoderHeadState

/-!
Source provenance of saved latest pointers. Open forest owners are source
positions in the current lexical scope, not target positions. A saved
pointer must name a visible non-owner on the highest numerical ancestor
chain. No inverse to the source-to-target numerical view is assumed.
-/
namespace BTnSSBMS.Encoder

def FrameSources (d : Nat) (source : ParentContext) (visible owners : List Nat)
    (position : Nat) (frame : List Binding) : Prop :=
  ∀ b ∈ frame, ∀ p, b.latest = some p →
    ∃ i, i < source.length ∧ i ∉ owners ∧ p = Parents.point visible i ∧
      Parents.Ancestor source (d - 1) i position

structure VisibleSources (d : Nat) (source : ParentContext) (visible owners : List Nat)
    (state : State d) : Prop where
  length : visible.length = source.length
  ownersBound : ∀ i ∈ owners, i < source.length
  frames : ∀ i, i < source.length → ∃ col,
    state[Parents.point visible i]? = some col ∧
      FrameSources d source visible owners i col.frame

/-- Strictly older source origins of a frame read at a new column. -/
def InheritedSources (d : Nat) (source : ParentContext) (coordinates : List Nat)
    (visible owners : List Nat) (frame : List Binding) : Prop :=
  ∀ b ∈ frame, ∀ p, b.latest = some p →
    ∃ i, i < source.length ∧ i ∉ owners ∧ p = Parents.point visible i ∧
      Parents.Ancestor (source ++ [Parents.label d source coordinates]) (d - 1) i source.length

theorem empty_visibleSources (d : Nat) : VisibleSources d [] [] [] [] := by
  refine ⟨rfl, ?_, ?_⟩
  · intro i member; simp at member
  · intro i bound; simp at bound

theorem VisibleSources.extends {d : Nat} {source : ParentContext}
    {visible owners : List Nat} {state next : State d}
    (sources : VisibleSources d source visible owners state) (extended : state <+: next) :
    VisibleSources d source visible owners next := by
  refine ⟨sources.length, sources.ownersBound, ?_⟩
  intro i inside
  obtain ⟨col, lookup, provenance⟩ := sources.frames i inside
  obtain ⟨extra, rfl⟩ := extended
  have bounded := (List.getElem?_eq_some_iff.mp lookup).choose
  exact ⟨col, by rw [List.getElem?_append_left bounded]; exact lookup, provenance⟩

theorem FrameSources.append {d : Nat} {source : ParentContext}
    {visible owners : List Nat} {position : Nat} {frame : List Binding}
    (provenance : FrameSources d source visible owners position frame)
    (length : visible.length = source.length) (a : ParentLabel) (point : Nat)
    (nextOwners : List Nat)
    (keep : ∀ i, i < source.length → i ∉ owners → i ∉ nextOwners) :
    FrameSources d (source ++ [a]) (visible ++ [point]) nextOwners position frame := by
  intro b member p found
  obtain ⟨i, inside, free, named, ancestry⟩ := provenance b member p found
  refine ⟨i, by simp only [List.length_append, List.length_cons, List.length_nil]; omega,
    keep i inside free, ?_, ancestry.prefix (List.prefix_append _ _)⟩
  rw [Parents.point_append_old visible i point (by rw [length]; exact inside)]
  exact named

theorem VisibleSources.append_emit {d : Nat} {source : ParentContext}
    {visible owners : List Nat} {state : State d}
    (sources : VisibleSources d source visible owners state)
    (a : ParentLabel) (u : Nat → Nat) (height tag : Nat) (frame : List Binding)
    (nextOwners : List Nat)
    (ownersBound : ∀ i ∈ nextOwners, i < source.length + 1)
    (keep : ∀ i, i < source.length → i ∉ owners → i ∉ nextOwners)
    (added : FrameSources d (source ++ [a]) (visible ++ [state.length]) nextOwners
      source.length frame) :
    VisibleSources d (source ++ [a]) (visible ++ [state.length]) nextOwners
      (emit state u height tag frame) := by
  refine ⟨by simp only [List.length_append, List.length_cons, List.length_nil, sources.length],
    by simpa only [List.length_append, List.length_cons, List.length_nil] using ownersBound, ?_⟩
  intro i bound
  by_cases old : i < source.length
  · obtain ⟨col, lookup, provenance⟩ := sources.frames i old
    refine ⟨col, ?_, provenance.append sources.length a state.length nextOwners keep⟩
    rw [Parents.point_append_old visible i state.length (by rw [sources.length]; exact old)]
    have bounded := (List.getElem?_eq_some_iff.mp lookup).choose
    simpa only [emit, List.getElem?_append_left bounded] using lookup
  · have same : i = source.length := by
      simp only [List.length_append, List.length_cons, List.length_nil] at bound
      omega
    subst i
    refine ⟨⟨row d u height tag, row_width d u height tag, frame⟩, ?_, added⟩
    rw [← sources.length, Parents.point_append_last]
    exact List.getElem?_concat_length

theorem virtual_frame_inheritedSources (d : Nat) (source : ParentContext)
    (coordinates : List Nat) (visible owners : List Nat) :
    InheritedSources d source coordinates visible owners virtualFrame := by
  intro b member p found
  have same : b = zeroBinding := by simpa only [virtualFrame, List.mem_singleton] using member
  simp only [same, zeroBinding] at found
  cases found

theorem queried_frame_inheritedSources {d : Nat} {source : ParentContext}
    {visible owners : List Nat} {state : State d}
    (sources : VisibleSources d source visible owners state)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (coordinates : List Nat) :
    InheritedSources d source coordinates visible owners
      (frameAt state (representative visible (Parents.label d source coordinates) (d - 1))) := by
  rw [representative_eq_point view]
  cases selected : (Parents.label d source coordinates).parents[d - 1]?.join with
  | none =>
    simpa only [Option.map_none, frameAt, Option.bind_none] using
      virtual_frame_inheritedSources d source coordinates visible owners
  | some parent =>
    have parentBound := Parents.label_parent_bound d source coordinates (d - 1) parent selected
    obtain ⟨col, lookup, provenance⟩ := sources.frames parent parentBound
    simp only [Option.map_some, frameAt, Option.bind_some, lookup]
    intro b member p found
    obtain ⟨i, inside, free, named, ancestry⟩ := provenance b member p found
    refine ⟨i, inside, free, named, .up ?_ (ancestry.prefix (List.prefix_append _ _))⟩
    simpa only [Parents.parent, List.getElem?_concat_length, Option.bind_some] using selected

theorem smaller_inheritedSources {d : Nat} {source : ParentContext}
    {coordinates visible owners : List Nat} {frame : List Binding}
    (inherited : InheritedSources d source coordinates visible owners frame) (key : Key) :
    InheritedSources d source coordinates visible owners (smaller frame key) :=
  fun b member p found => inherited b (List.mem_filter.mp member).1 p found

theorem InheritedSources.append {d : Nat} {source : ParentContext}
    {coordinates visible owners : List Nat} {frame : List Binding}
    (inherited : InheritedSources d source coordinates visible owners frame)
    (length : visible.length = source.length) (point : Nat) (nextOwners : List Nat)
    (keep : ∀ i, i < source.length → i ∉ owners → i ∉ nextOwners) :
    FrameSources d (source ++ [Parents.label d source coordinates]) (visible ++ [point])
      nextOwners source.length frame := by
  intro b member p found
  obtain ⟨i, inside, free, named, ancestry⟩ := inherited b member p found
  refine ⟨i, by simp only [List.length_append, List.length_cons, List.length_nil]; omega,
    keep i inside free, ?_, ancestry⟩
  rw [Parents.point_append_old visible i point (by rw [length]; exact inside)]
  exact named

theorem InheritedSources.updated {d : Nat} {source : ParentContext}
    {coordinates visible owners : List Nat} {frame : List Binding}
    (inherited : InheritedSources d source coordinates visible owners frame)
    (length : visible.length = source.length)
    (ownersBound : ∀ i ∈ owners, i < source.length)
    (point : Nat) (b : Binding) (latest : b.latest = some point) :
    FrameSources d (source ++ [Parents.label d source coordinates]) (visible ++ [point])
      owners source.length (frame ++ [b]) := by
  intro x member p found
  rcases List.mem_append.mp member with old | new
  · exact inherited.append length point owners (fun _ _ free => free) x old p found
  · have same : x = b := by simpa only [List.mem_singleton] using new
    subst x
    have atEnd : p = point := Option.some.inj (found.symm.trans latest)
    refine ⟨source.length, by simp, ?_, ?_, .refl _⟩
    · intro member
      have impossible := ownersBound source.length member
      omega
    · rw [← length, Parents.point_append_last]
      exact atEnd

theorem VisibleSources.inherit_slot {d : Nat} {source : ParentContext}
    {coordinates visible owners : List Nat} {frame : List Binding} {state : State d}
    (sources : VisibleSources d source visible owners state)
    (inherited : InheritedSources d source coordinates visible owners frame)
    (u : Nat → Nat) (height : Nat) :
    VisibleSources d (source ++ [Parents.label d source coordinates]) (visible ++ [state.length])
      (owners ++ [source.length]) (emit state u height 0 frame) := by
  have keep : ∀ i, i < source.length → i ∉ owners → i ∉ owners ++ [source.length] := by
    intro i inside free member
    rcases List.mem_append.mp member with old | new
    · exact free old
    · have same : i = source.length := by simpa only [List.mem_singleton] using new
      omega
  apply sources.append_emit _ u height 0 frame (owners ++ [source.length])
  · intro i member
    rcases List.mem_append.mp member with old | new
    · have bound := sources.ownersBound i old
      omega
    · have same : i = source.length := by simpa only [List.mem_singleton] using new
      omega
  · exact keep
  · exact inherited.append sources.length state.length (owners ++ [source.length]) keep

theorem VisibleSources.save_latest {d : Nat} {source : ParentContext}
    {coordinates visible owners : List Nat} {frame : List Binding} {state : State d}
    (sources : VisibleSources d source visible owners state)
    (inherited : InheritedSources d source coordinates visible owners frame)
    (u : Nat → Nat) (height : Nat) (b : Binding) (latest : b.latest = some state.length) :
    VisibleSources d (source ++ [Parents.label d source coordinates]) (visible ++ [state.length])
      owners (emit state u height 0 (frame ++ [b])) := by
  apply sources.append_emit _ u height 0 (frame ++ [b]) owners
  · intro i member
    have bound := sources.ownersBound i member
    omega
  · exact fun _ _ free => free
  · exact inherited.updated sources.length sources.ownersBound state.length b latest

/-- A completed source column saves its own binding only after restoring
the outer scope. Entries created inside its forests do not leak out. -/
theorem headState_sources {d : Nat} {source : ParentContext} {visible owners : List Nat}
    {state : State d} (sources : VisibleSources d source visible owners state)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (coordinates : List Nat) (hs : Forests (List Nat)) :
    VisibleSources d (source ++ [Parents.label d source coordinates])
      (visible ++ [(headState d (Parents.label d source coordinates)
        (Parents.annotateForests d (source ++ [Parents.label d source coordinates]) hs)
        visible state).length - 1]) owners
      (headState d (Parents.label d source coordinates)
        (Parents.annotateForests d (source ++ [Parents.label d source coordinates]) hs)
        visible state) := by
  have inherited := queried_frame_inheritedSources sources view coordinates
  have belowSources := smaller_inheritedSources inherited
    (Keys.ofColumn d visible.length (Parents.label d source coordinates)
      (Parents.annotateForests d (source ++ [Parents.label d source coordinates]) hs))
  simp only [headState, encode]
  split
  next bound found =>
    simpa only [encode, emit_length, Nat.add_sub_cancel] using
      sources.save_latest belowSources (vector state visible (Parents.label d source coordinates))
        bound.height {bound with latest := some state.length} rfl
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
    simpa only [encode, emit_length, Nat.add_sub_cancel] using
      (sources.extends extended).save_latest belowSources (fun j => u j + 1) (c + 2)
        ⟨key, c + 2, some forests.length, some state.length⟩ rfl

/-- The source origin is unique in the active scope. Target ancestry is
not used backwards to recover this origin. -/
theorem inherited_source_unique {d : Nat} {source target : ParentContext}
    {coordinates visible owners : List Nat} {frame : List Binding}
    (inherited : InheritedSources d source coordinates visible owners frame)
    (view : Parents.NumericalView d source target visible)
    (b : Binding) (member : b ∈ frame) (p : Nat) (found : b.latest = some p) :
    ∃ i, i < source.length ∧ i ∉ owners ∧ p = Parents.point visible i ∧
      Parents.Ancestor (source ++ [Parents.label d source coordinates]) (d - 1) i source.length ∧
      ∀ j, j < source.length → p = Parents.point visible j → j = i := by
  obtain ⟨i, inside, free, named, ancestry⟩ := inherited b member p found
  refine ⟨i, inside, free, named, ancestry, ?_⟩
  intro j bounded other
  by_cases left : j < i
  · have ordered := view.increasing j i left inside
    omega
  · by_cases right : i < j
    · have ordered := view.increasing i j right bounded
      omega
    · omega

end BTnSSBMS.Encoder
