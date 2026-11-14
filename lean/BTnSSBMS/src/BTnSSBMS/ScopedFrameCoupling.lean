import BTnSSBMS.MaterialStability

/-!
Finite correspondence of real saved frames at paired source positions.
The states and their frames are the actual encoder states. Only key and
height fields are paired; absolute target pointers are not identified.
-/
namespace BTnSSBMS.Encoder

def CoupledFrames (d : Nat) (source target : ParentContext) (moved visible nextVisible : List Nat)
    (materials : List (Forests (List Nat))) (state next : State d) : Prop :=
  ∀ i, i < source.length → ∃ oldCol newCol,
    state[Parents.point visible i]? = some oldCol ∧
    next[Parents.point nextVisible (Parents.point moved i)]? = some newCol ∧
    KeyFrameRel (fun b => (rekeyBinding d source target visible moved materials b).key) oldCol.frame newCol.frame

theorem coupledFrames_empty (d : Nat) (target : ParentContext) (nextVisible : List Nat) (next : State d) :
    CoupledFrames d [] target [] [] nextVisible [] [] next := by
  intro i inside
  simp at inside

theorem CoupledFrames.extends {d : Nat} {source target : ParentContext} {moved visible nextVisible : List Nat}
    {materials : List (Forests (List Nat))} {state next state' next' : State d}
    (related : CoupledFrames d source target moved visible nextVisible materials state next)
    (oldExtended : state <+: state') (newExtended : next <+: next') :
    CoupledFrames d source target moved visible nextVisible materials state' next' := by
  intro i inside
  obtain ⟨a, b, oldLookup, newLookup, pair⟩ := related i inside
  obtain ⟨oldExtra, rfl⟩ := oldExtended
  obtain ⟨newExtra, rfl⟩ := newExtended
  exact ⟨a, b, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp oldLookup).choose]; exact oldLookup,
    by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp newLookup).choose]; exact newLookup, pair⟩

/-- Query the real target position obtained from the actual transported
parent search. This is not an arbitrary supplied target frame. -/
theorem CoupledFrames.queried {d : Nat} {source target : ParentContext} {moved visible nextVisible : List Nat}
    {materials : List (Forests (List Nat))} {state next : State d}
    (related : CoupledFrames d source target moved visible nextVisible materials state next)
    (oldView : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (newView : Parents.NumericalView d target (BMS.parentTable (d + 2) (matrix next)) nextVisible)
    (view : Parents.NumericalView d source target moved)
    (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
    (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
    (positive : 0 < d) (coordinates : List Nat) :
    KeyFrameRel (fun b => (rekeyBinding d source target visible moved materials b).key)
      (frameAt state (representative visible (Parents.label d source coordinates) (d - 1)))
      (frameAt next (representative nextVisible
        (Parents.label d target (Source.relocationHead d source target moved coordinates)) (d - 1))) := by
  rw [representative_eq_point oldView, representative_eq_point newView,
    Source.relocationHead_parents sourceCoherent sourceValid targetCoherent targetValid view coordinates
      (d - 1) (by omega)]
  cases parent : (Parents.label d source coordinates).parents[d - 1]?.join with
  | none =>
    simp only [Option.map_none, frameAt, Option.bind_none]
    exact KeyFrameRel.virtual rfl
  | some p =>
    have bound := Parents.label_parent_bound d source coordinates (d - 1) p parent
    obtain ⟨a, b, oldLookup, newLookup, pair⟩ := related p bound
    simpa only [Option.map_some, frameAt, Option.bind_some, oldLookup, newLookup] using pair

/-- Extending both numerical source contexts and emitting their real
new representatives preserves every older frame pair. The new pair is
checked separately, because saving it changes the latest-source origin. -/
theorem CoupledFrames.append_emit {d : Nat} {source target oldOutput : ParentContext}
    {moved visible nextVisible owners : List Nat} {materials : List (Forests (List Nat))}
    {state next : State d}
    (related : CoupledFrames d source target moved visible nextVisible materials state next)
    (known : VisibleMaterials d source visible owners materials state)
    (oldView : Parents.NumericalView d source oldOutput visible)
    (view : Parents.NumericalView d source target moved) (newLength : nextVisible.length = target.length)
    (a newA : ParentLabel) (hs : Forests (List Nat)) (u v : Nat → Nat)
    (height newHeight : Nat) (oldFrame newFrame : List Binding)
    (added : KeyFrameRel
      (fun b => (rekeyBinding d (source ++ [a]) (target ++ [newA]) (visible ++ [state.length])
        (moved ++ [target.length]) (materials ++ [hs]) b).key) oldFrame newFrame) :
    CoupledFrames d (source ++ [a]) (target ++ [newA]) (moved ++ [target.length])
      (visible ++ [state.length]) (nextVisible ++ [next.length]) (materials ++ [hs])
      (emit state u height 0 oldFrame) (emit next v newHeight 0 newFrame) := by
  intro i inside
  by_cases old : i < source.length
  · obtain ⟨oldCol, newCol, oldLookup, newLookup, pair⟩ := related i old
    obtain ⟨saved, savedLookup, payload⟩ := known.frames i old
    have same : saved = oldCol := Option.some.inj (savedLookup.symm.trans oldLookup)
    subst saved
    have newPair := payload.rekey_prefix oldView view known.materialContext.length
      (List.prefix_append source [a]) (List.prefix_append target [newA]) (List.prefix_append visible [state.length])
      (List.prefix_append moved [target.length]) (List.prefix_append materials [hs]) pair
    refine ⟨oldCol, newCol, ?_, ?_, newPair⟩
    · rw [Parents.point_append_old visible i state.length (by rw [oldView.length]; exact old),
        emit, List.getElem?_append_left (List.getElem?_eq_some_iff.mp oldLookup).choose]
      exact oldLookup
    · rw [Parents.point_append_old moved i target.length (by rw [view.length]; exact old),
        Parents.point_append_old nextVisible (Parents.point moved i) next.length
          (by rw [newLength]; exact view.bounded i old),
        emit, List.getElem?_append_left (List.getElem?_eq_some_iff.mp newLookup).choose]
      exact newLookup
  · have same : i = source.length := by
      simp only [List.length_append, List.length_cons, List.length_nil] at inside
      omega
    subst i
    refine ⟨⟨row d u height 0, row_width d u height 0, oldFrame⟩,
      ⟨row d v newHeight 0, row_width d v newHeight 0, newFrame⟩, ?_, ?_, added⟩
    · rw [← oldView.length, Parents.point_append_last]
      exact List.getElem?_concat_length
    · rw [← view.length, Parents.point_append_last, ← newLength, Parents.point_append_last]
      exact List.getElem?_concat_length

end BTnSSBMS.Encoder
