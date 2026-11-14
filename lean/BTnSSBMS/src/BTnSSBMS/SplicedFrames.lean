import BTnSSBMS.KeySplice
import BTnSSBMS.ScopedFrameCoupling

/-!
An insertion relation at every paired visible source position. A query
inherits the particular frame at its real highest numerical parent, not
the frame most recently seen in a global traversal. A fixed pool bounds
unmatched keys, while each position may retain a different sublist.
-/
namespace BTnSSBMS.Encoder

def SplicedFrames (d : Nat) (source target : ParentContext) (moved visible nextVisible : List Nat)
    (materials : List (Forests (List Nat))) (pool : List Key) (state next : State d) : Prop :=
  ∀ i, i < source.length → ∃ oldCol newCol,
    state[Parents.point visible i]? = some oldCol ∧
    next[Parents.point nextVisible (Parents.point moved i)]? = some newCol ∧
    Nonempty (RekeyedInsertion (fun b => (rekeyBinding d source target visible moved materials b).key)
      oldCol.frame newCol.frame pool)

theorem SplicedFrames.extends {d : Nat} {source target : ParentContext} {moved visible nextVisible : List Nat}
    {materials : List (Forests (List Nat))} {pool : List Key} {state next state' next' : State d}
    (related : SplicedFrames d source target moved visible nextVisible materials pool state next)
    (oldExtended : state <+: state') (newExtended : next <+: next') :
    SplicedFrames d source target moved visible nextVisible materials pool state' next' := by
  intro i inside
  obtain ⟨a, b, oldLookup, newLookup, pair⟩ := related i inside
  obtain ⟨oldExtra, rfl⟩ := oldExtended
  obtain ⟨newExtra, rfl⟩ := newExtended
  exact ⟨a, b, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp oldLookup).choose]; exact oldLookup,
    by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp newLookup).choose]; exact newLookup, pair⟩

theorem SplicedFrames.queried {d : Nat} {source target : ParentContext} {moved visible nextVisible : List Nat}
    {materials : List (Forests (List Nat))} {pool : List Key} {state next : State d}
    (related : SplicedFrames d source target moved visible nextVisible materials pool state next)
    (oldView : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (newView : Parents.NumericalView d target (BMS.parentTable (d + 2) (matrix next)) nextVisible)
    (view : Parents.NumericalView d source target moved)
    (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
    (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
    (positive : 0 < d) (coordinates : List Nat) :
    Nonempty (RekeyedInsertion (fun b => (rekeyBinding d source target visible moved materials b).key)
      (frameAt state (representative visible (Parents.label d source coordinates) (d - 1)))
      (frameAt next (representative nextVisible
        (Parents.label d target (Source.relocationHead d source target moved coordinates)) (d - 1))) pool) := by
  rw [representative_eq_point oldView, representative_eq_point newView,
    Source.relocationHead_parents sourceCoherent sourceValid targetCoherent targetValid view coordinates
      (d - 1) (by omega)]
  cases parent : (Parents.label d source coordinates).parents[d - 1]?.join with
  | none =>
    simp only [Option.map_none, frameAt, Option.bind_none]
    exact ⟨RekeyedInsertion.virtual _ pool rfl⟩
  | some p =>
    have bound := Parents.label_parent_bound d source coordinates (d - 1) p parent
    obtain ⟨a, b, oldLookup, newLookup, pair⟩ := related p bound
    simpa only [Option.map_some, frameAt, Option.bind_some, oldLookup, newLookup] using pair

/-- Save a new visible pair after arbitrary finite intervening output.
Older pairs retain their original materials and their original splice.
No equality of absolute output lengths is used. -/
theorem SplicedFrames.append_states {d : Nat} {source target : ParentContext}
    {moved visible nextVisible owners : List Nat} {materials : List (Forests (List Nat))}
    {pool : List Key} {state next state' next' : State d}
    (related : SplicedFrames d source target moved visible nextVisible materials pool state next)
    (known : VisibleMaterials d source visible owners materials state)
    (oldView : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (view : Parents.NumericalView d source target moved) (newLength : nextVisible.length = target.length)
    (oldExtended : state <+: state') (newExtended : next <+: next')
    (a newA : ParentLabel) (hs : Forests (List Nat)) (oldPoint newPoint : Nat)
    (oldInside : oldPoint < state'.length) (newInside : newPoint < next'.length)
    (added : Nonempty (RekeyedInsertion
      (fun b => (rekeyBinding d (source ++ [a]) (target ++ [newA]) (visible ++ [oldPoint])
        (moved ++ [target.length]) (materials ++ [hs]) b).key)
      (frameAt state' (some oldPoint)) (frameAt next' (some newPoint)) pool)) :
    SplicedFrames d (source ++ [a]) (target ++ [newA]) (moved ++ [target.length])
      (visible ++ [oldPoint]) (nextVisible ++ [newPoint]) (materials ++ [hs]) pool state' next' := by
  have extended := related.extends oldExtended newExtended
  intro i inside
  by_cases old : i < source.length
  · obtain ⟨oldCol, newCol, oldLookup, newLookup, ⟨pair⟩⟩ := extended i old
    obtain ⟨saved, savedLookup, payload⟩ := (known.extends oldExtended).frames i old
    have same : saved = oldCol := Option.some.inj (savedLookup.symm.trans oldLookup)
    subst saved
    have newPair := pair.congr (fun b member => congrArg Binding.key
      (rekeyBinding_prefix oldView view known.materialContext.length
        (List.prefix_append source [a]) (List.prefix_append target [newA])
        (List.prefix_append visible [oldPoint]) (List.prefix_append moved [target.length])
        (List.prefix_append materials [hs]) b (payload b member)))
    refine ⟨oldCol, newCol, ?_, ?_, ⟨newPair⟩⟩
    · rw [Parents.point_append_old visible i oldPoint (by rw [oldView.length]; exact old)]
      exact oldLookup
    · rw [Parents.point_append_old moved i target.length (by rw [view.length]; exact old),
        Parents.point_append_old nextVisible (Parents.point moved i) newPoint
          (by rw [newLength]; exact view.bounded i old)]
      exact newLookup
  · have same : i = source.length := by
      simp only [List.length_append, List.length_cons, List.length_nil] at inside
      omega
    subst i
    refine ⟨state'[oldPoint], next'[newPoint], ?_, ?_, ?_⟩
    · rw [← oldView.length, Parents.point_append_last, List.getElem?_eq_getElem oldInside]
    · rw [← view.length, Parents.point_append_last, ← newLength, Parents.point_append_last,
        List.getElem?_eq_getElem newInside]
    · simpa only [frameAt, Option.bind_some, List.getElem?_eq_getElem oldInside,
        List.getElem?_eq_getElem newInside] using added

end BTnSSBMS.Encoder
