import BTnSSBMS.RootedSaving

namespace BTnSSBMS.Encoder

/-- Extending both numerical source contexts and emitting their real
new representatives preserves every older frame pair. The new pair is
checked separately, because saving it changes the latest-source origin. -/
theorem RootedFrames.append_emit {root d : Nat} {source target oldOutput : ParentContext}
    {moved visible nextVisible owners : List Nat} {materials : List (Forests (List Nat))}
    {state next : State d} {pool : List Key}
    (related : RootedFrames root d source target moved visible nextVisible materials pool state next)
    (known : VisibleMaterials d source visible owners materials state)
    (oldView : Parents.NumericalView d source oldOutput visible)
    (view : Parents.NumericalView d source target moved) (newLength : nextVisible.length = target.length)
    (a newA : ParentLabel) (hs : Forests (List Nat)) (u v : Nat → Nat)
    (height newHeight : Nat) (oldFrame newFrame : List Binding)
    (added : RootedInsertion root
      (fun b => (rekeyBinding d (source ++ [a]) (target ++ [newA]) (visible ++ [state.length])
        (moved ++ [target.length]) (materials ++ [hs]) b).key) oldFrame newFrame pool) :
    RootedFrames root d (source ++ [a]) (target ++ [newA]) (moved ++ [target.length])
      (visible ++ [state.length]) (nextVisible ++ [next.length]) (materials ++ [hs]) pool
      (emit state u height 0 oldFrame) (emit next v newHeight 0 newFrame) := by
  intro i inside
  by_cases old : i < source.length
  · obtain ⟨oldCol, newCol, oldLookup, newLookup, ⟨pair⟩⟩ := related i old
    obtain ⟨saved, savedLookup, payload⟩ := known.frames i old
    have same : saved = oldCol := Option.some.inj (savedLookup.symm.trans oldLookup)
    subst saved
    have newPair := pair.congr (fun b member => congrArg Binding.key
      (rekeyBinding_prefix oldView view known.materialContext.length
        (List.prefix_append source [a]) (List.prefix_append target [newA]) (List.prefix_append visible [state.length])
        (List.prefix_append moved [target.length]) (List.prefix_append materials [hs]) b (payload b member)))
    refine ⟨oldCol, newCol, ?_, ?_, ⟨newPair⟩⟩
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
      ⟨row d v newHeight 0, row_width d v newHeight 0, newFrame⟩, ?_, ?_, ⟨added⟩⟩
    · rw [← oldView.length, Parents.point_append_last]
      exact List.getElem?_concat_length
    · rw [← view.length, Parents.point_append_last, ← newLength, Parents.point_append_last]
      exact List.getElem?_concat_length

/-- Every forest slot uses the owner's filtered entering frame, not a
frame left by a preceding sibling. The intervening real output may be
arbitrarily long and need not have equal lengths in the two executions. -/
theorem RootedFrames.filtered_slot {root d : Nat} {source target : ParentContext}
    {coordinates visible nextVisible owners moved : List Nat} {materials : List (Forests (List Nat))}
    {original newOriginal state next : State d} {hs : Forests (List Nat)} {pool : List Key}
    (related : RootedFrames root d source target moved visible nextVisible materials pool original newOriginal)
    (known : VisibleMaterials d source visible owners materials original)
    (query : MaterialQuery d source coordinates visible owners materials original hs)
    (newView : Parents.NumericalView d target (BMS.parentTable (d + 2) (matrix newOriginal)) nextVisible)
    (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
    (targetUnit : Parents.UnitSteps d target) (view : Parents.NumericalView d source target moved)
    (targetWidth : ∀ i, i < target.length → (target[i]?.getD default).coordinates.length = d)
    (positive : 0 < d) (oldExtended : original <+: state) (newExtended : newOriginal <+: next)
    (u v : Nat → Nat) :
    let a := Parents.label d source coordinates
    let newCoordinates := Source.relocationHead d source target moved coordinates
    let newA := Parents.label d target newCoordinates
    let newHs := Source.relocateForests d (source ++ [a]) (target ++ [newA]) (moved ++ [target.length]) hs
    let below := smaller (frameAt original (representative visible a (d - 1))) (queryKey d source coordinates hs)
    let newBelow := smaller (frameAt newOriginal (representative nextVisible newA (d - 1)))
      (queryKey d target newCoordinates newHs)
    RootedFrames root d (source ++ [a]) (target ++ [newA]) (moved ++ [target.length])
      (visible ++ [state.length]) (nextVisible ++ [next.length]) (materials ++ [hs]) pool
      (emit state (fun j => u j + 2) ((base below).height + 2) 0 below)
      (emit next (fun j => v j + 2) ((base newBelow).height + 2) 0 newBelow) := by
  dsimp only
  obtain ⟨splice⟩ := related.queried query.view newView view query.coherent query.valid
    targetCoherent targetValid positive coordinates
  have comparisons := query.relocation_comparisons targetCoherent targetValid targetUnit view targetWidth positive
  have filtered := splice.filtered (queryKey d source coordinates hs) _ comparisons
  have retainedMaterials := smaller_inheritedMaterials query.inherited (queryKey d source coordinates hs)
  have shifted := filtered.congr (fun b member => congrArg Binding.key
    (rekeyBinding_prefix query.view view query.inherited.materialContext.length
      (List.prefix_append source [Parents.label d source coordinates])
      (List.prefix_append target [Parents.label d target (Source.relocationHead d source target moved coordinates)])
      (List.prefix_append visible [state.length]) (List.prefix_append moved [target.length])
      (List.prefix_append materials [hs]) b (retainedMaterials.keys b member)))
  exact (related.extends oldExtended newExtended).append_emit (known.extends oldExtended)
    query.view view newView.length _ _ hs _ _ _ _ _ _ shifted

end BTnSSBMS.Encoder
