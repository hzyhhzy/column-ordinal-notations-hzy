import BTnSSBMS.CoupledQuery

/-!
Preserve the paired real frames when a representative is saved. Both
reuse and fresh closing columns change the latest-material origin;
older bindings retain their original, separately transported materials.
-/
namespace BTnSSBMS.Encoder

theorem CoupledFrames.save_emit {d : Nat} {source target oldOutput : ParentContext}
    {moved visible nextVisible owners : List Nat} {materials : List (Forests (List Nat))}
    {state next : State d} {below newBelow : List Binding}
    (related : CoupledFrames d source target moved visible nextVisible materials state next)
    (known : VisibleMaterials d source visible owners materials state)
    (oldView : Parents.NumericalView d source oldOutput visible) (outputSize : oldOutput.length ≤ state.length)
    (view : Parents.NumericalView d source target moved) (newLength : nextVisible.length = target.length)
    (belowKnown : FrameMaterials d source visible materials below)
    (belowRelated : KeyFrameRel (fun b => (rekeyBinding d source target visible moved materials b).key) below newBelow)
    (a newA : ParentLabel) (hs : Forests (List Nat)) (u v : Nat → Nat) (b newB : Binding)
    (latest : b.latest = some state.length) (height : newB.height = b.height)
    (key : newB.key = Keys.atContext d (target ++ [newA]) target.length
      (Source.relocateForests d (source ++ [a]) (target ++ [newA]) (moved ++ [target.length]) hs)) :
    CoupledFrames d (source ++ [a]) (target ++ [newA]) (moved ++ [target.length])
      (visible ++ [state.length]) (nextVisible ++ [next.length]) (materials ++ [hs])
      (emit state u b.height 0 (below ++ [b])) (emit next v newB.height 0 (newBelow ++ [newB])) := by
  have oldPairs := belowKnown.rekey_prefix oldView view known.materialContext.length
    (List.prefix_append source [a]) (List.prefix_append target [newA]) (List.prefix_append visible [state.length])
    (List.prefix_append moved [target.length]) (List.prefix_append materials [hs]) belowRelated
  have fresh : ∀ i, i < visible.length → Parents.point visible i < state.length := by
    intro i inside
    have bounded := oldView.bounded i (by rw [← oldView.length]; exact inside)
    omega
  have saved := rekeyBinding_new_latest oldView view known.materialContext.length a newA hs state.length fresh b latest
  exact related.append_emit known oldView view newLength a newA hs u v b.height newB.height _ _
    (oldPairs.append (.cons ⟨key.trans saved.symm, height⟩ .nil))

/-- In the reused-key branch this relates the two actual headState
results, including the newly saved binding. The new query is proved to
reuse; it is not supplied as a premise. -/
theorem CoupledFrames.reused_head {d : Nat} {source target : ParentContext}
    {coordinates visible nextVisible owners moved : List Nat} {materials : List (Forests (List Nat))}
    {state next : State d} {hs : Forests (List Nat)}
    (related : CoupledFrames d source target moved visible nextVisible materials state next)
    (known : VisibleMaterials d source visible owners materials state)
    (query : MaterialQuery d source coordinates visible owners materials state hs)
    (newView : Parents.NumericalView d target (BMS.parentTable (d + 2) (matrix next)) nextVisible)
    (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
    (targetUnit : Parents.UnitSteps d target) (view : Parents.NumericalView d source target moved)
    (targetWidth : ∀ i, i < target.length → (target[i]?.getD default).coordinates.length = d)
    (positive : 0 < d) (bound : Binding)
    (found : equal (frameAt state (representative visible (Parents.label d source coordinates) (d - 1)))
      (queryKey d source coordinates hs) = some bound) :
    let a := Parents.label d source coordinates
    let newCoordinates := Source.relocationHead d source target moved coordinates
    let newA := Parents.label d target newCoordinates
    let newHs := Source.relocateForests d (source ++ [a]) (target ++ [newA]) (moved ++ [target.length]) hs
    let headed := headState d a (Parents.annotateForests d (source ++ [a]) hs) visible state
    let newHeaded := headState d newA (Parents.annotateForests d (target ++ [newA]) newHs) nextVisible next
    CoupledFrames d (source ++ [a]) (target ++ [newA]) (moved ++ [target.length])
      (visible ++ [headed.length - 1]) (nextVisible ++ [newHeaded.length - 1]) (materials ++ [hs]) headed newHeaded := by
  let a := Parents.label d source coordinates
  let newCoordinates := Source.relocationHead d source target moved coordinates
  let newA := Parents.label d target newCoordinates
  let newHs := Source.relocateForests d (source ++ [a]) (target ++ [newA]) (moved ++ [target.length]) hs
  have tests := related.query_tests query newView targetCoherent targetValid targetUnit view targetWidth positive
  obtain ⟨newBound, newFound, pair⟩ := (show ∃ newBound,
      equal (frameAt next (representative nextVisible newA (d - 1)))
        (queryKey d target newCoordinates newHs) = some newBound ∧
      KeyBindingRel (fun b => (rekeyBinding d source target visible moved materials b).key) bound newBound from
    by simpa only [found] using tests.2.2)
  have newKey := Keys.compare_eq_imp _ _ (by simpa only [beq_iff_eq] using List.find?_some newFound)
  have result := related.save_emit known query.view (by simp only [BMS.parentTable_length, matrix, List.length_map]; exact Nat.le_refl _)
    view newView.length (smaller_inheritedMaterials query.inherited (queryKey d source coordinates hs)).keys tests.1
    a newA hs (vector state visible a) (vector next nextVisible newA)
    {bound with latest := some state.length} {newBound with latest := some next.length} rfl pair.2
    (by simpa only [newA, Keys.atContext_append, queryKey, newHs] using newKey)
  simp only [queryKey] at found newFound
  dsimp only [newA, newCoordinates, newHs, a] at newFound
  simp only [headState, encode, query.view.length, newView.length,
    found, newFound, emit_length, Nat.add_sub_cancel]
  exact result

/-- Fresh columns restore the entry frame when their forests close.
The inner computations may have different absolute lengths; their
actual output prefixes suffice to prove the closing-frame relation. -/
theorem CoupledFrames.fresh_head {d : Nat} {source target : ParentContext}
    {coordinates visible nextVisible owners moved : List Nat} {materials : List (Forests (List Nat))}
    {state next : State d} {hs : Forests (List Nat)}
    (related : CoupledFrames d source target moved visible nextVisible materials state next)
    (known : VisibleMaterials d source visible owners materials state)
    (query : MaterialQuery d source coordinates visible owners materials state hs)
    (newView : Parents.NumericalView d target (BMS.parentTable (d + 2) (matrix next)) nextVisible)
    (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
    (targetUnit : Parents.UnitSteps d target) (view : Parents.NumericalView d source target moved)
    (targetWidth : ∀ i, i < target.length → (target[i]?.getD default).coordinates.length = d)
    (positive : 0 < d)
    (fresh : equal (frameAt state (representative visible (Parents.label d source coordinates) (d - 1)))
      (queryKey d source coordinates hs) = none) :
    let a := Parents.label d source coordinates
    let newCoordinates := Source.relocationHead d source target moved coordinates
    let newA := Parents.label d target newCoordinates
    let newHs := Source.relocateForests d (source ++ [a]) (target ++ [newA]) (moved ++ [target.length]) hs
    let headed := headState d a (Parents.annotateForests d (source ++ [a]) hs) visible state
    let newHeaded := headState d newA (Parents.annotateForests d (target ++ [newA]) newHs) nextVisible next
    CoupledFrames d (source ++ [a]) (target ++ [newA]) (moved ++ [target.length])
      (visible ++ [headed.length - 1]) (nextVisible ++ [newHeaded.length - 1]) (materials ++ [hs]) headed newHeaded := by
  let a := Parents.label d source coordinates
  let newCoordinates := Source.relocationHead d source target moved coordinates
  let newA := Parents.label d target newCoordinates
  let newHs := Source.relocateForests d (source ++ [a]) (target ++ [newA]) (moved ++ [target.length]) hs
  let key := queryKey d source coordinates hs
  let newKey := queryKey d target newCoordinates newHs
  let below := smaller (frameAt state (representative visible a (d - 1))) key
  let newBelow := smaller (frameAt next (representative nextVisible newA (d - 1))) newKey
  let c := (base below).height
  let newC := (base newBelow).height
  let u := vector state visible a
  let v := vector next nextVisible newA
  let withGuard := emit (emit state u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 []
  let nextGuard := emit (emit next v (newC + 1) 1 []) (fun j => v j + 1) (newC + 2) 2 []
  let withForests := encodeForests d (Parents.annotateForests d (source ++ [a]) hs) visible u c below withGuard
  let nextForests := encodeForests d (Parents.annotateForests d (target ++ [newA]) newHs) nextVisible v newC newBelow nextGuard
  have oldExtended : state <+: withForests :=
    (emit_extends ..).trans ((emit_extends ..).trans (encodeForests_extends ..))
  have newExtended : next <+: nextForests :=
    (emit_extends ..).trans ((emit_extends ..).trans (encodeForests_extends ..))
  have tests := related.query_tests query newView targetCoherent targetValid targetUnit view targetWidth positive
  have newFresh : equal (frameAt next (representative nextVisible newA (d - 1))) newKey = none := by
    simpa only [fresh] using tests.2.2
  have heights : newC = c := tests.1.base_height
  have result := (related.extends oldExtended newExtended).save_emit (known.extends oldExtended) query.view
    (by simpa only [BMS.parentTable_length, matrix, List.length_map] using oldExtended.length_le)
    view newView.length (smaller_inheritedMaterials query.inherited key).keys tests.1
    a newA hs (fun j => u j + 1) (fun j => v j + 1)
    ⟨key, c + 2, some withForests.length, some state.length⟩
    ⟨newKey, newC + 2, some nextForests.length, some next.length⟩ rfl
    (congrArg (· + 2) heights) (by simp only [newKey, newA, Keys.atContext_append, queryKey, newHs])
  simp only [queryKey] at fresh
  dsimp only [newKey, queryKey, newA, newCoordinates, newHs, a] at newFresh
  simp only [headState, encode, query.view.length, newView.length,
    fresh, newFresh, emit_length, Nat.add_sub_cancel]
  exact result

theorem CoupledFrames.head {d : Nat} {source target : ParentContext}
    {coordinates visible nextVisible owners moved : List Nat} {materials : List (Forests (List Nat))}
    {state next : State d} {hs : Forests (List Nat)}
    (related : CoupledFrames d source target moved visible nextVisible materials state next)
    (known : VisibleMaterials d source visible owners materials state)
    (query : MaterialQuery d source coordinates visible owners materials state hs)
    (newView : Parents.NumericalView d target (BMS.parentTable (d + 2) (matrix next)) nextVisible)
    (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
    (targetUnit : Parents.UnitSteps d target) (view : Parents.NumericalView d source target moved)
    (targetWidth : ∀ i, i < target.length → (target[i]?.getD default).coordinates.length = d)
    (positive : 0 < d) :
    let a := Parents.label d source coordinates
    let newCoordinates := Source.relocationHead d source target moved coordinates
    let newA := Parents.label d target newCoordinates
    let newHs := Source.relocateForests d (source ++ [a]) (target ++ [newA]) (moved ++ [target.length]) hs
    let headed := headState d a (Parents.annotateForests d (source ++ [a]) hs) visible state
    let newHeaded := headState d newA (Parents.annotateForests d (target ++ [newA]) newHs) nextVisible next
    CoupledFrames d (source ++ [a]) (target ++ [newA]) (moved ++ [target.length])
      (visible ++ [headed.length - 1]) (nextVisible ++ [newHeaded.length - 1]) (materials ++ [hs]) headed newHeaded := by
  cases found : equal (frameAt state (representative visible (Parents.label d source coordinates) (d - 1)))
      (queryKey d source coordinates hs) with
  | none => exact related.fresh_head known query newView targetCoherent targetValid targetUnit view targetWidth positive found
  | some b => exact related.reused_head known query newView targetCoherent targetValid targetUnit view targetWidth positive b found

end BTnSSBMS.Encoder
