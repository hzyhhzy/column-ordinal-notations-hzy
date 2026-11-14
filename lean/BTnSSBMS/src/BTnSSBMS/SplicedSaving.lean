import BTnSSBMS.SplicedFrames
import BTnSSBMS.InsertionHead
import BTnSSBMS.EntryOrigins

/-!
Save the insertion relation after actual complete heads. The two
executions may choose different fresh/reuse branches or emit different
amounts of forest material. Closing-frame restoration is still exact.
This is not a comparison of those intervening output columns.
-/
namespace BTnSSBMS.Encoder

theorem headFrame_split (d : Nat) (a : ParentLabel) (hs : Forests ParentLabel)
    (visible : List Nat) (state : State d) :
    ∃ binding,
      headFrame d a hs visible state =
        smaller (frameAt state (representative visible a (d - 1))) (Keys.ofColumn d visible.length a hs) ++ [binding] ∧
      binding.key = Keys.ofColumn d visible.length a hs ∧
      binding.latest = some ((headState d a hs visible state).length - 1) := by
  simp only [headFrame, headState, encode]
  split
  next bound found =>
    have keyEq : bound.key = Keys.ofColumn d visible.length a hs :=
      Keys.compare_eq_imp _ _ (by simpa only [beq_iff_eq] using List.find?_some found)
    simp only [emit_length, Nat.add_sub_cancel]
    simp only [frameAt, Option.bind_some, emit, List.getElem?_concat_length]
    exact ⟨{bound with latest := some state.length}, rfl, keyEq, rfl⟩
  next fresh =>
    simp only [emit_length, Nat.add_sub_cancel]
    simp only [frameAt, Option.bind_some, emit, List.getElem?_concat_length]
    exact ⟨_, rfl, rfl, rfl⟩

theorem MaterialQuery.headFrame_splice {d : Nat} {source target : ParentContext}
    {coordinates visible nextVisible owners moved : List Nat} {materials : List (Forests (List Nat))}
    {state next : State d} {hs : Forests (List Nat)} {pool : List Key}
    (query : MaterialQuery d source coordinates visible owners materials state hs)
    (newLength : nextVisible.length = target.length)
    (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
    (targetUnit : Parents.UnitSteps d target) (view : Parents.NumericalView d source target moved)
    (targetWidth : ∀ i, i < target.length → (target[i]?.getD default).coordinates.length = d)
    (positive : 0 < d) :
    let a := Parents.label d source coordinates
    let newCoordinates := Source.relocationHead d source target moved coordinates
    let newA := Parents.label d target newCoordinates
    let newHs := Source.relocateForests d (source ++ [a]) (target ++ [newA]) (moved ++ [target.length]) hs
    let annotated := Parents.annotateForests d (source ++ [a]) hs
    let newAnnotated := Parents.annotateForests d (target ++ [newA]) newHs
    let headed := headState d a annotated visible state
    ∀ _splice : RekeyedInsertion (fun b => (rekeyBinding d source target visible moved materials b).key)
      (frameAt state (representative visible a (d - 1)))
      (frameAt next (representative nextVisible newA (d - 1))) pool,
    Nonempty (RekeyedInsertion
      (fun b => (rekeyBinding d (source ++ [a]) (target ++ [newA]) (visible ++ [headed.length - 1])
        (moved ++ [target.length]) (materials ++ [hs]) b).key)
      (headFrame d a annotated visible state) (headFrame d newA newAnnotated nextVisible next) pool) := by
  dsimp only
  intro splice
  let a := Parents.label d source coordinates
  let newCoordinates := Source.relocationHead d source target moved coordinates
  let newA := Parents.label d target newCoordinates
  let newHs := Source.relocateForests d (source ++ [a]) (target ++ [newA]) (moved ++ [target.length]) hs
  let annotated := Parents.annotateForests d (source ++ [a]) hs
  let newAnnotated := Parents.annotateForests d (target ++ [newA]) newHs
  let headed := headState d a annotated visible state
  let key := queryKey d source coordinates hs
  let newKey := queryKey d target newCoordinates newHs
  obtain ⟨oldBinding, oldShape, _, oldLatest⟩ := headFrame_split d a annotated visible state
  obtain ⟨newBinding, newShape, newSaved, _⟩ := headFrame_split d newA newAnnotated nextVisible next
  have comparisons := query.relocation_comparisons targetCoherent targetValid targetUnit view targetWidth positive
  have stable : ∀ b ∈ smaller (frameAt state (representative visible a (d - 1))) key,
      (rekeyBinding d (source ++ [a]) (target ++ [newA]) (visible ++ [headed.length - 1])
        (moved ++ [target.length]) (materials ++ [hs]) b).key =
      (rekeyBinding d source target visible moved materials b).key := by
    intro b member
    exact congrArg Binding.key (rekeyBinding_prefix query.view view query.inherited.materialContext.length
      (List.prefix_append source [a]) (List.prefix_append target [newA])
      (List.prefix_append visible [headed.length - 1]) (List.prefix_append moved [target.length])
      (List.prefix_append materials [hs]) b ((smaller_inheritedMaterials query.inherited key).keys b member))
  have fresh : ∀ i, i < visible.length → Parents.point visible i < headed.length - 1 := by
    intro i inside
    have bounded := query.view.bounded i (by rw [← query.view.length]; exact inside)
    have before := headState_first_before_last d a annotated visible state
    change state.length ≤ headed.length - 1 at before
    simp only [BMS.parentTable_length, matrix, List.length_map] at bounded
    omega
  have savedKey := rekeyBinding_new_latest query.view view query.inherited.materialContext.length
    a newA hs (headed.length - 1) fresh oldBinding oldLatest
  have oldSaved : (rekeyBinding d (source ++ [a]) (target ++ [newA]) (visible ++ [headed.length - 1])
      (moved ++ [target.length]) (materials ++ [hs]) oldBinding).key = newKey := by
    simpa only [newKey, newA, newHs, Keys.atContext_append, queryKey] using savedKey
  have newSaved' : newBinding.key = newKey := by
    simpa only [newLength, newKey, newA, newAnnotated, queryKey] using newSaved
  have saved := splice.saved key newKey comparisons stable oldBinding newBinding oldSaved newSaved'
  rw [oldShape, newShape]
  simpa only [query.view.length, newLength, key, newKey, queryKey, a, newA, annotated, newAnnotated] using
    (show Nonempty _ from ⟨saved⟩)

theorem SplicedFrames.head {d : Nat} {source target : ParentContext}
    {coordinates visible nextVisible owners moved : List Nat} {materials : List (Forests (List Nat))}
    {state next : State d} {hs : Forests (List Nat)} {pool : List Key}
    (related : SplicedFrames d source target moved visible nextVisible materials pool state next)
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
    SplicedFrames d (source ++ [a]) (target ++ [newA]) (moved ++ [target.length])
      (visible ++ [headed.length - 1]) (nextVisible ++ [newHeaded.length - 1]) (materials ++ [hs]) pool headed newHeaded := by
  dsimp only
  obtain ⟨splice⟩ := related.queried query.view newView view query.coherent query.valid
    targetCoherent targetValid positive coordinates
  have added := query.headFrame_splice newView.length targetCoherent targetValid targetUnit view targetWidth positive splice
  apply related.append_states known query.view view newView.length
    (encode_extends ..) (encode_extends ..) _ _ hs _ _
  · exact Nat.sub_lt (headState_nonempty ..) (by decide)
  · exact Nat.sub_lt (headState_nonempty ..) (by decide)
  · exact added

end BTnSSBMS.Encoder
