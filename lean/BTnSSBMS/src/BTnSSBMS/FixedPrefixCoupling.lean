import BTnSSBMS.PartialRebaseQuery
import BTnSSBMS.ScopedFrameCoupling

/-!
Initialize the paired saved frames after a root appended to a longer
shared prefix. The pairing of all older frames is derived from their
real immutable columns and material, not assumed as an entry relation.
-/
namespace BTnSSBMS.Encoder

theorem fixed_prefix_root_emit {d : Nat} {source target oldOutput : ParentContext}
    {visible nextVisible owners : List Nat} {materials : List (Forests (List Nat))}
    {original state next : State d}
    (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
    (unit : Parents.UnitSteps d source) (initial : source <+: target)
    (known : VisibleMaterials d source visible owners materials original)
    (oldView : Parents.NumericalView d source oldOutput visible)
    (visiblePrefix : visible <+: nextVisible) (newLength : nextVisible.length = target.length)
    (oldExtended : original <+: state) (newExtended : original <+: next)
    (a newA : ParentLabel) (hs : Forests (List Nat)) (u v : Nat → Nat)
    (height newHeight : Nat) (oldFrame newFrame : List Binding)
    (added : KeyFrameRel
      (fun b => (rekeyBinding d (source ++ [a]) (target ++ [newA]) (visible ++ [state.length])
        (List.range source.length ++ [target.length]) (materials ++ [hs]) b).key) oldFrame newFrame) :
    CoupledFrames d (source ++ [a]) (target ++ [newA]) (List.range source.length ++ [target.length])
      (visible ++ [state.length]) (nextVisible ++ [next.length]) (materials ++ [hs])
      (emit state u height 0 oldFrame) (emit next v newHeight 0 newFrame) := by
  intro i inside
  by_cases old : i < source.length
  · obtain ⟨col, lookup, payload⟩ := known.frames i old
    have pair := payload.fixed_prefix coherent valid unit known.materialContext oldView
      (List.prefix_append source [a]) (initial.trans (List.prefix_append target [newA]))
      (List.prefix_append visible [state.length])
      (List.prefix_append (List.range source.length) [target.length]) (List.prefix_append materials [hs])
    have visibleInside : i < visible.length := by rw [oldView.length]; exact old
    have nextInside : i < nextVisible.length := by
      have bound := visiblePrefix.length_le
      omega
    have point : Parents.point nextVisible i = Parents.point visible i := by
      obtain ⟨extra, rfl⟩ := visiblePrefix
      simp only [Parents.point, List.getElem?_append_left visibleInside]
    have oldLookup : state[Parents.point visible i]? = some col := by
      obtain ⟨extra, rfl⟩ := oldExtended
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp lookup).choose]
      exact lookup
    have newLookup : next[Parents.point visible i]? = some col := by
      obtain ⟨extra, rfl⟩ := newExtended
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp lookup).choose]
      exact lookup
    refine ⟨col, col, ?_, ?_, pair⟩
    · rw [Parents.point_append_old visible i state.length visibleInside,
        emit, List.getElem?_append_left (List.getElem?_eq_some_iff.mp oldLookup).choose]
      exact oldLookup
    · rw [Parents.point_append_old (List.range source.length) i target.length (by simpa using old),
        Parents.point_range source.length i old,
        Parents.point_append_old nextVisible i next.length nextInside, point,
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
    · have last : Parents.point (List.range source.length ++ [target.length]) source.length = target.length := by
        simpa only [List.length_range] using Parents.point_append_last (List.range source.length) target.length
      rw [last, ← newLength, Parents.point_append_last]
      exact List.getElem?_concat_length

theorem fixed_prefix_save_emit {d : Nat} {source target oldOutput : ParentContext}
    {visible nextVisible owners : List Nat} {materials : List (Forests (List Nat))}
    {original state next : State d} {below : List Binding}
    (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
    (unit : Parents.UnitSteps d source) (initial : source <+: target)
    (known : VisibleMaterials d source visible owners materials original)
    (oldView : Parents.NumericalView d source oldOutput visible) (outputSize : oldOutput.length ≤ original.length)
    (visiblePrefix : visible <+: nextVisible) (newLength : nextVisible.length = target.length)
    (oldExtended : original <+: state) (newExtended : original <+: next)
    (belowKnown : FrameMaterials d source visible materials below)
    (a newA : ParentLabel) (hs : Forests (List Nat)) (u v : Nat → Nat) (b newB : Binding)
    (latest : b.latest = some state.length) (height : newB.height = b.height)
    (key : newB.key = Keys.atContext d (target ++ [newA]) target.length
      (Source.relocateForests d (source ++ [a]) (target ++ [newA]) (List.range source.length ++ [target.length]) hs)) :
    CoupledFrames d (source ++ [a]) (target ++ [newA]) (List.range source.length ++ [target.length])
      (visible ++ [state.length]) (nextVisible ++ [next.length]) (materials ++ [hs])
      (emit state u b.height 0 (below ++ [b])) (emit next v newB.height 0 (below ++ [newB])) := by
  have belowPair := belowKnown.fixed_prefix coherent valid unit known.materialContext oldView
    (List.prefix_append source [a]) (initial.trans (List.prefix_append target [newA]))
    (List.prefix_append visible [state.length])
    (List.prefix_append (List.range source.length) [target.length]) (List.prefix_append materials [hs])
  have fresh : ∀ i, i < visible.length → Parents.point visible i < state.length := by
    intro i inside
    have bounded := oldView.bounded i (by rw [← oldView.length]; exact inside)
    have size := oldExtended.length_le
    omega
  have saved := rekeyBinding_new_latest_of_length (target := target) (moved := List.range source.length) oldView (by simp)
    known.materialContext.length a newA hs state.length fresh b latest
  exact fixed_prefix_root_emit coherent valid unit initial known oldView visiblePrefix newLength
    oldExtended newExtended a newA hs u v b.height newB.height _ _
    (belowPair.append (.cons ⟨key.trans saved.symm, height⟩ .nil))

/-- Shared real root queries initialize the recursive correspondence
after either reuse or closing a fresh definition. Inner output lengths
need not be assumed equal, because all saved old frames are immutable. -/
theorem prefix_rebase_head_coupled {d : Nat} {source target : ParentContext}
    {visible nextVisible owners : List Nat} {materials : List (Forests (List Nat))}
    {state next : State d}
    (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
    (unit : Parents.UnitSteps d source) (initial : source <+: target)
    (known : VisibleMaterials d source visible owners materials state)
    (oldView : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (visiblePrefix : visible <+: nextVisible) (newLength : nextVisible.length = target.length)
    (statePrefix : state <+: next) (coordinates newCoordinates : List Nat) (hs : Forests (List Nat))
    (frameSame : frameAt next (representative nextVisible (Parents.label d target newCoordinates) (d - 1)) =
      frameAt state (representative visible (Parents.label d source coordinates) (d - 1)))
    (keySame : queryKey d target newCoordinates
      (Source.relocateForests d (source ++ [Parents.label d source coordinates])
        (target ++ [Parents.label d target newCoordinates]) (List.range source.length ++ [target.length]) hs) =
      queryKey d source coordinates hs) :
    let a := Parents.label d source coordinates
    let newA := Parents.label d target newCoordinates
    let newHs := Source.relocateForests d (source ++ [a]) (target ++ [newA]) (List.range source.length ++ [target.length]) hs
    let headed := headState d a (Parents.annotateForests d (source ++ [a]) hs) visible state
    let newHeaded := headState d newA (Parents.annotateForests d (target ++ [newA]) newHs) nextVisible next
    CoupledFrames d (source ++ [a]) (target ++ [newA]) (List.range source.length ++ [target.length])
      (visible ++ [headed.length - 1]) (nextVisible ++ [newHeaded.length - 1]) (materials ++ [hs]) headed newHeaded := by
  let a := Parents.label d source coordinates
  let newA := Parents.label d target newCoordinates
  let newHs := Source.relocateForests d (source ++ [a]) (target ++ [newA]) (List.range source.length ++ [target.length]) hs
  let key := queryKey d source coordinates hs
  let frame := frameAt state (representative visible a (d - 1))
  let below := smaller frame key
  let u := vector state visible a
  let v := vector next nextVisible newA
  have belowKnown := (smaller_inheritedMaterials (queried_frame_inheritedMaterials known oldView coordinates) key).keys
  have outputSize : (BMS.parentTable (d + 2) (matrix state)).length ≤ state.length := by
    simp only [BMS.parentTable_length, matrix, List.length_map]; exact Nat.le_refl _
  cases found : equal frame key with
  | some bound =>
    have foundKey : bound.key = key := Keys.compare_eq_imp _ _
      (by simpa only [beq_iff_eq] using List.find?_some found)
    have result := fixed_prefix_save_emit coherent valid unit initial known oldView outputSize
      visiblePrefix newLength (List.prefix_refl state) statePrefix belowKnown a newA hs u v
      {bound with latest := some state.length} {bound with latest := some next.length} rfl rfl
      (by change bound.key = _; rw [Keys.atContext_append]; exact foundKey.trans keySame.symm)
    dsimp only [frame, key, queryKey, a] at found
    simp only [queryKey] at keySame
    simp only [headState, encode, oldView.length, newLength, keySame, frameSame, found,
      emit_length, Nat.add_sub_cancel]
    exact result
  | none =>
    let c := (base below).height
    let withForests := encodeForests d (Parents.annotateForests d (source ++ [a]) hs) visible u c below
      (emit (emit state u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 [])
    let newForests := encodeForests d (Parents.annotateForests d (target ++ [newA]) newHs) nextVisible v c below
      (emit (emit next v (c + 1) 1 []) (fun j => v j + 1) (c + 2) 2 [])
    have oldExtended : state <+: withForests :=
      (emit_extends ..).trans ((emit_extends ..).trans (encodeForests_extends ..))
    have newExtended : state <+: newForests := statePrefix.trans
      ((emit_extends ..).trans ((emit_extends ..).trans (encodeForests_extends ..)))
    have result := fixed_prefix_save_emit coherent valid unit initial known oldView outputSize
      visiblePrefix newLength oldExtended newExtended belowKnown a newA hs (fun j => u j + 1) (fun j => v j + 1)
      ⟨key, c + 2, some withForests.length, some state.length⟩
      ⟨key, c + 2, some newForests.length, some next.length⟩ rfl rfl
      (by change key = _; rw [Keys.atContext_append]; exact keySame.symm)
    dsimp only [frame, key, queryKey, a] at found
    simp only [queryKey] at keySame
    simp only [headState, encode, oldView.length, newLength, keySame, frameSame, found,
      emit_length, Nat.add_sub_cancel]
    exact result

end BTnSSBMS.Encoder
