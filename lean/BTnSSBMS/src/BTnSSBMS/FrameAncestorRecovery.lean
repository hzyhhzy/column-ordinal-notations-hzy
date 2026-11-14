import BTnSSBMS.TopRowEndpointClasses

/-!
Recover a surviving saved binding from an actual key-row ancestor path.
Density supplies a binding at every even height up to a self-registered
representative. Uniqueness along the computed parent chain identifies its
actual latest pointer. No converse to frame ancestry is assumed.
-/
namespace BTnSSBMS.Encoder

theorem FramesDense.restrict {state next : State d} (dense : FramesDense next)
    (initial : state <+: next) : FramesDense state :=
  fun col member => dense col (initial.subset member)

theorem selfLatest_even_readout {state : State d} (dense : FramesDense state)
    (known : FramesRealized state) {position : Nat} (self : SelfLatest state position) :
    ∃ i, Readout state position (2 * i) 0 := by
  obtain ⟨col, lookup, b, member, latest⟩ := self
  obtain ⟨i, found⟩ := List.mem_iff_getElem?.mp member
  have height := dense col (List.mem_of_getElem? lookup) i b found
  have output := (known position col lookup b member).1
  rw [latest] at output
  rw [height] at output
  exact ⟨i, readout_extends (List.take_prefix ..) output⟩

theorem key_ancestors_same_height {state : State d} {left right endpoint h t u : Nat}
    (leftPath : Parents.Ancestor (BMS.parentTable (d + 2) (matrix state)) d left endpoint)
    (rightPath : Parents.Ancestor (BMS.parentTable (d + 2) (matrix state)) d right endpoint)
    (leftOutput : Readout state left h t) (rightOutput : Readout state right h u) :
    left = right := by
  have forward := leftPath.of_reading_le (BMS.parentTable_coherent _ _) rightPath
    (by rw [leftOutput.key_reading, rightOutput.key_reading]; exact Nat.le_refl _)
  have backward := rightPath.of_reading_le (BMS.parentTable_coherent _ _) leftPath
    (by rw [leftOutput.key_reading, rightOutput.key_reading]; exact Nat.le_refl _)
  have one := forward.le (BMS.parentTable_valid _ _)
  have two := backward.le (BMS.parentTable_valid _ _)
  omega

/-- For two self-registered actual representatives, a key-row ancestry
path is witnessed by a binding in the later representative's own saved
frame. This holds also when the two positions coincide. -/
theorem selfLatest_ancestor_binding {state : State d} (dense : FramesDense state)
    (known : FramesRealized state) (paths : FramesAncestral state) {left right : Nat}
    (leftSelf : SelfLatest state left) (rightSelf : SelfLatest state right)
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (matrix state)) d left right) :
    ∃ col, state[right]? = some col ∧ ∃ b ∈ col.frame, b.latest = some left := by
  obtain ⟨i, leftOutput⟩ := selfLatest_even_readout dense known leftSelf
  obtain ⟨col, lookup, top, topMember, topLatest⟩ := rightSelf
  obtain ⟨j, topLookup⟩ := List.mem_iff_getElem?.mp topMember
  have frameDense := dense col (List.mem_of_getElem? lookup)
  have topHeight := frameDense j top topLookup
  have frameKnown := frameRealized_extends (List.take_prefix ..) (known right col lookup)
  have rightOutput := (frameKnown top topMember).1
  rw [topLatest, topHeight] at rightOutput
  have heightBound := path.reading_le (BMS.parentTable_coherent _ _)
  rw [leftOutput.key_reading, rightOutput.key_reading] at heightBound
  have jBound := (List.getElem?_eq_some_iff.mp topLookup).choose
  have iBound : i < col.frame.length := by omega
  let b := col.frame[i]
  have bLookup : col.frame[i]? = some b := List.getElem?_eq_getElem iBound
  have bMember := List.mem_of_getElem? bLookup
  have bHeight := frameDense i b bLookup
  obtain ⟨q, latest, qPath, _⟩ := paths right col lookup b bMember
  have qOutput := (frameKnown b bMember).1
  rw [latest, bHeight] at qOutput
  have same : left = q := key_ancestors_same_height path qPath leftOutput qOutput
  exact ⟨col, lookup, b, bMember, same ▸ latest⟩

end BTnSSBMS.Encoder
