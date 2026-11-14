import BTnSSBMS.RootedHead
import BTnSSBMS.ShiftedOutput

/-!
First-column comparison of two real relocated queries. Numerical values
are obtained from actual parent paths. A strict key-row difference ends
the comparison; equality forces the same fresh/reuse branch.
-/
namespace BTnSSBMS.Encoder

theorem queryHead_matrix (d : Nat) (a : ParentLabel) (key : Key) (visible : List Nat) (state : State d) :
    matrix (queryHead d a key visible state) = matrix state ++
      [row d (vector state visible a)
        (firstHeight (frameAt state (representative visible a (d - 1))) key)
        (freshBit (frameAt state (representative visible a (d - 1))) key)] := by
  simp only [queryHead]
  split <;> simp_all only [matrix_emit, firstHeight, freshBit, Option.isSome_some,
    Option.isSome_none, if_true, Bool.false_eq_true, if_false]

theorem queryHead_shiftedColumn (d : Nat) (a : ParentLabel) (key : Key) (visible : List Nat) (state : State d)
    (root : Nat) (delta : Nat → Nat) :
    shiftedColumn (queryHead d a key visible state) root delta state.length =
      row d (fun j => vector state visible a j + rowBump (queryHead d a key visible state) j root (delta j) state.length)
        (firstHeight (frameAt state (representative visible a (d - 1))) key +
          rowBump (queryHead d a key visible state) d root (delta d) state.length)
        (freshBit (frameAt state (representative visible a (d - 1))) key) := by
  simp only [queryHead]
  split <;> simp_all only [shiftedColumn_emit, firstHeight, freshBit, Option.isSome_some,
    Option.isSome_none, if_true, Bool.false_eq_true, if_false]

theorem RowRebaseValues.query_values {d : Nat} {source target : ParentContext}
    {moved visible nextVisible : List Nat} {state next : State d} {j root amount : Nat}
    (values : RowRebaseValues j root amount source.length moved visible nextVisible state next)
    (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
    (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
    (view : Parents.NumericalView d source target moved)
    (oldView : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (newView : Parents.NumericalView d target (BMS.parentTable (d + 2) (matrix next)) nextVisible)
    (coordinates : List Nat) (key : Key) (room : j < d) (rootBefore : root < state.length) :
    vector next nextVisible (Parents.label d target (Source.relocationHead d source target moved coordinates)) j =
      vector state visible (Parents.label d source coordinates) j +
        rowBump (queryHead d (Parents.label d source coordinates) key visible state) j root amount state.length := by
  simp only [queryHead]
  split <;> exact values.head_values sourceCoherent sourceValid targetCoherent targetValid view oldView newView
    coordinates _ _ _ room rootBefore

theorem RootedFrames.query_column_alternative {d root : Nat} {source target : ParentContext}
    {coordinates visible nextVisible moved owners : List Nat} {materials : List (Forests (List Nat))}
    {state next : State d} {hs : Forests (List Nat)} {pool : List Key}
    (related : RootedFrames root d source target moved visible nextVisible materials pool state next)
    (query : MaterialQuery d source coordinates visible owners materials state hs)
    (positive : 0 < d) (rootBefore : root < state.length)
    (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
    (targetUnit : Parents.UnitSteps d target) (view : Parents.NumericalView d source target moved)
    (newView : Parents.NumericalView d target (BMS.parentTable (d + 2) (matrix next)) nextVisible)
    (targetWidth : ∀ i, i < target.length → (target[i]?.getD default).coordinates.length = d)
    (ordered : FramesOrdered state) (dense : FramesDense state) (good : VisibleGood state visible)
    (realized : FramesRealized state) (paths : FramesAncestral state)
    (newOrdered : FramesOrdered next) (newDense : FramesDense next) (newGood : VisibleGood next nextVisible)
    (delta : Nat → Nat) (keyAmount : delta d = 2 * pool.length)
    (values : ∀ j, j < d → RowRebaseValues j root (delta j) source.length moved visible nextVisible state next) :
    let a := Parents.label d source coordinates
    let newCoordinates := Source.relocationHead d source target moved coordinates
    let newA := Parents.label d target newCoordinates
    let newHs := Source.relocateForests d (source ++ [a]) (target ++ [newA]) (moved ++ [target.length]) hs
    let key := queryKey d source coordinates hs
    let newKey := queryKey d target newCoordinates newHs
    let frame := frameAt state (representative visible a (d - 1))
    let newFrame := frameAt next (representative nextVisible newA (d - 1))
    let first := queryHead d a key visible state
    let newCol := row d (vector next nextVisible newA) (firstHeight newFrame newKey) (freshBit newFrame newKey)
    listCompare Ord.compare newCol (shiftedColumn first root delta state.length) = .lt ∨
      (newCol = shiftedColumn first root delta state.length ∧
        (equal newFrame newKey = none ↔ equal frame key = none)) := by
  dsimp only
  let a := Parents.label d source coordinates
  let newCoordinates := Source.relocationHead d source target moved coordinates
  let newA := Parents.label d target newCoordinates
  let newHs := Source.relocateForests d (source ++ [a]) (target ++ [newA]) (moved ++ [target.length]) hs
  let key := queryKey d source coordinates hs
  let newKey := queryKey d target newCoordinates newHs
  let frame := frameAt state (representative visible a (d - 1))
  let newFrame := frameAt next (representative nextVisible newA (d - 1))
  let first := queryHead d a key visible state
  have oldOrder : FrameOrdered frame := queried_frame_ordered ordered _
  have oldDense : FrameDense frame := queried_frame_dense dense _
  have oldZero : HasZero frame := queried_frame_has_zero state visible good a (d - 1)
  have newOrder : FrameOrdered newFrame := queried_frame_ordered newOrdered _
  have newD : FrameDense newFrame := queried_frame_dense newDense _
  have newZero : HasZero newFrame := queried_frame_has_zero next nextVisible newGood newA (d - 1)
  obtain ⟨splice⟩ := related.queried query.view newView view query.coherent query.valid
    targetCoherent targetValid positive coordinates
  have comparisons := query.relocation_comparisons targetCoherent targetValid targetUnit view targetWidth positive
  have bound := (splice.query_height_bound state positive query.coherent query.valid query.view ordered dense realized paths
    coordinates key newKey oldZero newOrder newD newZero comparisons).1
  change firstHeight newFrame newKey ≤ firstHeight frame key + rowBump first d root (2 * pool.length) state.length at bound
  rw [← keyAmount] at bound
  have numerical (j : Nat) (room : j < d) :
      vector next nextVisible newA j = vector state visible a j + rowBump first j root (delta j) state.length :=
    (values j room).query_values query.coherent query.valid targetCoherent targetValid view query.view newView
      coordinates key room rootBefore
  by_cases same : firstHeight newFrame newKey = firstHeight frame key + rowBump first d root (delta d) state.length
  · have branch := firstHeight_bump_eq_branch oldOrder oldDense oldZero newOrder newD newZero key newKey d root pool.length state.length
      (by simpa only [keyAmount] using same)
    have bitSame : freshBit newFrame newKey = freshBit frame key := by
      cases oldFound : equal frame key <;> cases newFound : equal newFrame newKey <;> simp_all [freshBit]
    refine Or.inr ⟨?_, branch⟩
    rw [queryHead_shiftedColumn]
    change row d (vector next nextVisible newA) (firstHeight newFrame newKey) (freshBit newFrame newKey) =
      row d (fun j => vector state visible a j + rowBump first j root (delta j) state.length)
        (firstHeight frame key + rowBump first d root (delta d) state.length) (freshBit frame key)
    rw [same, bitSame]
    unfold row
    congr 1
    apply List.map_congr_left
    intro j member
    exact numerical j (List.mem_range.mp member)
  · apply Or.inl
    rw [queryHead_shiftedColumn]
    apply columnCompare_lt_at _ _ d (by rw [row_width]; omega) (by rw [row_width]; omega)
    · intro j room
      rw [row_numerical_reading d _ _ _ j room, row_numerical_reading d _ _ _ j room]
      exact numerical j room
    · simp only [row_key_reading]
      exact Nat.lt_of_le_of_ne bound same

end BTnSSBMS.Encoder
