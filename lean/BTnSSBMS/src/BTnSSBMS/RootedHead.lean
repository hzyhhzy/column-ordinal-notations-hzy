import BTnSSBMS.RootedQuery
import BTnSSBMS.KeyRowRebase

/-!
Query comparison at a genuine entering state, including entries inside
nested forests. No global standard-entry certificate is needed: the
stored root and the actual key-row parent search supply the activation.
-/
namespace BTnSSBMS.Encoder

theorem retained_root_queryHead_ancestor {d : Nat} {source : ParentContext} {visible : List Nat}
    (state : State d) (positive : 0 < d) (coherent : Parents.Coherent d source)
    (valid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (ordered : FramesOrdered state) (dense : FramesDense state)
    (realized : FramesRealized state) (paths : FramesAncestral state)
    (coordinates : List Nat) (key : Key)
    (zero : HasZero (frameAt state (representative visible (Parents.label d source coordinates) (d - 1))))
    (root : Nat)
    (retained : ∃ b ∈ smaller (frameAt state
      (representative visible (Parents.label d source coordinates) (d - 1))) key,
      b.latest = some root) :
    Parents.Ancestor (BMS.parentTable (d + 2) (matrix
      (queryHead d (Parents.label d source coordinates) key visible state))) d root state.length := by
  obtain ⟨b, member, latest⟩ := retained
  obtain ⟨inFrame, less⟩ := List.mem_filter.mp member
  exact (queryHead_key_ancestor_iff state positive coherent valid view ordered dense realized paths
    coordinates key zero b inFrame root latest).mpr (by simpa only [beq_iff_eq] using less)

theorem RootedInsertion.query_height_bound {d : Nat} {source : ParentContext} {visible : List Nat}
    (state : State d) (positive : 0 < d) (coherent : Parents.Coherent d source)
    (valid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (ordered : FramesOrdered state) (dense : FramesDense state)
    (realized : FramesRealized state) (paths : FramesAncestral state)
    (coordinates : List Nat) (oldKey newKey : Key)
    (zero : HasZero (frameAt state (representative visible (Parents.label d source coordinates) (d - 1))))
    {new : List Binding} (newOrdered : FrameOrdered new) (newDense : FrameDense new) (newZero : HasZero new)
    {root : Nat} {keyOf : Binding → Key} {pool : List Key}
    (splice : RootedInsertion root keyOf
      (frameAt state (representative visible (Parents.label d source coordinates) (d - 1))) new pool)
    (comparisons : ∀ b ∈ frameAt state (representative visible (Parents.label d source coordinates) (d - 1)),
      Keys.compare (keyOf b) newKey = Keys.compare b.key oldKey) :
    let first := queryHead d (Parents.label d source coordinates) oldKey visible state
    let old := frameAt state (representative visible (Parents.label d source coordinates) (d - 1))
    firstHeight new newKey ≤ firstHeight old oldKey + rowBump first d root (2 * pool.length) state.length ∧
      (¬ Parents.Ancestor (BMS.parentTable (d + 2) (matrix first)) d root state.length →
        firstHeight new newKey = firstHeight old oldKey) := by
  classical
  dsimp only
  have activates := retained_root_queryHead_ancestor state positive coherent valid view ordered dense realized paths
    coordinates oldKey zero root
  refine ⟨?_, ?_⟩
  · exact splice.height_le_activated (queried_frame_ordered ordered _) (queried_frame_dense dense _) zero
      newOrdered newDense newZero oldKey newKey comparisons _ activates
  · intro inactive
    exact splice.height_eq_of_inactive (queried_frame_ordered ordered _) (queried_frame_dense dense _) zero
      newOrdered newDense newZero oldKey newKey comparisons (fun kept => inactive (activates kept))

theorem firstHeight_bump_eq_branch {d : Nat} {state : State d} {old new : List Binding}
    (oldOrdered : FrameOrdered old) (oldDense : FrameDense old) (oldZero : HasZero old)
    (newOrdered : FrameOrdered new) (newDense : FrameDense new) (newZero : HasZero new)
    (oldKey newKey : Key) (j root count p : Nat)
    (same : firstHeight new newKey = firstHeight old oldKey + rowBump state j root (2 * count) p) :
    equal new newKey = none ↔ equal old oldKey = none := by
  classical
  apply freshBit_eq_branch
  by_cases active : Parents.Ancestor (BMS.parentTable (d + 2) (matrix state)) j root p
  · apply firstHeight_even_shift_freshBit oldOrdered oldDense oldZero newOrdered newDense newZero oldKey newKey count
    simpa only [rowBump, active, if_true] using same
  · apply firstHeight_even_shift_freshBit oldOrdered oldDense oldZero newOrdered newDense newZero oldKey newKey 0
    simpa only [rowBump, active, if_false, Nat.mul_zero] using same

/-- A different fresh/reuse choice has already created a strict height
difference. Nothing about the subsequent forest lengths is assumed. -/
theorem firstHeight_bump_lt_of_branch_mismatch {d : Nat} {state : State d} {old new : List Binding}
    (oldOrdered : FrameOrdered old) (oldDense : FrameDense old) (oldZero : HasZero old)
    (newOrdered : FrameOrdered new) (newDense : FrameDense new) (newZero : HasZero new)
    (oldKey newKey : Key) (j root count p : Nat)
    (bound : firstHeight new newKey ≤ firstHeight old oldKey + rowBump state j root (2 * count) p)
    (mismatch : ¬ (equal new newKey = none ↔ equal old oldKey = none)) :
    firstHeight new newKey < firstHeight old oldKey + rowBump state j root (2 * count) p := by
  have different : firstHeight new newKey ≠ firstHeight old oldKey + rowBump state j root (2 * count) p := by
    intro same
    exact mismatch (firstHeight_bump_eq_branch oldOrdered oldDense oldZero newOrdered newDense newZero
      oldKey newKey j root count p same)
  omega

theorem fresh_base_shift {old new : List Binding} {oldKey newKey : Key} {shift : Nat}
    (oldFresh : equal old oldKey = none) (newFresh : equal new newKey = none)
    (same : firstHeight new newKey = firstHeight old oldKey + shift) :
    (base (smaller new newKey)).height = (base (smaller old oldKey)).height + shift := by
  simp only [firstHeight, oldFresh, newFresh] at same
  omega

end BTnSSBMS.Encoder
