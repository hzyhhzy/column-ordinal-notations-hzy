import BTnSSBMS.RootedHeadComparison
import BTnSSBMS.ShiftComparison

/-!
Turn a concrete query decision into a real output decision. Strictness
survives arbitrary continuations. If a query reuses a definition, the
decision already covers the complete source head, not just its first row.
The fresh/fresh case is reserved for the mutual forest comparison.
-/
namespace BTnSSBMS.Encoder

theorem queryHead_comparison {d : Nat} (state next : State d) (a newA : ParentLabel)
    (key newKey : Key) (visible nextVisible : List Nat) (root : Nat) (delta : Nat → Nat)
    (decision :
      listCompare Ord.compare (row d (vector next nextVisible newA)
        (firstHeight (frameAt next (representative nextVisible newA (d - 1))) newKey)
        (freshBit (frameAt next (representative nextVisible newA (d - 1))) newKey))
        (shiftedColumn (queryHead d a key visible state) root delta state.length) = .lt ∨
      row d (vector next nextVisible newA)
        (firstHeight (frameAt next (representative nextVisible newA (d - 1))) newKey)
        (freshBit (frameAt next (representative nextVisible newA (d - 1))) newKey) =
        shiftedColumn (queryHead d a key visible state) root delta state.length) :
    ShiftComparison root delta state next (queryHead d a key visible state) (queryHead d newA newKey nextVisible next) := by
  refine ⟨queryHead_extends .., queryHead_extends .., ?_⟩
  rw [queryHead_length, shiftedOutput_single, queryHead_matrix]
  have length : (matrix next).length = next.length := List.length_map _
  rw [← length, List.drop_left]
  rcases decision with strict | same
  · exact Or.inl ⟨[], _, _, [], [], rfl, rfl, strict⟩
  · exact Or.inr (congrArg (fun col => [col]) same)

/-- A strict query difference compares the complete later outputs with
the actual frozen BMS copy, regardless of either continuation's length. -/
theorem queryHead_strict_continuations {d : Nat} (state next : State d) (a newA : ParentLabel)
    (key newKey : Key) (visible nextVisible : List Nat) (root : Nat) (delta : Nat → Nat)
    {result newResult : State d}
    (oldContinuation : queryHead d a key visible state <+: result)
    (newContinuation : queryHead d newA newKey nextVisible next <+: newResult)
    (strict : listCompare Ord.compare (row d (vector next nextVisible newA)
      (firstHeight (frameAt next (representative nextVisible newA (d - 1))) newKey)
      (freshBit (frameAt next (representative nextVisible newA (d - 1))) newKey))
      (shiftedColumn (queryHead d a key visible state) root delta state.length) = .lt) :
    MatrixFirstLt ((matrix newResult).drop next.length)
      (BMS.copy (matrix result) (BMS.thresholds (BMS.parentTable (d + 2) (matrix result)) root (d + 1))
        ((List.range (d + 2)).map delta) state.length result.length 1) := by
  rw [← shiftedOutput_eq_copy result root delta state.length result.length (Nat.le_refl _)]
  apply shifted_strict_extends (queryHead_extends ..) (queryHead_extends ..) oldContinuation newContinuation
  rw [queryHead_length, shiftedOutput_single, queryHead_matrix]
  have length : (matrix next).length = next.length := List.length_map _
  rw [← length, List.drop_left]
  exact ⟨[], _, _, [], [], rfl, rfl, strict⟩

theorem headState_eq_queryHead_of_reuse {d : Nat} {state : State d} {a : ParentLabel}
    {hs : Forests ParentLabel} {visible : List Nat}
    (reused : equal (frameAt state (representative visible a (d - 1)))
      (Keys.ofColumn d visible.length a hs) ≠ none) :
    headState d a hs visible state = queryHead d a (Keys.ofColumn d visible.length a hs) visible state := by
  cases found : equal (frameAt state (representative visible a (d - 1))) (Keys.ofColumn d visible.length a hs) with
  | none => exact False.elim (reused found)
  | some bound => simp only [headState, encode, queryHead, found]

theorem headState_comparison_of_query_decision {d : Nat} (state next : State d) (a newA : ParentLabel)
    (hs newHs : Forests ParentLabel) (visible nextVisible : List Nat) (root : Nat) (delta : Nat → Nat)
    (reused : equal (frameAt state (representative visible a (d - 1))) (Keys.ofColumn d visible.length a hs) ≠ none ∨
      equal (frameAt next (representative nextVisible newA (d - 1))) (Keys.ofColumn d nextVisible.length newA newHs) ≠ none)
    (decision :
      let key := Keys.ofColumn d visible.length a hs
      let newKey := Keys.ofColumn d nextVisible.length newA newHs
      let old := frameAt state (representative visible a (d - 1))
      let new := frameAt next (representative nextVisible newA (d - 1))
      let newCol := row d (vector next nextVisible newA) (firstHeight new newKey) (freshBit new newKey)
      let copied := shiftedColumn (queryHead d a key visible state) root delta state.length
      listCompare Ord.compare newCol copied = .lt ∨
        (newCol = copied ∧ (equal new newKey = none ↔ equal old key = none))) :
    ShiftComparison root delta state next (headState d a hs visible state) (headState d newA newHs nextVisible next) := by
  dsimp only at decision
  rcases decision with strict | ⟨same, branch⟩
  · have compared := queryHead_strict_continuations state next a newA _ _ visible nextVisible root delta
      (queryHead_prefix_encode d a hs .nil visible state) (queryHead_prefix_encode d newA newHs .nil nextVisible next) strict
    refine ⟨encode_extends .., encode_extends .., Or.inl ?_⟩
    rw [shiftedOutput_eq_copy _ _ _ _ _ (Nat.le_refl _)]
    exact compared
  · have oldReused : equal (frameAt state (representative visible a (d - 1))) (Keys.ofColumn d visible.length a hs) ≠ none := by
      intro fresh
      rcases reused with old | new
      · exact old fresh
      · exact new (branch.mpr fresh)
    have newReused : equal (frameAt next (representative nextVisible newA (d - 1)))
        (Keys.ofColumn d nextVisible.length newA newHs) ≠ none := fun fresh => oldReused (branch.mp fresh)
    rw [headState_eq_queryHead_of_reuse oldReused, headState_eq_queryHead_of_reuse newReused]
    exact queryHead_comparison state next a newA _ _ visible nextVisible root delta (Or.inr same)

end BTnSSBMS.Encoder
