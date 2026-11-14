import BTnSSBMS.EncoderBoundary

/-!
Split the real encoder after one complete source column. This is a proved
decomposition of encode, not a replacement algorithm. In particular the
restored representative is its closing column, not its definition or slot.
-/
namespace BTnSSBMS.Encoder

def headState (d : Nat) (a : ParentLabel) (hs : Forests ParentLabel)
    (visible : List Nat) (state : State d) : State d :=
  encode d (.cons a hs .nil) visible state

theorem encode_split_head (d : Nat) (a : ParentLabel) (hs : Forests ParentLabel)
    (tail : ParentExpr) (visible : List Nat) (state : State d) :
    encode d (.cons a hs tail) visible state =
      encode d tail (visible ++ [(headState d a hs visible state).length - 1])
        (headState d a hs visible state) := by
  simp only [headState, encode]
  split <;> simp only [emit_length, Nat.add_sub_cancel]

theorem headState_nonempty (d : Nat) (a : ParentLabel) (hs : Forests ParentLabel)
    (visible : List Nat) (state : State d) : 0 < (headState d a hs visible state).length := by
  simp only [headState, encode]
  split <;> simp only [emit_length] <;> omega

theorem headState_view {d : Nat} {source : ParentContext} {visible : List Nat}
    (state : State d) (positive : 0 < d)
    (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (a : List Nat) (hs : Forests (List Nat))
    (separated : Source.ForestsAbove (a[0]?.getD 0) hs) :
    Parents.NumericalView d (source ++ [Parents.label d source a])
      (BMS.parentTable (d + 2) (matrix (headState d (Parents.label d source a)
        (Parents.annotateForests d (source ++ [Parents.label d source a]) hs) visible state)))
      (visible ++ [(headState d (Parents.label d source a)
        (Parents.annotateForests d (source ++ [Parents.label d source a]) hs) visible state).length - 1]) := by
  simp only [headState, encode]
  split
  next bound found =>
    simpa only [encode, emit_length, Nat.add_sub_cancel] using
      emit_numerical_view state coherent valid view a bound.height 0 _
  next fresh =>
    let label := Parents.label d source a
    let annotated := Parents.annotateForests d (source ++ [label]) hs
    let key := Keys.ofColumn d visible.length label annotated
    let below := smaller (frameAt state (representative visible label (d - 1))) key
    let c := (base below).height
    let u := vector state visible label
    let guarded := emit (emit state u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 []
    let forests := encodeForests d annotated visible u c below guarded
    have gate := encodeForests_numerical_gate d hs source a visible state guarded u
      (state.length + 1) c below positive coherent valid view
      (initial_numerical_gate state coherent valid view a c) separated
    simpa only [encode, emit_length, Nat.add_sub_cancel] using
      closing_numerical_view state forests valid view a c
        (below ++ [⟨key, c + 2, some forests.length, some state.length⟩]) gate
        (encodeForests_extends d annotated visible u c below guarded) positive coherent

theorem headState_good (d : Nat) (a : ParentLabel) (hs : Forests ParentLabel)
    (visible : List Nat) (state : State d) (good : VisibleGood state visible) :
    VisibleGood (headState d a hs visible state)
      (visible ++ [(headState d a hs visible state).length - 1]) := by
  have hz := queried_frame_has_zero state visible good a (d - 1)
  simp only [headState, encode]
  split
  next bound found =>
    simpa only [encode, emit_length, Nat.add_sub_cancel] using
      visibleGood_emit state visible good (vector state visible a) bound.height 0 _
        (reused_frame_has_zero hz _ bound found _)
  next fresh =>
    have belowGood := fresh_smaller_has_zero hz _ fresh
    simp only [emit_length, Nat.add_sub_cancel]
    apply visibleGood_emit
    · exact visibleGood_extends ((emit_extends ..).trans
        ((emit_extends ..).trans (encodeForests_extends d hs _ _ _ _ _))) good
    · exact hasZero_append belowGood

/-- Peel a known state prefix off a matrix comparison with suffixes. -/
theorem matrix_extension {d : Nat} {state next : State d} (extended : state <+: next) :
    ∃ added, matrix next = matrix state ++ added := by
  obtain ⟨extra, shape⟩ := extended
  exact ⟨matrix extra, by rw [← shape]; simp only [matrix, List.map_append]⟩

end BTnSSBMS.Encoder
