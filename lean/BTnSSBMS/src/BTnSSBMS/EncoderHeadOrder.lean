import BTnSSBMS.KeyNormalizationOrder

/-!
Join numerical/key comparison to the real output prefix. Two distinct
fresh keys in the identical binding gap require recursive comparison.
EncoderStrictOrder supplies that argument, including delimiter boundaries.
-/
namespace BTnSSBMS.Encoder

theorem encode_lt_of_firstHeight (d : Nat) (a : ParentLabel)
    (hs ks : Forests ParentLabel) (tail rest : ParentExpr) (visible : List Nat) (state : State d)
    (strict : firstHeight (frameAt state (representative visible a (d - 1)))
        (Keys.ofColumn d visible.length a hs) <
      firstHeight (frameAt state (representative visible a (d - 1)))
        (Keys.ofColumn d visible.length a ks)) :
    matrixCompare (matrix (encode d (.cons a hs tail) visible state))
      (matrix (encode d (.cons a ks rest) visible state)) = .lt := by
  obtain ⟨heightA, tagA, extraA, firstA, shapeA⟩ := encode_cons_first_row d a hs tail visible state
  obtain ⟨heightB, tagB, extraB, firstB, shapeB⟩ := encode_cons_first_row d a ks rest visible state
  have first : listCompare Ord.compare (row d (vector state visible a) heightA tagA)
      (row d (vector state visible a) heightB tagB) = .lt := by
    apply columnCompare_lt_at _ _ d (by rw [row_width]; omega) (by rw [row_width]; omega)
    · intro j room
      rw [row_numerical_reading d _ heightA tagA j room, row_numerical_reading d _ heightB tagB j room]
    · rw [row_key_reading, row_key_reading, firstA, firstB]
      exact strict
  simp only [shapeA, shapeB, matrixCompare,
    listCompare_common_prefix (listCompare Ord.compare) columnCompare_self, listCompare, first]

/-- A smaller actual attachment either already has a strictly smaller
matrix output or both complete keys are fresh in exactly the same gap.
Frame hypotheses are the existing maintained entering-state invariants. -/
theorem encode_attachment_compare_cases {d : Nat} {source : ParentContext} {visible : List Nat}
    (state : State d) (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
    (length : visible.length = source.length)
    (ordered : FramesOrdered state) (dense : FramesDense state) (good : VisibleGood state visible)
    (a : List Nat) (hs ks : Forests (List Nat)) (tail rest : NumericalExpr)
    (leftLegal : Source.FiniteLegalForests d (source ++ [Parents.label d source a]) (a[0]?.getD 0) hs)
    (rightLegal : Source.FiniteLegalForests d (source ++ [Parents.label d source a]) (a[0]?.getD 0) ks)
    (lower : hs.compare (listCompare Ord.compare) ks = .lt) :
    let annotatedH := Parents.annotateForests d (source ++ [Parents.label d source a]) hs
    let annotatedK := Parents.annotateForests d (source ++ [Parents.label d source a]) ks
    let keyH := Keys.ofColumn d visible.length (Parents.label d source a) annotatedH
    let keyK := Keys.ofColumn d visible.length (Parents.label d source a) annotatedK
    let frame := frameAt state (representative visible (Parents.label d source a) (d - 1))
    matrixCompare (matrix (encode d (Parents.annotate d source (.cons a hs tail)) visible state))
      (matrix (encode d (Parents.annotate d source (.cons a ks rest)) visible state)) = .lt ∨
      (equal frame keyH = none ∧ equal frame keyK = none ∧ smaller frame keyH = smaller frame keyK) := by
  dsimp only
  have keys : Keys.compare
      (Keys.ofColumn d visible.length (Parents.label d source a)
        (Parents.annotateForests d (source ++ [Parents.label d source a]) hs))
      (Keys.ofColumn d visible.length (Parents.label d source a)
        (Parents.annotateForests d (source ++ [Parents.label d source a]) ks)) = .lt := by
    rw [length, Keys.ofColumn_annotate_compare coherent valid a hs ks leftLegal rightLegal]
    exact lower
  have frameOrder := queried_frame_ordered ordered (representative visible (Parents.label d source a) (d - 1))
  have frameDense := queried_frame_dense dense (representative visible (Parents.label d source a) (d - 1))
  have frameZero := queried_frame_has_zero state visible good (Parents.label d source a) (d - 1)
  rcases firstHeight_compare_cases frameOrder frameDense frameZero _ _ keys with strict | gap
  · exact Or.inl (encode_lt_of_firstHeight d (Parents.label d source a) _ _ _ _ visible state strict)
  · exact Or.inr gap

end BTnSSBMS.Encoder
