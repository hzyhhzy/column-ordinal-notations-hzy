import BTnSSBMS.EncoderHeadState

/-!
Boundary bookkeeping for the actual mutual order proof. None means the
outer sequence has no following delimiter; some (s,t) records a source
owner value s and its actual target representative value t. No ordering
of the encoder is included in these finite entering-state predicates.
-/
namespace BTnSSBMS.Encoder

def OrderFence (source : ParentContext) (visible : List Nat) (state : State d)
    (floor : Option (Nat × Nat)) : Prop :=
  match floor with
  | none => True
  | some (s, t) => ∃ root, root < source.length ∧
      Parents.reading source 0 root = s ∧
      Parents.Ancestor source 0 root (source.length - 1) ∧
      Parents.reading (BMS.parentTable (d + 2) (matrix state)) 0 (Parents.point visible root) = t

def AboveFloor (floor : Option (Nat × Nat)) (e : NumericalExpr) : Prop :=
  ∀ s t, floor = some (s, t) → ∀ a ∈ Source.labels e, s < a[0]?.getD 0

def ExitBelow (bound : Option Nat) : Matrix → Prop
  | [] => True
  | head :: _ => ∃ t, bound = some t ∧ 0 < head.length ∧ head[0]?.getD 0 ≤ t

theorem ExitBelow.mono {a b : Nat} {tail : Matrix} (bound : a ≤ b)
    (low : ExitBelow (some a) tail) : ExitBelow (some b) tail := by
  cases tail with
  | nil => trivial
  | cons head rest =>
    obtain ⟨t, equal, width, value⟩ := low
    have same : a = t := Option.some.inj equal
    exact ⟨b, rfl, width, by omega⟩

theorem OrderFence.after_head {d : Nat} {source : ParentContext} {visible : List Nat}
    (state : State d) (positive : 0 < d)
    (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    {floor : Option (Nat × Nat)} (fence : OrderFence source visible state floor)
    (a : List Nat) (hs : Forests (List Nat))
    (above : ∀ s t, floor = some (s, t) → s < a[0]?.getD 0) :
    let next := headState d (Parents.label d source a)
      (Parents.annotateForests d (source ++ [Parents.label d source a]) hs) visible state
    OrderFence (source ++ [Parents.label d source a])
      (visible ++ [next.length - 1]) next floor := by
  dsimp only
  cases floor with
  | none => trivial
  | some pair =>
    obtain ⟨s, t⟩ := pair
    obtain ⟨root, inside, sourceValue, path, targetValue⟩ := fence
    have extended := encode_extends d
      (.cons (Parents.label d source a) (Parents.annotateForests d (source ++ [Parents.label d source a]) hs) .nil)
      visible state
    refine ⟨root, by simp only [List.length_append, List.length_cons, List.length_nil]; omega,
      ?_, ?_, ?_⟩
    · rw [← Parents.reading_prefix (List.prefix_append _ _) 0 root inside]
      exact sourceValue
    · simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_sub_cancel]
      apply Parents.fence_append_label coherent valid positive inside path a
      rw [sourceValue]
      exact above s t rfl
    · rw [Parents.point_append_old visible root _ (by rw [view.length]; exact inside)]
      dsimp only [headState]
      rw [← Parents.reading_prefix (table_prefix extended) 0 (Parents.point visible root) (view.bounded root inside)]
      exact targetValue

theorem empty_before_nonempty {d : Nat} {source : ParentContext} {visible : List Nat}
    (state : State d) (positive : 0 < d)
    (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    {floor : Option (Nat × Nat)} (fence : OrderFence source visible state floor)
    (a : List Nat) (hs : Forests (List Nat)) (tail : NumericalExpr)
    (above : ∀ s t, floor = some (s, t) → s < a[0]?.getD 0)
    (leftExit rightExit : Matrix) (low : ExitBelow (floor.map Prod.snd) leftExit) :
    matrixCompare (matrix state ++ leftExit)
      (matrix (encode d (Parents.annotate d source (.cons a hs tail)) visible state) ++ rightExit) = .lt := by
  obtain ⟨height, tag, rest, _, shape⟩ := encode_cons_first_row d (Parents.label d source a)
    (Parents.annotateForests d (source ++ [Parents.label d source a]) hs)
    (Parents.annotate d (source ++ [Parents.label d source a]) tail) visible state
  change matrixCompare (matrix state ++ leftExit)
    (matrix (encode d (.cons (Parents.label d source a)
      (Parents.annotateForests d (source ++ [Parents.label d source a]) hs)
      (Parents.annotate d (source ++ [Parents.label d source a]) tail)) visible state) ++ rightExit) = .lt
  rw [shape, List.append_assoc, List.cons_append]
  simp only [matrixCompare, listCompare_common_prefix (listCompare Ord.compare) columnCompare_self]
  cases leftExit with
  | nil => rfl
  | cons head more =>
    obtain ⟨bound, selected, width, value⟩ := low
    cases floor with
    | none => simp at selected
    | some pair =>
      obtain ⟨s, t⟩ := pair
      have equal : t = bound := by simpa using selected
      obtain ⟨root, inside, sourceValue, path, targetValue⟩ := fence
      have high := vector_above_fence state positive coherent valid view inside path a (by
        rw [sourceValue]; exact above s t rfl)
      rw [targetValue] at high
      have first : listCompare Ord.compare head
          (row d (vector state visible (Parents.label d source a)) height tag) = .lt := by
        apply columnCompare_lt_of_zero width (by rw [row_width]; omega)
        rw [row_numerical_reading d _ height tag 0 positive]
        omega
      simp only [listCompare, first]

theorem encodeForests_extension_low (d : Nat) (hs : Forests ParentLabel)
    (visible : List Nat) (u : Nat → Nat) (c : Nat) (below : List Binding) (state : State d)
    (positive : 0 < d) (exit : Matrix) (low : ExitBelow (some (u 0 + 2)) exit) :
    ∃ extra, matrix (encodeForests d hs visible u c below state) ++ exit = matrix state ++ extra ∧
      ExitBelow (some (u 0 + 2)) extra := by
  cases hs with
  | nil => exact ⟨exit, rfl, low⟩
  | cons h hs =>
    have extended := (encode_extends d h (visible ++ [state.length])
      (emit state (fun j => u j + 2) (c + 2) 0 below)).trans
      (encodeForests_extends d hs visible u c below _)
    obtain ⟨added, shape⟩ := matrix_extension extended
    refine ⟨row d (fun j => u j + 2) (c + 2) 0 :: (added ++ exit), ?_, ?_⟩
    · change matrix (encodeForests d hs visible u c below
        (encode d h (visible ++ [state.length]) (emit state (fun j => u j + 2) (c + 2) 0 below))) ++ exit = _
      rw [shape, matrix_emit]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    · exact ⟨u 0 + 2, rfl, by rw [row_width]; omega,
        by rw [row_numerical_reading d _ (c + 2) 0 0 positive]; exact Nat.le_refl _⟩

theorem encode_cons_close_extension (d : Nat) (a : ParentLabel) (hs : Forests ParentLabel)
    (tail : ParentExpr) (visible : List Nat) (state : State d) (positive : 0 < d)
    (fresh : equal (frameAt state (representative visible a (d - 1)))
      (Keys.ofColumn d visible.length a hs) = none) (exit : Matrix) :
    let u := vector state visible a
    let below := smaller (frameAt state (representative visible a (d - 1))) (Keys.ofColumn d visible.length a hs)
    let c := (base below).height
    let guarded := emit (emit state u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 []
    ∃ extra, matrix (encode d (.cons a hs tail) visible state) ++ exit =
        matrix (encodeForests d hs visible u c below guarded) ++ extra ∧
      ExitBelow (some (u 0 + 1)) extra := by
  dsimp only
  rw [encode, fresh]
  obtain ⟨added, shape⟩ := matrix_extension (encode_extends d tail _ _)
  refine ⟨row d (fun j => vector state visible a j + 1)
    ((base (smaller (frameAt state (representative visible a (d - 1)))
      (Keys.ofColumn d visible.length a hs))).height + 2) 0 :: (added ++ exit), ?_, ?_⟩
  · rw [shape, matrix_emit]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  · exact ⟨vector state visible a 0 + 1, rfl, by rw [row_width]; omega,
      by rw [row_numerical_reading d _ _ 0 0 positive]; exact Nat.le_refl _⟩

theorem encode_first_lt_of_numerical_heads {d : Nat} {source : ParentContext} {visible : List Nat}
    (state : State d) (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (a b : List Nat) (ha : a.length = d) (hb : b.length = d)
    (leftUnit : Parents.UnitSteps d (source ++ [Parents.label d source a]))
    (rightUnit : Parents.UnitSteps d (source ++ [Parents.label d source b]))
    (lower : listCompare Ord.compare a b = .lt)
    (hs ks : Forests (List Nat)) (tail rest : NumericalExpr) :
    MatrixFirstLt (matrix (encode d (Parents.annotate d source (.cons a hs tail)) visible state))
      (matrix (encode d (Parents.annotate d source (.cons b ks rest)) visible state)) := by
  obtain ⟨j, inside, common, strict⟩ := columnCompare_lt_exists_difference a b (ha.trans hb.symm) lower
  obtain ⟨heightA, tagA, extraA, _, shapeA⟩ := encode_cons_first_row d (Parents.label d source a)
    (Parents.annotateForests d (source ++ [Parents.label d source a]) hs)
    (Parents.annotate d (source ++ [Parents.label d source a]) tail) visible state
  obtain ⟨heightB, tagB, extraB, _, shapeB⟩ := encode_cons_first_row d (Parents.label d source b)
    (Parents.annotateForests d (source ++ [Parents.label d source b]) ks)
    (Parents.annotate d (source ++ [Parents.label d source b]) rest) visible state
  exact ⟨matrix state, _, _, extraA, extraB, shapeA, shapeB,
    head_row_lt_at_numerical_difference state coherent valid view a b leftUnit rightUnit
      (by omega : j < d) common strict heightA tagA heightB tagB⟩

theorem encode_first_lt_of_height (d : Nat) (a : ParentLabel)
    (hs ks : Forests ParentLabel) (tail rest : ParentExpr) (visible : List Nat) (state : State d)
    (strict : firstHeight (frameAt state (representative visible a (d - 1)))
        (Keys.ofColumn d visible.length a hs) <
      firstHeight (frameAt state (representative visible a (d - 1)))
        (Keys.ofColumn d visible.length a ks)) :
    MatrixFirstLt (matrix (encode d (.cons a hs tail) visible state))
      (matrix (encode d (.cons a ks rest) visible state)) := by
  obtain ⟨heightA, tagA, extraA, firstA, shapeA⟩ := encode_cons_first_row d a hs tail visible state
  obtain ⟨heightB, tagB, extraB, firstB, shapeB⟩ := encode_cons_first_row d a ks rest visible state
  refine ⟨matrix state, _, _, extraA, extraB, shapeA, shapeB, ?_⟩
  apply columnCompare_lt_at _ _ d (by rw [row_width]; omega) (by rw [row_width]; omega)
  · intro j room
    rw [row_numerical_reading d _ heightA tagA j room, row_numerical_reading d _ heightB tagB j room]
  · rw [row_key_reading, row_key_reading, firstA, firstB]
    exact strict

end BTnSSBMS.Encoder
