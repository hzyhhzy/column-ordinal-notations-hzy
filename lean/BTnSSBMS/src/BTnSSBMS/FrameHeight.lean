import BTnSSBMS.FrameOrder

/-!
The paper's exact height convention is an invariant of the real code:
the binding at stack position i has height 2*i. Filtering a saved frame
really truncates a prefix; it does not leave unaccounted-for height gaps.
-/
namespace BTnSSBMS.Encoder

def FrameDense (frame : List Binding) : Prop :=
  ∀ i b, frame[i]? = some b → b.height = 2 * i

def FramesDense (state : State d) : Prop := ∀ col ∈ state, FrameDense col.frame

theorem empty_frame_dense : FrameDense [] := by
  intro i b lookup
  simp at lookup

theorem virtual_frame_dense : FrameDense virtualFrame := by
  intro i b lookup
  cases i with
  | zero => have same : b = zeroBinding := by simpa [virtualFrame] using lookup.symm
            subst b; rfl
  | succ i => simp [virtualFrame] at lookup

theorem frameDense_prefix {small large : List Binding} (dense : FrameDense large)
    (initial : small <+: large) : FrameDense small := by
  obtain ⟨rest, rfl⟩ := initial
  intro i b lookup
  have bound := (List.getElem?_eq_some_iff.mp lookup).choose
  apply dense i b
  rw [List.getElem?_append_left bound]
  exact lookup

theorem frameDense_append (frame : List Binding) (dense : FrameDense frame)
    (b : Binding) (height : b.height = 2 * frame.length) : FrameDense (frame ++ [b]) := by
  intro i a lookup
  by_cases old : i < frame.length
  · rw [List.getElem?_append_left old] at lookup
    exact dense i a lookup
  · rw [List.getElem?_append_right (Nat.le_of_not_gt old)] at lookup
    cases index : i - frame.length with
    | zero =>
      have atEnd : i = frame.length := by omega
      have same : a = b := by simpa [index] using lookup.symm
      subst a; simpa only [atEnd] using height
    | succ j => simp [index] at lookup

theorem base_height_next {frame : List Binding} (dense : FrameDense frame)
    (nonempty : frame ≠ []) : (base frame).height + 2 = 2 * frame.length := by
  have lookup : frame[frame.length - 1]? = some (base frame) := by
    rw [← List.getLast?_eq_getElem?, List.getLast?_eq_some_getLast nonempty]
    simp only [base, List.getLast?_eq_some_getLast nonempty, Option.getD_some]
  have height := dense _ _ lookup
  have positive : 0 < frame.length := List.length_pos_iff.mpr nonempty
  omega

theorem fresh_frame_dense {frame : List Binding} (ordered : FrameOrdered frame)
    (dense : FrameDense frame) (key : Key) (nonempty : smaller frame key ≠ [])
    (latest definition : Option Nat) :
    FrameDense (smaller frame key ++
      [⟨key, (base (smaller frame key)).height + 2, latest, definition⟩]) := by
  have below := frameDense_prefix dense (smaller_prefix ordered key)
  exact frameDense_append _ below _ (base_height_next below nonempty)

theorem reused_frame_dense {frame : List Binding} (ordered : FrameOrdered frame)
    (dense : FrameDense frame) (key : Key) (bound : Binding)
    (found : equal frame key = some bound) (p : Nat) :
    FrameDense (smaller frame key ++ [{bound with latest := some p}]) := by
  have cut := frameDense_prefix dense (equal_cut_prefix ordered key bound found)
  have boundHeight := cut (smaller frame key).length bound List.getElem?_concat_length
  exact frameDense_append _ (frameDense_prefix dense (smaller_prefix ordered key)) _ boundHeight

theorem framesDense_emit {state : State d} (dense : FramesDense state)
    (u : Nat → Nat) (height tag : Nat) (frame : List Binding)
    (frameDense : FrameDense frame) : FramesDense (emit state u height tag frame) := by
  intro col hc
  rcases List.mem_append.mp hc with old | added
  · exact dense col old
  · have same : col = ⟨row d u height tag, row_width d u height tag, frame⟩ := by
      simpa using added
    exact same ▸ frameDense

theorem queried_frame_dense {state : State d} (dense : FramesDense state)
    (position : Option Nat) : FrameDense (frameAt state position) := by
  unfold frameAt
  cases h : position.bind (state[·]?) with
  | none => exact virtual_frame_dense
  | some col =>
    obtain ⟨p, _, lookup⟩ := Option.bind_eq_some_iff.mp h
    exact dense col (List.mem_of_getElem? lookup)

mutual
  theorem encode_framesDense (d : Nat) (e : ParentExpr) (visible : List Nat) (state : State d)
      (ordered : FramesOrdered state) (dense : FramesDense state)
      (safe : NoFallback d e visible state) : FramesDense (encode d e visible state) := by
    cases e with
    | nil => exact dense
    | cons a hs t =>
      have frameOrder := queried_frame_ordered ordered (representative visible a (d - 1))
      have frameDense := queried_frame_dense dense (representative visible a (d - 1))
      simp only [encode, NoFallback] at safe ⊢
      split at safe
      next bound found =>
        rw [found]
        apply encode_framesDense d t
        · exact framesOrdered_emit ordered _ _ _ _ (reused_frame_ordered frameOrder _ bound found _)
        · exact framesDense_emit dense _ _ _ _ (reused_frame_dense frameOrder frameDense _ bound found _)
        · exact safe
      next fresh =>
        rw [fresh]
        obtain ⟨nonempty, forestSafe, tailSafe⟩ := safe
        have belowOrdered := smaller_ordered frameOrder (Keys.ofColumn d visible.length a hs)
        have belowDense := frameDense_prefix frameDense
          (smaller_prefix frameOrder (Keys.ofColumn d visible.length a hs))
        let c := (base (smaller (frameAt state (representative visible a (d - 1)))
          (Keys.ofColumn d visible.length a hs))).height
        have guardOrdered := framesOrdered_emit
          (framesOrdered_emit ordered (vector state visible a) (c + 1) 1 [] (by simp [FrameOrdered]))
          (fun j => vector state visible a j + 1) (c + 2) 2 [] (by simp [FrameOrdered])
        have guardDense := framesDense_emit
          (framesDense_emit dense (vector state visible a) (c + 1) 1 [] empty_frame_dense)
          (fun j => vector state visible a j + 1) (c + 2) 2 [] empty_frame_dense
        apply encode_framesDense d t
        · apply framesOrdered_emit
          · exact encodeForests_framesOrdered d hs _ _ _ _ _ belowOrdered guardOrdered
          · exact fresh_frame_ordered frameOrder _ _ _
        · apply framesDense_emit
          · exact encodeForests_framesDense d hs _ _ _ _ _
              belowOrdered belowDense guardOrdered guardDense forestSafe
          · exact fresh_frame_dense frameOrder frameDense _ nonempty _ _
        · exact tailSafe
  theorem encodeForests_framesDense (d : Nat) (hs : Forests ParentLabel) (visible : List Nat)
      (u : Nat → Nat) (c : Nat) (below : List Binding) (state : State d)
      (belowOrdered : FrameOrdered below) (belowDense : FrameDense below)
      (ordered : FramesOrdered state) (dense : FramesDense state)
      (safe : NoFallbackForests d hs visible u c below state) :
      FramesDense (encodeForests d hs visible u c below state) := by
    cases hs with
    | nil => exact dense
    | cons h hs =>
      obtain ⟨childSafe, restSafe⟩ := safe
      have slotOrdered := framesOrdered_emit ordered (fun j => u j + 2) (c + 2) 0 below belowOrdered
      have slotDense := framesDense_emit dense (fun j => u j + 2) (c + 2) 0 below belowDense
      apply encodeForests_framesDense d hs _ _ _ _ _ belowOrdered belowDense
      · exact encode_framesOrdered d h _ _ slotOrdered
      · exact encode_framesDense d h _ _ slotOrdered slotDense childSafe
      · exact restSafe
end

theorem source_framesDense (d : Nat) (e : NumericalExpr) :
    FramesDense (encode d (Parents.annotate d [] e) [] []) :=
  encode_framesDense d _ [] [] (by intro col member; simp at member)
    (by intro col member; simp at member) (source_noFallback d e)

end BTnSSBMS.Encoder
