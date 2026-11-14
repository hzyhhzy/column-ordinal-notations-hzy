import BTnSSBMS.Environment

/-!
Saved binding pointers refer to real emitted columns, not just abstract
stack entries. A definition has tag 1 and height one below its binding;
the latest actual column has tag 0 and exactly the binding's height.
The definition precedes every latest representative, including after reuse.

These are invariants of the real recursive encoder on all finite inputs.
They do not by themselves identify those references with computed BMS parents.
-/
namespace BTnSSBMS.Encoder

def Readout (state : State d) (position height tag : Nat) : Prop :=
  ∃ col, state[position]? = some col ∧
    col.values[d]? = some height ∧ col.values[d + 1]? = some tag

def BindingRealized (state : State d) (b : Binding) : Prop :=
  (match b.latest with
   | none => b.height = 0 ∧ b.definition = none
   | some p => Readout state p b.height 0) ∧
  (match b.definition with
   | none => b.height = 0
   | some p => ∃ h, b.height = h + 1 ∧ Readout state p h 1) ∧
  (∀ p q, b.definition = some p → b.latest = some q → p < q)

def FrameRealized (state : State d) (frame : List Binding) : Prop :=
  ∀ b ∈ frame, BindingRealized state b

/-- Each saved frame is realized already at the point where it is saved.
This rules out forward pointers, even if a later extension happens to add
a column with the requested height. -/
def FramesRealized (state : State d) : Prop :=
  ∀ i col, state[i]? = some col → FrameRealized (state.take (i + 1)) col.frame

theorem readout_extends {state next : State d} (initial : state <+: next)
    {position height tag : Nat} (h : Readout state position height tag) :
    Readout next position height tag := by
  obtain ⟨rest, rfl⟩ := initial
  obtain ⟨col, lookup, key, label⟩ := h
  have bound := (List.getElem?_eq_some_iff.mp lookup).choose
  exact ⟨col, by rw [List.getElem?_append_left bound]; exact lookup, key, label⟩

theorem readout_bound {state : State d} {position height tag : Nat}
    (h : Readout state position height tag) : position < state.length := by
  obtain ⟨col, lookup, _, _⟩ := h
  exact (List.getElem?_eq_some_iff.mp lookup).choose

theorem readout_emit (state : State d) (u : Nat → Nat) (height tag : Nat)
    (frame : List Binding) : Readout (emit state u height tag frame) state.length height tag := by
  refine ⟨⟨row d u height tag, row_width d u height tag, frame⟩,
    List.getElem?_concat_length, ?_, ?_⟩
  · simp [row]
  · simp [row]

theorem bindingRealized_extends {state next : State d} (initial : state <+: next)
    {b : Binding} (h : BindingRealized state b) : BindingRealized next b := by
  obtain ⟨latest, definition, earlier⟩ := h
  refine ⟨?_, ?_, earlier⟩
  · cases hl : b.latest with
    | none => simpa only [hl] using latest
    | some p => exact readout_extends initial (by simpa only [hl] using latest)
  · cases hd : b.definition with
    | none => simpa only [hd] using definition
    | some p =>
      simp only [hd] at definition
      obtain ⟨height, same, output⟩ := definition
      exact ⟨height, same, readout_extends initial output⟩

theorem frameRealized_extends {state next : State d} (initial : state <+: next)
    {frame : List Binding} (h : FrameRealized state frame) : FrameRealized next frame := by
  intro b hb
  exact bindingRealized_extends initial (h b hb)

theorem empty_frame_realized (state : State d) : FrameRealized state [] := by
  intro b hb
  simp at hb

theorem virtual_frame_realized (state : State d) : FrameRealized state virtualFrame := by
  intro b hb
  have same : b = zeroBinding := by simpa [virtualFrame] using hb
  subst b
  simp [BindingRealized, zeroBinding]

theorem smaller_realized {state : State d} {frame : List Binding}
    (h : FrameRealized state frame) (key : Key) : FrameRealized state (smaller frame key) := by
  intro b hb
  exact h b (List.mem_filter.mp hb).1

theorem queried_frame_realized {state : State d} (h : FramesRealized state)
    (position : Option Nat) : FrameRealized state (frameAt state position) := by
  unfold frameAt
  cases output : position.bind (state[·]?) with
  | none => exact virtual_frame_realized _
  | some col =>
    obtain ⟨p, _, lookup⟩ := Option.bind_eq_some_iff.mp output
    exact frameRealized_extends (List.take_prefix ..) (h p col lookup)

theorem framesRealized_emit {state : State d} (h : FramesRealized state)
    (u : Nat → Nat) (height tag : Nat) (frame : List Binding)
    (added : FrameRealized (emit state u height tag frame) frame) :
    FramesRealized (emit state u height tag frame) := by
  intro i col lookup
  by_cases old : i < state.length
  · rw [emit, List.getElem?_append_left old] at lookup
    have prefixSame : (emit state u height tag frame).take (i + 1) = state.take (i + 1) := by
      rw [emit, List.take_append_of_le_length (by omega)]
    rw [prefixSame]
    exact h i col lookup
  · have bound := (List.getElem?_eq_some_iff.mp lookup).choose
    have atEnd : i = state.length := by simp only [emit_length] at bound; omega
    subst i
    have same : col = ⟨row d u height tag, row_width d u height tag, frame⟩ := by
      simpa only [emit, List.getElem?_concat_length, Option.some.injEq] using lookup.symm
    subst col
    simpa only [← emit_length state u height tag frame, List.take_length] using added

theorem reused_frame_realized {state : State d} {frame : List Binding}
    (h : FrameRealized state frame) (key : Key) (bound : Binding)
    (found : equal frame key = some bound) (u : Nat → Nat) :
    FrameRealized
      (emit state u bound.height 0 (smaller frame key ++ [{bound with latest := some state.length}]))
      (smaller frame key ++ [{bound with latest := some state.length}]) := by
  intro b hb
  rcases List.mem_append.mp hb with old | new
  · exact bindingRealized_extends (emit_extends ..) (smaller_realized h key b old)
  · have same : b = {bound with latest := some state.length} := by simpa using new
    subst b
    have known := h bound (List.mem_of_find?_eq_some found)
    refine ⟨readout_emit .., ?_, ?_⟩
    · exact (bindingRealized_extends (emit_extends ..) known).2.1
    · intro p q definition latest
      have atEnd : q = state.length := by simpa using latest.symm
      subst q
      have proof := known.2.1
      rw [definition] at proof
      obtain ⟨_, _, output⟩ := proof
      exact readout_bound output

theorem fresh_frame_realized {state : State d} (below : List Binding)
    (known : FrameRealized state below) (key : Key) (height definition : Nat)
    (witness : Readout state definition (height + 1) 1) (u : Nat → Nat) :
    FrameRealized
      (emit state u (height + 2) 0 (below ++ [⟨key, height + 2, some state.length, some definition⟩]))
      (below ++ [⟨key, height + 2, some state.length, some definition⟩]) := by
  intro b hb
  rcases List.mem_append.mp hb with old | new
  · exact bindingRealized_extends (emit_extends ..) (known b old)
  · have same : b = ⟨key, height + 2, some state.length, some definition⟩ := by simpa using new
    subst b
    refine ⟨readout_emit .., ⟨height + 1, rfl, readout_extends (emit_extends ..) witness⟩, ?_⟩
    intro p q hp hq
    have pSame : p = definition := by simpa using hp.symm
    have qSame : q = state.length := by simpa using hq.symm
    subst p; subst q
    exact readout_bound witness

mutual
  theorem encode_framesRealized (d : Nat) (e : ParentExpr) (visible : List Nat) (state : State d)
      (known : FramesRealized state) : FramesRealized (encode d e visible state) := by
    cases e with
    | nil => exact known
    | cons a hs t =>
      have frameKnown := queried_frame_realized known (representative visible a (d - 1))
      have belowKnown := smaller_realized frameKnown (Keys.ofColumn d visible.length a hs)
      simp only [encode]
      split
      next bound found =>
        apply encode_framesRealized d t
        exact framesRealized_emit known _ _ _ _ (reused_frame_realized frameKnown _ bound found _)
      next fresh =>
        let key := Keys.ofColumn d visible.length a hs
        let below := smaller (frameAt state (representative visible a (d - 1))) key
        let c := (base below).height
        let u := vector state visible a
        let withDefinition := emit state u (c + 1) 1 []
        let withGuard := emit withDefinition (fun j => u j + 1) (c + 2) 2 []
        let withForests := encodeForests d hs visible u c below withGuard
        have guardKnown : FramesRealized withGuard :=
          framesRealized_emit (framesRealized_emit known _ _ _ [] (empty_frame_realized _))
            _ _ _ [] (empty_frame_realized _)
        have toGuard : state <+: withGuard := (emit_extends ..).trans (emit_extends ..)
        have toForests : withGuard <+: withForests := encodeForests_extends ..
        have forestsKnown := encodeForests_framesRealized d hs visible u c below withGuard
          (frameRealized_extends toGuard belowKnown) guardKnown
        apply encode_framesRealized d t
        apply framesRealized_emit forestsKnown
        apply fresh_frame_realized below (frameRealized_extends (toGuard.trans toForests) belowKnown)
        exact readout_extends ((emit_extends ..).trans toForests) (readout_emit state u (c + 1) 1 [])
  theorem encodeForests_framesRealized (d : Nat) (hs : Forests ParentLabel) (visible : List Nat)
      (u : Nat → Nat) (c : Nat) (below : List Binding) (state : State d)
      (belowKnown : FrameRealized state below) (known : FramesRealized state) :
      FramesRealized (encodeForests d hs visible u c below state) := by
    cases hs with
    | nil => exact known
    | cons h hs =>
      have slotKnown := framesRealized_emit known (fun j => u j + 2) (c + 2) 0 below
        (frameRealized_extends (emit_extends ..) belowKnown)
      apply encodeForests_framesRealized d hs
      · exact frameRealized_extends ((emit_extends ..).trans (encode_extends d h _ _)) belowKnown
      · exact encode_framesRealized d h _ _ slotKnown
end

theorem source_framesRealized (d : Nat) (e : NumericalExpr) :
    FramesRealized (encode d (Parents.annotate d [] e) [] []) :=
  encode_framesRealized d _ [] [] (by intro i col lookup; simp at lookup)

end BTnSSBMS.Encoder
