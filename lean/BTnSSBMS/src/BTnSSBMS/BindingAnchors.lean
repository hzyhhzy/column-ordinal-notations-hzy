import BTnSSBMS.FrameReferences

/-!
Every latest-position pointer names an actual column that saved itself as
a latest position. In particular a forest slot, which only saves an older
frame, cannot later turn into such a representative. This concerns saved
finite data, not assumed source or target ancestry.
-/
namespace BTnSSBMS.Encoder

def SelfLatest (state : State d) (position : Nat) : Prop :=
  ∃ col, state[position]? = some col ∧ ∃ b ∈ col.frame, b.latest = some position

def FrameSelfLatest (state : State d) (frame : List Binding) : Prop :=
  ∀ b ∈ frame, ∀ p, b.latest = some p → SelfLatest state p

def FramesSelfLatest (state : State d) : Prop :=
  ∀ col ∈ state, FrameSelfLatest state col.frame

theorem SelfLatest.extends {state next : State d} {position : Nat}
    (self : SelfLatest state position) (extended : state <+: next) : SelfLatest next position := by
  obtain ⟨extra, rfl⟩ := extended
  obtain ⟨col, lookup, binding⟩ := self
  have inside := (List.getElem?_eq_some_iff.mp lookup).choose
  exact ⟨col, by rw [List.getElem?_append_left inside]; exact lookup, binding⟩

theorem SelfLatest.restrict {state next : State d} {position : Nat}
    (self : SelfLatest next position) (extended : state <+: next) (inside : position < state.length) :
    SelfLatest state position := by
  obtain ⟨extra, rfl⟩ := extended
  obtain ⟨col, lookup, binding⟩ := self
  exact ⟨col, by simpa only [List.getElem?_append_left inside] using lookup, binding⟩

theorem FrameSelfLatest.extends {state next : State d} {frame : List Binding}
    (self : FrameSelfLatest state frame) (extended : state <+: next) : FrameSelfLatest next frame :=
  fun b member p found => (self b member p found).extends extended

theorem empty_frame_selfLatest (state : State d) : FrameSelfLatest state [] := by
  intro b member
  simp at member

theorem virtual_frame_selfLatest (state : State d) : FrameSelfLatest state virtualFrame := by
  intro b member p found
  have same : b = zeroBinding := by simpa only [virtualFrame, List.mem_singleton] using member
  simp only [same, zeroBinding] at found
  cases found

theorem smaller_selfLatest {state : State d} {frame : List Binding}
    (self : FrameSelfLatest state frame) (key : Key) : FrameSelfLatest state (smaller frame key) :=
  fun b member p found => self b (List.mem_filter.mp member).1 p found

theorem queried_frame_selfLatest {state : State d} (self : FramesSelfLatest state)
    (position : Option Nat) : FrameSelfLatest state (frameAt state position) := by
  unfold frameAt
  cases found : position.bind (state[·]?) with
  | none => exact virtual_frame_selfLatest state
  | some col =>
    obtain ⟨p, _, lookup⟩ := Option.bind_eq_some_iff.mp found
    exact self col (List.mem_of_getElem? lookup)

theorem framesSelfLatest_emit {state : State d} (self : FramesSelfLatest state)
    (u : Nat → Nat) (height tag : Nat) (frame : List Binding)
    (added : FrameSelfLatest (emit state u height tag frame) frame) :
    FramesSelfLatest (emit state u height tag frame) := by
  intro col member
  rcases List.mem_append.mp member with old | new
  · exact (self col old).extends (emit_extends ..)
  · have same : col = ⟨row d u height tag, row_width d u height tag, frame⟩ := by simpa using new
    subst col
    exact added

theorem selfLatest_emit (state : State d) (u : Nat → Nat) (height tag : Nat)
    (frame : List Binding) (b : Binding) (member : b ∈ frame) (latest : b.latest = some state.length) :
    SelfLatest (emit state u height tag frame) state.length :=
  ⟨⟨row d u height tag, row_width d u height tag, frame⟩, List.getElem?_concat_length,
    b, member, latest⟩

theorem updated_frame_selfLatest {state : State d} {frame : List Binding}
    (self : FrameSelfLatest state frame) (b : Binding) (latest : b.latest = some state.length)
    (u : Nat → Nat) (height tag : Nat) :
    FrameSelfLatest (emit state u height tag (frame ++ [b])) (frame ++ [b]) := by
  intro x member p found
  rcases List.mem_append.mp member with old | added
  · exact (self x old p found).extends (emit_extends ..)
  · have same : x = b := by simpa using added
    subst x
    have atEnd : p = state.length := Option.some.inj (found.symm.trans latest)
    subst p
    exact selfLatest_emit state u height tag (frame ++ [b]) b
      (List.mem_append_right _ (by simp)) latest

mutual
  theorem encode_framesSelfLatest (d : Nat) (e : ParentExpr) (visible : List Nat) (state : State d)
      (self : FramesSelfLatest state) : FramesSelfLatest (encode d e visible state) := by
    cases e with
    | nil => exact self
    | cons a hs tail =>
      have frameSelf := queried_frame_selfLatest self (representative visible a (d - 1))
      have belowSelf := smaller_selfLatest frameSelf (Keys.ofColumn d visible.length a hs)
      simp only [encode]
      split
      next bound found =>
        apply encode_framesSelfLatest d tail
        apply framesSelfLatest_emit self
        exact updated_frame_selfLatest belowSelf {bound with latest := some state.length} rfl _ _ _
      next fresh =>
        let key := Keys.ofColumn d visible.length a hs
        let below := smaller (frameAt state (representative visible a (d - 1))) key
        let c := (base below).height
        let u := vector state visible a
        let guarded := emit (emit state u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 []
        let forests := encodeForests d hs visible u c below guarded
        have guardSelf : FramesSelfLatest guarded := framesSelfLatest_emit
          (framesSelfLatest_emit self u (c + 1) 1 [] (empty_frame_selfLatest _))
          (fun j => u j + 1) (c + 2) 2 [] (empty_frame_selfLatest _)
        have guardExtends : state <+: guarded := (emit_extends ..).trans (emit_extends ..)
        have forestExtends : guarded <+: forests := encodeForests_extends ..
        have forestSelf := encodeForests_framesSelfLatest d hs visible u c below guarded
          (belowSelf.extends guardExtends) guardSelf
        apply encode_framesSelfLatest d tail
        apply framesSelfLatest_emit forestSelf
        exact updated_frame_selfLatest (belowSelf.extends (guardExtends.trans forestExtends))
          ⟨key, c + 2, some forests.length, some state.length⟩ rfl _ _ _

  theorem encodeForests_framesSelfLatest (d : Nat) (hs : Forests ParentLabel) (visible : List Nat)
      (u : Nat → Nat) (c : Nat) (below : List Binding) (state : State d)
      (belowSelf : FrameSelfLatest state below) (self : FramesSelfLatest state) :
      FramesSelfLatest (encodeForests d hs visible u c below state) := by
    cases hs with
    | nil => exact self
    | cons h hs =>
      have slotSelf := framesSelfLatest_emit self (fun j => u j + 2) (c + 2) 0 below
        (belowSelf.extends (emit_extends ..))
      apply encodeForests_framesSelfLatest d hs
      · exact belowSelf.extends ((emit_extends ..).trans (encode_extends d h _ _))
      · exact encode_framesSelfLatest d h _ _ slotSelf
end

theorem source_framesSelfLatest (d : Nat) (e : NumericalExpr) :
    FramesSelfLatest (encode d (Parents.annotate d [] e) [] []) :=
  encode_framesSelfLatest d _ [] [] (by intro col member; simp at member)

end BTnSSBMS.Encoder
