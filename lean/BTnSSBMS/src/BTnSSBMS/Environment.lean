import BTnSSBMS.Encoder
import BTnSSBMS.KeyEquality
import Init.Data.List.Find

/-!
The zero binding is available throughout the actual encoder execution.
This is an invariant of the executable mutually recursive encoder, not a
hypothesis that the final order embedding can simply assume. It holds even
for arbitrary raw source annotations, provided incoming visible positions
carry a zero binding. No numerical legality assumption is needed here.
-/
namespace BTnSSBMS.Encoder

def HasZero (frame : List Binding) : Prop := ∃ b ∈ frame, b.key = .nil

def VisibleGood (state : State d) (visible : List Nat) : Prop :=
  ∀ p ∈ visible, ∃ col, state[p]? = some col ∧ HasZero col.frame

theorem virtual_has_zero : HasZero virtualFrame := ⟨zeroBinding, by simp [virtualFrame], rfl⟩

theorem hasZero_append {xs ys : List Binding} (h : HasZero xs) : HasZero (xs ++ ys) := by
  obtain ⟨b, hb, hk⟩ := h
  exact ⟨b, List.mem_append_left _ hb, hk⟩

theorem hasZero_nonempty {frame : List Binding} (h : HasZero frame) : frame ≠ [] := by
  obtain ⟨b, hb, _⟩ := h
  intro eq
  simp [eq] at hb

theorem smaller_has_zero {frame : List Binding} (h : HasZero frame)
    (key : Key) (nonempty : key ≠ .nil) : HasZero (smaller frame key) := by
  obtain ⟨b, hb, hk⟩ := h
  refine ⟨b, List.mem_filter.mpr ⟨hb, ?_⟩, hk⟩
  cases key with
  | nil => exact False.elim (nonempty rfl)
  | cons x xs => simp [hk, Keys.compare, Forests.compare]

theorem fresh_key_nonempty {frame : List Binding} (h : HasZero frame)
    (key : Key) (fresh : equal frame key = none) : key ≠ .nil := by
  intro empty
  obtain ⟨b, hb, hk⟩ := h
  have absent := List.find?_eq_none.mp fresh b hb
  simp [empty, hk, Keys.compare, Forests.compare] at absent

theorem fresh_smaller_has_zero {frame : List Binding} (h : HasZero frame)
    (key : Key) (fresh : equal frame key = none) : HasZero (smaller frame key) :=
  smaller_has_zero h key (fresh_key_nonempty h key fresh)

theorem reused_frame_has_zero {frame : List Binding} (h : HasZero frame)
    (key : Key) (bound : Binding) (same : equal frame key = some bound) (p : Nat) :
    HasZero (smaller frame key ++ [{bound with latest := some p}]) := by
  by_cases empty : key = .nil
  · have compared : Keys.compare bound.key key = .eq := by
      simpa only [beq_iff_eq] using List.find?_some same
    have bk : bound.key = .nil := (Keys.compare_eq_imp _ _ compared).trans empty
    exact ⟨{bound with latest := some p}, List.mem_append_right _ (by simp), bk⟩
  · exact hasZero_append (smaller_has_zero h key empty)

theorem visibleGood_extends {state next : State d} (extended : state <+: next)
    {visible : List Nat} (good : VisibleGood state visible) : VisibleGood next visible := by
  obtain ⟨added, rfl⟩ := extended
  intro p hp
  obtain ⟨col, lookup, hz⟩ := good p hp
  have bound := (List.getElem?_eq_some_iff.mp lookup).choose
  exact ⟨col, by rw [List.getElem?_append_left bound]; exact lookup, hz⟩

theorem visibleGood_emit (state : State d) (visible : List Nat)
    (good : VisibleGood state visible) (u : Nat → Nat) (height tag : Nat)
    (frame : List Binding) (hz : HasZero frame) :
    VisibleGood (emit state u height tag frame) (visible ++ [state.length]) := by
  intro p hp
  rcases List.mem_append.mp hp with old | added
  · exact visibleGood_extends (emit_extends ..) good p old
  · have same : p = state.length := by simpa using added
    subst p
    exact ⟨⟨row d u height tag, row_width d u height tag, frame⟩,
      List.getElem?_concat_length, hz⟩

theorem queried_frame_has_zero (state : State d) (visible : List Nat)
    (good : VisibleGood state visible) (a : ParentLabel) (j : Nat) :
    HasZero (frameAt state (representative visible a j)) := by
  unfold representative
  cases parent : a.parents[j]?.join with
  | none => exact virtual_has_zero
  | some p =>
    cases position : visible[p]? with
    | none => simpa only [Option.bind_some, position, frameAt, Option.bind_none] using virtual_has_zero
    | some q =>
      obtain ⟨col, lookup, hz⟩ := good q (List.mem_of_getElem? position)
      simpa only [Option.bind_some, position, frameAt, lookup] using hz

mutual
  def NoFallback (d : Nat) (e : ParentExpr) (visible : List Nat) (state : State d) : Prop :=
    match e with
    | .nil => True
    | .cons a hs t =>
      let key := Keys.ofColumn d visible.length a hs
      let u := vector state visible a
      let frame := frameAt state (representative visible a (d - 1))
      let below := smaller frame key
      match equal frame key with
      | some bound =>
        NoFallback d t (visible ++ [state.length])
          (emit state u bound.height 0 (below ++ [{bound with latest := some state.length}]))
      | none =>
        let c := (base below).height
        let withGuard := emit (emit state u (c + 1) 1) (fun j => u j + 1) (c + 2) 2
        let withForests := encodeForests d hs visible u c below withGuard
        below ≠ [] ∧ NoFallbackForests d hs visible u c below withGuard ∧
          NoFallback d t (visible ++ [withForests.length])
            (emit withForests (fun j => u j + 1) (c + 2) 0
              (below ++ [⟨key, c + 2, some withForests.length, some state.length⟩]))
  def NoFallbackForests (d : Nat) (hs : Forests ParentLabel) (visible : List Nat)
      (u : Nat → Nat) (c : Nat) (below : List Binding) (state : State d) : Prop :=
    match hs with
    | .nil => True
    | .cons h hs =>
      let withSlot := emit state (fun j => u j + 2) (c + 2) 0 below
      NoFallback d h (visible ++ [state.length]) withSlot ∧
        NoFallbackForests d hs visible u c below (encode d h (visible ++ [state.length]) withSlot)
end

mutual
  theorem encode_noFallback (d : Nat) (e : ParentExpr) (visible : List Nat) (state : State d)
      (good : VisibleGood state visible) : NoFallback d e visible state := by
    cases e with
    | nil => trivial
    | cons a hs t =>
      have hz := queried_frame_has_zero state visible good a (d - 1)
      simp only [NoFallback]
      split
      next bound same =>
        apply encode_noFallback d t
        exact visibleGood_emit state visible good _ _ _ _ (reused_frame_has_zero hz _ bound same _)
      next fresh =>
        have belowGood := fresh_smaller_has_zero hz _ fresh
        refine ⟨hasZero_nonempty belowGood, ?_, ?_⟩
        · apply encodeForests_noFallback d hs
          · exact visibleGood_extends ((emit_extends ..).trans (emit_extends ..)) good
          · exact belowGood
        · apply encode_noFallback d t
          apply visibleGood_emit
          · exact visibleGood_extends ((emit_extends ..).trans
              ((emit_extends ..).trans (encodeForests_extends d hs _ _ _ _ _))) good
          · exact hasZero_append belowGood
  theorem encodeForests_noFallback (d : Nat) (hs : Forests ParentLabel) (visible : List Nat)
      (u : Nat → Nat) (c : Nat) (below : List Binding) (state : State d)
      (good : VisibleGood state visible) (belowGood : HasZero below) :
      NoFallbackForests d hs visible u c below state := by
    cases hs with
    | nil => trivial
    | cons h hs =>
      refine ⟨?_, ?_⟩
      · apply encode_noFallback d h
        exact visibleGood_emit state visible good _ _ _ below belowGood
      · apply encodeForests_noFallback d hs
        · exact visibleGood_extends ((emit_extends ..).trans (encode_extends d h _ _)) good
        · exact belowGood
end

/-- The defensive empty-base case is unreachable in every encoding begun
from the real empty context, including all intended standard source terms. -/
theorem source_noFallback (d : Nat) (e : NumericalExpr) :
    NoFallback d (Parents.annotate d [] e) [] [] :=
  encode_noFallback d _ [] [] (by intro p hp; simp at hp)

end BTnSSBMS.Encoder
