import BTnSSBMS.Environment
import BTnSSBMS.KeyOrder
import Init.Data.List.Pairwise

/-!
Saved environments are strictly increasing both in complete key and in
height. The invariant is proved for the actual recursive encoder on every
raw finite input. It does not assert the separate exact target-parent table.
-/
namespace BTnSSBMS.Encoder

def BindingBefore (a b : Binding) : Prop :=
  Keys.compare a.key b.key = .lt ∧ a.height < b.height

def FrameOrdered (frame : List Binding) : Prop := List.Pairwise BindingBefore frame

def FramesOrdered (state : State d) : Prop := ∀ col ∈ state, FrameOrdered col.frame

private theorem pairwise_members {r : α → α → Prop} {xs : List α}
    (ordered : List.Pairwise r xs) (a b : α) (ha : a ∈ xs) (hb : b ∈ xs) :
    r a b ∨ a = b ∨ r b a := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    obtain ⟨first, rest⟩ := List.pairwise_cons.mp ordered
    rcases List.mem_cons.mp ha with rfl | tailA
    · rcases List.mem_cons.mp hb with rfl | tailB
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl (first b tailB)
    · rcases List.mem_cons.mp hb with rfl | tailB
      · exact Or.inr (Or.inr (first a tailA))
      · exact ih rest tailA tailB

theorem virtual_frame_ordered : FrameOrdered virtualFrame := by
  simp [FrameOrdered, virtualFrame]

theorem smaller_ordered {frame : List Binding} (ordered : FrameOrdered frame) (key : Key) :
    FrameOrdered (smaller frame key) := ordered.filter _

theorem binding_height_lt {frame : List Binding} (ordered : FrameOrdered frame)
    (a b : Binding) (ha : a ∈ frame) (hb : b ∈ frame)
    (less : Keys.compare a.key b.key = .lt) : a.height < b.height := by
  have alternatives := pairwise_members ordered a b ha hb
  rcases alternatives with before | same | after
  · exact before.2
  · subst b
    simp [Keys.compare_self] at less
  · exact False.elim (Keys.compare_asymmetric _ _ less after.1)

theorem binding_height_iff {frame : List Binding} (ordered : FrameOrdered frame)
    (a b : Binding) (ha : a ∈ frame) (hb : b ∈ frame) :
    Keys.compare a.key b.key = .lt ↔ a.height < b.height := by
  constructor
  · exact binding_height_lt ordered a b ha hb
  · intro lower
    cases compared : Keys.compare a.key b.key with
    | lt => rfl
    | eq =>
      have keySame := Keys.compare_eq_imp _ _ compared
      rcases pairwise_members ordered a b ha hb with before | same | after
      · simp [BindingBefore, keySame, Keys.compare_self] at before
      · subst b; omega
      · simp [BindingBefore, keySame, Keys.compare_self] at after
    | gt =>
      have back : Keys.compare b.key a.key = .lt := by
        have flip := Keys.compare_oriented b.key a.key
        simpa [compared] using flip
      have larger := binding_height_lt ordered b a hb ha back
      omega

theorem smaller_prefix {frame : List Binding} (ordered : FrameOrdered frame) (key : Key) :
    smaller frame key <+: frame := by
  induction frame with
  | nil => exact List.prefix_refl _
  | cons a frame ih =>
    obtain ⟨before, tail⟩ := List.pairwise_cons.mp ordered
    by_cases first : Keys.compare a.key key = .lt
    · obtain ⟨rest, same⟩ := ih tail
      refine ⟨rest, ?_⟩
      simpa only [smaller, List.filter_cons, first, beq_self_eq_true, if_true,
        List.cons_append] using congrArg (a :: ·) same
    · have absent : smaller frame key = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro b hb
        intro hit
        have ltKey : Keys.compare b.key key = .lt := by simpa only [beq_iff_eq] using hit
        exact first (Keys.compare_lt_trans _ _ _ (before b hb).1 ltKey)
      have noFirst : (Keys.compare a.key key == .lt) = false := by
        simp [first]
      simp only [smaller, List.filter_cons, noFirst, Bool.false_eq_true, if_false] at *
      rw [absent]
      exact List.nil_prefix

theorem equal_cut_prefix {frame : List Binding} (ordered : FrameOrdered frame)
    (key : Key) (bound : Binding) (found : equal frame key = some bound) :
    smaller frame key ++ [bound] <+: frame := by
  induction frame with
  | nil => simp [equal] at found
  | cons a frame ih =>
    obtain ⟨before, tail⟩ := List.pairwise_cons.mp ordered
    by_cases hit : Keys.compare a.key key = .eq
    · have foundHead : bound = a := by simpa [equal, hit] using found.symm
      subst bound
      have keySame := Keys.compare_eq_imp _ _ hit
      have absent : smaller frame key = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro b hb ltKey
        have back : Keys.compare b.key a.key = .lt := by
          simpa only [keySame, beq_iff_eq] using ltKey
        exact Keys.compare_asymmetric _ _ (before b hb).1 back
      simp only [smaller, List.filter_cons, hit, show (.eq == Ordering.lt) = false from rfl,
        Bool.false_eq_true, if_false] at *
      rw [absent]
      exact ⟨frame, rfl⟩
    · have next : equal frame key = some bound := by
        simpa [equal, hit] using found
      have member : bound ∈ frame := List.mem_of_find?_eq_some next
      have keySame : bound.key = key := Keys.compare_eq_imp _ _
        (by simpa only [beq_iff_eq] using List.find?_some next)
      have less : Keys.compare a.key key = .lt := by simpa only [← keySame] using (before bound member).1
      obtain ⟨rest, same⟩ := ih tail next
      refine ⟨rest, ?_⟩
      simpa only [smaller, List.filter_cons, less, beq_self_eq_true, if_true,
        List.cons_append] using congrArg (a :: ·) same

theorem member_height_le_base {frame : List Binding} (ordered : FrameOrdered frame)
    (a : Binding) (ha : a ∈ frame) : a.height ≤ (base frame).height := by
  have nonempty : frame ≠ [] := by intro empty; simp [empty] at ha
  have parts := List.take_append_getLast frame nonempty
  have paired : List.Pairwise BindingBefore
      (frame.take (frame.length - 1) ++ [frame.getLast nonempty]) := by
    rw [parts]; exact ordered
  have member : a ∈ frame.take (frame.length - 1) ++ [frame.getLast nonempty] := by
    rw [parts]; exact ha
  simp only [base, List.getLast?_eq_some_getLast nonempty, Option.getD_some]
  rcases List.mem_append.mp member with old | last
  · exact Nat.le_of_lt ((List.pairwise_append.mp paired).2.2 a old _ (by simp)).2
  · have same : a = frame.getLast nonempty := by simpa using last
    exact same ▸ Nat.le_refl _

theorem fresh_frame_ordered {frame : List Binding} (ordered : FrameOrdered frame)
    (key : Key) (latest definition : Option Nat) :
    FrameOrdered (smaller frame key ++
      [⟨key, (base (smaller frame key)).height + 2, latest, definition⟩]) := by
  have filtered := smaller_ordered ordered key
  apply List.pairwise_append.mpr
  refine ⟨filtered, by simp, ?_⟩
  intro a ha b hb
  have same : b = ⟨key, (base (smaller frame key)).height + 2, latest, definition⟩ := by
    simpa using hb
  subst b
  have ltKey : Keys.compare a.key key = .lt := by
    simpa only [beq_iff_eq] using (List.mem_filter.mp ha).2
  have bound := member_height_le_base filtered a ha
  exact ⟨ltKey, by dsimp; omega⟩

theorem reused_frame_ordered {frame : List Binding} (ordered : FrameOrdered frame)
    (key : Key) (bound : Binding) (found : equal frame key = some bound) (p : Nat) :
    FrameOrdered (smaller frame key ++ [{bound with latest := some p}]) := by
  have member : bound ∈ frame := List.mem_of_find?_eq_some found
  have keySame : bound.key = key := Keys.compare_eq_imp _ _
    (by simpa only [beq_iff_eq] using List.find?_some found)
  apply List.pairwise_append.mpr
  refine ⟨smaller_ordered ordered key, by simp, ?_⟩
  intro a ha b hb
  have same : b = {bound with latest := some p} := by simpa using hb
  subst b
  have info := List.mem_filter.mp ha
  have ltKey : Keys.compare a.key bound.key = .lt := by
    simpa only [keySame, beq_iff_eq] using info.2
  exact ⟨ltKey, binding_height_lt ordered a bound info.1 member ltKey⟩

theorem framesOrdered_emit {state : State d} (ordered : FramesOrdered state)
    (u : Nat → Nat) (height tag : Nat) (frame : List Binding)
    (frameOrdered : FrameOrdered frame) : FramesOrdered (emit state u height tag frame) := by
  intro col hc
  rcases List.mem_append.mp hc with old | added
  · exact ordered col old
  · have same : col = ⟨row d u height tag, row_width d u height tag, frame⟩ := by
      simpa using added
    exact same ▸ frameOrdered

theorem queried_frame_ordered {state : State d} (ordered : FramesOrdered state)
    (position : Option Nat) : FrameOrdered (frameAt state position) := by
  unfold frameAt
  cases h : position.bind (state[·]?) with
  | none => exact virtual_frame_ordered
  | some col =>
    obtain ⟨p, _, lookup⟩ := Option.bind_eq_some_iff.mp h
    exact ordered col (List.mem_of_getElem? lookup)

mutual
  theorem encode_framesOrdered (d : Nat) (e : ParentExpr) (visible : List Nat) (state : State d)
      (ordered : FramesOrdered state) : FramesOrdered (encode d e visible state) := by
    cases e with
    | nil => exact ordered
    | cons a hs t =>
      have frameOrder := queried_frame_ordered ordered (representative visible a (d - 1))
      simp only [encode]
      split
      next bound found =>
        apply encode_framesOrdered d t
        exact framesOrdered_emit ordered _ _ _ _ (reused_frame_ordered frameOrder _ bound found _)
      next fresh =>
        apply encode_framesOrdered d t
        apply framesOrdered_emit
        · apply encodeForests_framesOrdered d hs
          · exact smaller_ordered frameOrder _
          · apply framesOrdered_emit
            · exact framesOrdered_emit ordered _ _ _ [] (by simp [FrameOrdered])
            · simp [FrameOrdered]
        · exact fresh_frame_ordered frameOrder _ _ _
  theorem encodeForests_framesOrdered (d : Nat) (hs : Forests ParentLabel) (visible : List Nat)
      (u : Nat → Nat) (c : Nat) (below : List Binding) (state : State d)
      (belowOrdered : FrameOrdered below) (ordered : FramesOrdered state) :
      FramesOrdered (encodeForests d hs visible u c below state) := by
    cases hs with
    | nil => exact ordered
    | cons h hs =>
      apply encodeForests_framesOrdered d hs _ _ _ _ _ belowOrdered
      apply encode_framesOrdered d h
      exact framesOrdered_emit ordered _ _ _ below belowOrdered
end

theorem source_framesOrdered (d : Nat) (e : NumericalExpr) :
    FramesOrdered (encode d (Parents.annotate d [] e) [] []) :=
  encode_framesOrdered d _ [] [] (by intro col member; simp at member)

end BTnSSBMS.Encoder
