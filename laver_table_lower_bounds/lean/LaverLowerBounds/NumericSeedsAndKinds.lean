import LaverLowerBounds.NumericExpansionFidelity
import LaverLowerBounds.HierarchyEvaluation

set_option autoImplicit false

namespace LaverLowerBounds.NumericBMS
open YesMetaZFC.BMS

theorem parents_last_none {a : BMSArray} {k : Nat} (hlen : a.length = k + 1)
    (hm : maximalParentRow a = none) : parents a k = [] := by
  apply List.ext_getElem?
  intro r
  rw [parents_get, List.getElem?_nil]
  cases hp : parent r a k with
  | none => rfl
  | some p =>
    have hb := parent_row_lt hp
    simp only [maximalParentRow, hlen] at hm
    have hbound : r < (a[k]?.map List.length).getD 0 := by
      cases hh : a[k]? <;> simpa [hh] using hb
    have := greatestBelow?_eq_none_iff.mp hm r hbound
    simp [hp] at this

theorem encoded_last {a : BMSArray} {s : ParentBMS.Matrix} {last : List Nat}
    (he : encode a = s ++ [last]) : parents a s.length = last := by
  have hlen : a.length = s.length + 1 := by simpa using congrArg List.length he
  have hg := congrArg (fun t : ParentBMS.Matrix => t[s.length]?) he
  rw [encode_get _ (by omega)] at hg
  simpa using hg

theorem encoded_tail_kind {a : ValidArray} {s : ParentBMS.Matrix} {last : List Nat}
    (he : encode a.raw = s ++ [last]) : last = [] ↔ maximalParentRow a.raw = none := by
  have hlen : a.raw.length = s.length + 1 := by simpa using congrArg List.length he
  have hl := encoded_last he
  constructor
  · intro hz
    cases hm : maximalParentRow a.raw with
    | none => rfl
    | some r =>
      obtain ⟨c⟩ := exists_expansionContext_of_maximalParentRow_eq_some hm
      have hi : c.lastIndex = s.length := by have := c.array_length; omega
      have hc := parents_length_context c
      rw [hi, hl, hz] at hc
      simp at hc
  · intro hm
    rw [← hl]
    exact parents_last_none hlen hm

theorem numeric_nonempty {a : ValidArray} {s : ParentBMS.Matrix}
    (he : encode a.raw = s) (hs : s ≠ []) : a.raw ≠ [] := by
  intro ha
  have : s = [] := by simpa [ha, encode] using he.symm
  exact hs this

theorem parent_seed_left (h r : Nat) : parent r (seed h) 0 = none := by
  cases hp : parent r (seed h) 0 with
  | none => rfl
  | some p => have := parent_some_lt hp; omega

theorem parent_seed_right (h r : Nat) :
    parent r (seed h) 1 = if r < h then some 0 else none := by
  by_cases hr : r < h
  · rw [if_pos hr]
    induction r with
    | zero => simp [parent, seed, greatestBelow?, entry?, hr]
    | succ r ih =>
      have hp := ih (by omega)
      apply parent_eq_some_iff.mpr
      refine ⟨by simp [seed], by omega, ?_, ?_⟩
      · have ha := direct_parent_isAncestor hp
        simpa [parentEligible, entry?, seed, hr] using ha
      · intro q hq _; omega
  · rw [if_neg hr]
    cases hp : parent r (seed h) 1 with
    | none => rfl
    | some p =>
      have hb := parent_row_lt hp
      simp only [seed, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.getD_some, List.length_replicate] at hb
      omega

theorem encode_seed (h : Nat) : encode (seed h) = ParentBMS.seed h := by
  apply matrix_ext (by simp [seed, ParentBMS.seed])
  intro r i
  rw [encode_parent]
  cases i with
  | zero => simp [ParentBMS.parent, ParentBMS.seed, parent_seed_left]
  | succ i =>
    cases i with
    | zero => simp [ParentBMS.parent, ParentBMS.seed, parent_seed_right, List.getElem?_replicate]
    | succ i =>
      have hn : parent r (seed h) (i + 1 + 1) = none := by
        cases hp : parent r (seed h) (i + 1 + 1) with
        | none => rfl
        | some p => have hh := parent_some_target_valid hp; simp only [seed, List.length_cons,
            List.length_nil] at hh; omega
      simp [ParentBMS.parent, ParentBMS.seed, hn]

#print axioms encoded_tail_kind
#print axioms encode_seed

end LaverLowerBounds.NumericBMS
