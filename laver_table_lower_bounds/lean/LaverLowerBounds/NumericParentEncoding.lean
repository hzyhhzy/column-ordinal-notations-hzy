import LaverLowerBounds.NumericCopyParents
import LaverLowerBounds.ParentGraph

set_option autoImplicit false

namespace LaverLowerBounds.NumericBMS
open YesMetaZFC.BMS

/-- A finite initial segment of an option-valued function, stopping at the
first absent entry. Numeric BM4 parents have no holes in their row support. -/
def pack (f : Nat → Option Nat) : Nat → List Nat
  | 0 => []
  | h + 1 => match f 0 with
    | none => []
    | some p => p :: pack (fun r => f (r + 1)) h

theorem pack_get (f : Nat → Option Nat) (h : Nat)
    (hup : ∀ r q, r ≤ q → f r = none → f q = none)
    (hbound : ∀ r, h ≤ r → f r = none) (r : Nat) : (pack f h)[r]? = f r := by
  induction h generalizing f r with
  | zero => simp only [pack, List.getElem?_nil]; exact (hbound r (by omega)).symm
  | succ h ih =>
    cases h0 : f 0 with
    | none => simp only [pack, h0, List.getElem?_nil]; exact (hup 0 r (by omega) h0).symm
    | some p =>
      cases r with
      | zero => simp [pack, h0]
      | succ r =>
        simp only [pack, h0, List.getElem?_cons_succ]
        exact ih _ (fun q t hqt => hup (q + 1) (t + 1) (by omega))
          (fun q hq => hbound (q + 1) (by omega)) r

theorem parent_none_up (a : BMSArray) (i : Nat) {r q : Nat}
    (hrq : r ≤ q) (hr : parent r a i = none) : parent q a i = none := by
  by_cases he : r = q
  · subst q; exact hr
  · cases hq : parent q a i with
    | none => rfl
    | some p =>
      have ha := isAncestor_of_lt_row (by omega : r < q) (direct_parent_isAncestor hq)
      have := isAncestor_eq_false_of_parent_none hr (ancestor := p)
      simp_all

def parents (a : BMSArray) (i : Nat) : List Nat :=
  pack (fun r => parent r a i) (trimHeight a)

theorem parents_get (a : BMSArray) (i r : Nat) : (parents a i)[r]? = parent r a i :=
  pack_get _ _ (fun _ _ => parent_none_up a i)
    (fun _ hr => parent_none_above_support a hr i) r

def encode (a : BMSArray) : ParentBMS.Matrix :=
  (List.range a.length).map (parents a)

@[simp] theorem encode_length (a : BMSArray) : (encode a).length = a.length := by
  simp [encode]

theorem encode_get (a : BMSArray) {i : Nat} (hi : i < a.length) :
    (encode a)[i]? = some (parents a i) := by simp [encode, hi]

theorem encode_parent (a : BMSArray) (r i : Nat) :
    ParentBMS.parent (encode a) r i = parent r a i := by
  by_cases hi : i < a.length
  · simp only [ParentBMS.parent, encode_get a hi, Option.bind_some, parents_get]
  · have hn : parent r a i = none := by
      cases hp : parent r a i with
      | none => rfl
      | some p => have := parent_some_target_valid hp; omega
    rw [hn]
    simp [ParentBMS.parent, List.getElem?_eq_none (by simp; omega : (encode a).length ≤ i)]

theorem matrix_ext {s t : ParentBMS.Matrix} (hlen : s.length = t.length)
    (hp : ∀ r i, ParentBMS.parent s r i = ParentBMS.parent t r i) : s = t := by
  apply List.ext_getElem hlen
  intro i hi ht
  apply List.ext_getElem?
  intro r
  simpa only [ParentBMS.parent, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem ht, Option.bind_some] using hp r i

theorem encode_trim (a : BMSArray) : encode (trimZeroRows a) = encode a := by
  apply matrix_ext (by simp [length_trimZeroRows])
  intro r i
  rw [encode_parent, encode_parent, parent_trim]

theorem encode_take (a : BMSArray) (k : Nat) : encode (a.take k) = (encode a).take k := by
  apply matrix_ext (by simp)
  intro r i
  by_cases hi : i < min k a.length
  · rw [encode_parent]
    have hei : i < (encode a).length := by simp; omega
    simp only [ParentBMS.parent, List.getElem?_take_of_lt (by omega : i < k)]
    change parent r (a.take k) i = ParentBMS.parent (encode a) r i
    rw [encode_parent]
    apply parent_eq_of_entry?_eq_below (by simp; omega) (by omega)
    intro j hj q
    unfold entry?
    rw [List.getElem?_take_of_lt (by omega)]
  · have hleft : (encode (a.take k)).length ≤ i := by simp; omega
    have hright : ((encode a).take k).length ≤ i := by simp; omega
    simp [ParentBMS.parent, List.getElem?_eq_none hleft, List.getElem?_eq_none hright]

theorem parent_row_lt {a : BMSArray} {r i p : Nat} (hp : parent r a i = some p) :
    r < (a[i]?.getD []).length := by
  obtain ⟨u, v, _, hv, _⟩ := parent_some_entry_lt hp
  unfold entry? at hv
  cases he : a[i]? with
  | none => simp [he] at hv
  | some col =>
    simp only [he, Option.bind_some] at hv
    simp only [Option.getD_some]
    exact (List.getElem?_eq_some_iff.mp hv).1

theorem parents_length_context {a : ValidArray} (c : ExpansionContext a) :
    (parents a.raw c.lastIndex).length = c.maximalRow + 1 := by
  have hp : (parents a.raw c.lastIndex)[c.maximalRow]? = some c.parentColumn := by
    rw [parents_get]; exact c.parent_eq
  have hm := (List.getElem?_eq_some_iff.mp hp).1
  have hmax := c.maximal_row_eq
  simp only [maximalParentRow, c.array_length] at hmax
  by_cases hne : (parents a.raw c.lastIndex).length = c.maximalRow + 1
  · exact hne
  · have hr : c.maximalRow + 1 < (parents a.raw c.lastIndex).length := by omega
    have hpp : parent (c.maximalRow + 1) a.raw c.lastIndex =
        some (parents a.raw c.lastIndex)[c.maximalRow + 1] := by
      rw [← parents_get]; exact List.getElem?_eq_getElem hr
    have hrow := parent_row_lt hpp
    have hbound : c.maximalRow + 1 < (a.raw[c.lastIndex]?.map List.length).getD 0 := by
      cases he : a.raw[c.lastIndex]? <;> simpa [he] using hrow
    have := greatestBelow?_some_isGreatest hmax (c.maximalRow + 1)
      hbound (by simp [hpp])
    omega

theorem parents_last_context {a : ValidArray} (c : ExpansionContext a) :
    (parents a.raw c.lastIndex).getLast? = some c.parentColumn := by
  rw [List.getLast?_eq_getElem?, parents_length_context]
  simpa only [Nat.add_sub_cancel, parents_get] using c.parent_eq

#print axioms encode_parent
#print axioms parents_last_context

end LaverLowerBounds.NumericBMS
