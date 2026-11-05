import LaverLowerBounds.NumericParentEncoding

set_option autoImplicit false

namespace LaverLowerBounds.NumericBMS
open YesMetaZFC.BMS
open ExpansionContext

theorem encode_expand_zero (a : ValidArray) :
    encode (a.expand 0).raw = (encode a.raw).dropLast := by
  rw [ValidArray.raw_expand, expand_zero_eq_trimmed_take_pred, encode_trim, encode_take]
  simp only [List.dropLast_eq_take, encode_length]

def stem {a : ValidArray} (c : ExpansionContext a) : ParentBMS.Matrix :=
  (encode a.raw).take c.lastIndex

@[simp] theorem stem_length {a : ValidArray} (c : ExpansionContext a) :
    (stem c).length = c.lastIndex := by simp [stem, c.array_length]

theorem stem_get {a : ValidArray} (c : ExpansionContext a) {i : Nat}
    (hi : i < c.lastIndex) : (stem c)[i]? = some (parents a.raw i) := by
  simp only [stem, List.getElem?_take_of_lt hi]
  exact encode_get _ (by rw [c.array_length]; omega)

theorem new_column {a : ValidArray} (c : ExpansionContext a) (n : Nat)
    {i : Nat} (hi : i < c.blockLength) :
    parents (a.expand (n + 1)).raw (c.copyPosition (n + 1) i) =
      if i = 0 then
        ((parents a.raw c.lastIndex).take c.maximalRow).map
          (ParentBMS.shift c.parentColumn (n * c.blockLength)) ++
            (parents a.raw c.parentColumn).drop c.maximalRow
      else (parents a.raw (c.parentColumn + i)).map
        (ParentBMS.shift c.parentColumn ((n + 1) * c.blockLength)) := by
  apply List.ext_getElem?
  intro r
  rw [parents_get, parent_copied c (by omega) (Nat.le_refl _) hi]
  by_cases hi0 : i = 0
  · subst i
    simp only [↓reduceIte, Nat.add_sub_cancel]
    have hlen : (((parents a.raw c.lastIndex).take c.maximalRow).map
        (ParentBMS.shift c.parentColumn (n * c.blockLength))).length = c.maximalRow := by
      simp [parents_length_context]
    by_cases hr : r < c.maximalRow
    · rw [if_pos hr, List.getElem?_append_left (by omega), List.getElem?_map,
        List.getElem?_take_of_lt hr, parents_get]
    · rw [if_neg hr, List.getElem?_append_right (by omega), hlen, List.getElem?_drop]
      rw [Nat.add_sub_cancel' (by omega : c.maximalRow ≤ r), parents_get]
  · simp only [if_neg hi0, List.getElem?_map, parents_get]

theorem copy_get {a : ValidArray} (c : ExpansionContext a) (n : Nat)
    {i : Nat} (hi : i < c.blockLength) :
    (ParentBMS.copy (stem c) (parents a.raw c.lastIndex) c.maximalRow
      c.parentColumn c.blockLength n)[i]? =
        some (parents (a.expand (n + 1)).raw (c.copyPosition (n + 1) i)) := by
  rw [new_column c n hi]
  simp only [ParentBMS.copy, List.getElem?_map, List.getElem?_range hi, Option.map_some]
  by_cases hi0 : i = 0
  · simp only [hi0, ↓reduceIte, stem_get c c.parentColumn_lt_lastIndex, Option.getD_some]
  · have hc : c.parentColumn + i < c.lastIndex := by
      unfold blockLength at hi
      have := c.parentColumn_lt_lastIndex
      omega
    simp only [if_neg hi0, stem_get c hc, Option.getD_some]

theorem encode_expand_succ {a : ValidArray} (c : ExpansionContext a) (n : Nat) :
    encode (a.expand (n + 1)).raw = encode (a.expand n).raw ++
      ParentBMS.copy (stem c) (parents a.raw c.lastIndex) c.maximalRow
        c.parentColumn c.blockLength n := by
  have hlen : (a.expand (n + 1)).raw.length = (a.expand n).raw.length + c.blockLength := by
    rw [c.length_expand, c.length_expand]
    simp only [Nat.add_mul, Nat.one_mul]
    omega
  apply List.ext_getElem?
  intro j
  by_cases hnew : j < (a.expand (n + 1)).raw.length
  · rw [encode_get _ hnew]
    by_cases hold : j < (a.expand n).raw.length
    · rw [List.getElem?_append_left (by simpa using hold), encode_get _ hold]
      congr 1
      apply List.ext_getElem?
      intro r
      rw [parents_get, parents_get]
      exact (parent_expand_indices c (n := n) (k := n + 1) (by omega) hold r).symm
    · rw [List.getElem?_append_right (by simp only [encode_length]; omega), encode_length]
      have hj : j - (a.expand n).raw.length < c.blockLength := by omega
      rw [copy_get c n hj]
      have he : j = c.copyPosition (n + 1) (j - (a.expand n).raw.length) := by
        rw [c.length_expand]
        simp only [copyPosition, copyStart]
        rw [c.length_expand] at hold
        omega
      rw [← he]
  · rw [List.getElem?_eq_none (by rw [encode_length]; omega), List.getElem?_eq_none]
    simp only [List.length_append, encode_length, ParentBMS.copy_length]
    omega

theorem encode_split {a : ValidArray} (c : ExpansionContext a) :
    encode a.raw = stem c ++ [parents a.raw c.lastIndex] := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < c.lastIndex
  · rw [List.getElem?_append_left (by simpa using hi), stem_get c hi]
    exact encode_get _ (by rw [c.array_length]; omega)
  · rw [List.getElem?_append_right (by simp; omega), stem_length]
    by_cases he : i = c.lastIndex
    · subst i
      rw [encode_get _ (by rw [c.array_length]; omega)]
      simp
    · rw [List.getElem?_eq_none (by simp [c.array_length]; omega)]
      exact (List.getElem?_eq_none (by simp; omega)).symm

theorem encode_expand_context {a : ValidArray} (c : ExpansionContext a) (n : Nat) :
    encode (a.expand n).raw = ParentBMS.expand (encode a.raw) n := by
  rw [encode_split c, ParentBMS.expand_append]
  simp only [ParentBMS.expandTail, parents_last_context, parents_length_context,
    Nat.add_sub_cancel, stem_length]
  change encode (a.expand n).raw = stem c ++ (List.range n).flatMap
    (ParentBMS.copy (stem c) (parents a.raw c.lastIndex) c.maximalRow c.parentColumn c.blockLength)
  induction n with
  | zero =>
    rw [encode_expand_zero]
    simp only [List.range_zero, List.flatMap_nil, List.append_nil]
    simp only [stem, List.dropLast_eq_take, encode_length, c.array_length, Nat.add_sub_cancel]
  | succ n ih =>
    rw [encode_expand_succ c n, ih, List.range_succ, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

/-- Exact equality of arbitrary-index expansions, on all valid numeric BM4
arrays. It is stronger than equality of ordinal values or finite tests. -/
theorem encode_expand (a : ValidArray) (n : Nat) :
    encode (a.expand n).raw = ParentBMS.expand (encode a.raw) n := by
  cases hm : maximalParentRow a.raw with
  | some r =>
    obtain ⟨c⟩ := exists_expansionContext_of_maximalParentRow_eq_some hm
    exact encode_expand_context c n
  | none =>
    cases hs : a.raw.reverse with
    | nil =>
      have he : a.raw = [] := by simpa using congrArg List.reverse hs
      simp [ValidArray.raw_expand, YesMetaZFC.BMS.expand, expandRaw, he,
        trimZeroRows, encode, ParentBMS.expand]
    | cons last rest =>
      have he : a.raw = rest.reverse ++ [last] := by simpa using congrArg List.reverse hs
      have hlen : a.raw.length = rest.length + 1 := by simp [he]
      have hlast : parents a.raw rest.length = [] := by
        apply List.ext_getElem?
        intro r
        rw [parents_get, List.getElem?_nil]
        cases hp : parent r a.raw rest.length with
        | none => rfl
        | some p =>
          have hb := parent_row_lt hp
          simp only [maximalParentRow, hlen] at hm
          have hbound : r < (a.raw[rest.length]?.map List.length).getD 0 := by
            cases hh : a.raw[rest.length]? <;> simpa [hh] using hb
          have := greatestBelow?_eq_none_iff.mp hm r hbound
          simp [hp] at this
      have hes : encode a.raw = (encode a.raw).dropLast ++ [[]] := by
        have hslen : (encode a.raw).length = rest.length + 1 := by simp [hlen]
        have hlget : (encode a.raw)[rest.length]? = some [] := by
          rw [encode_get _ (by omega), hlast]
        have hlastget : (encode a.raw).getLast? = some [] := by
          rw [List.getLast?_eq_getElem?, hslen]; simpa using hlget
        obtain ⟨s, hseq⟩ := List.getLast?_eq_some_iff.mp hlastget
        simp [hseq]
      rw [hes, ParentBMS.expand_append, ParentBMS.expandTail_empty]
      rw [ValidArray.raw_expand]
      simp only [YesMetaZFC.BMS.expand, expandRaw, hlen, hm]
      rw [encode_trim, encode_take]
      simp only [List.dropLast_eq_take, encode_length, hlen, Nat.add_sub_cancel]

#print axioms encode_expand

end LaverLowerBounds.NumericBMS
