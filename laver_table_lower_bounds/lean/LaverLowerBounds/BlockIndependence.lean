import LaverLowerBounds.LiftWExpansion

set_option autoImplicit false

namespace LaverLowerBounds.ParentBMS

@[simp] theorem translated_length (offset : Nat) (s : Matrix) : (translated offset s).length = s.length := by
  simp [translated]

theorem translated_append (offset : Nat) (s t : Matrix) :
    translated offset (s ++ t) = translated offset s ++ translated offset t := by simp [translated]

theorem translated_comp (a b : Nat) (s : Matrix) :
    translated a (translated b s) = translated (b + a) s := by
  simp only [translated, List.map_map]
  apply congrArg (fun f => s.map f)
  funext c
  simp only [Function.comp_def, List.map_map, Nat.add_assoc]

def attached (front tail : Matrix) := front ++ translated front.length tail

@[simp] theorem attached_empty (s : Matrix) : attached s [] = s := by simp [attached, translated]
@[simp] theorem empty_attached (s : Matrix) : attached [] s = s := by simp [attached, translated_zero]

theorem attached_assoc (a b c : Matrix) : attached (attached a b) c = attached a (attached b c) := by
  simp only [attached, translated_append, translated_length, List.length_append, translated_comp, List.append_assoc]
  rw [Nat.add_comm b.length a.length]

theorem shift_offset (root offset base p : Nat) :
    shift (base + root) offset (p + base) = shift root offset p + base := by
  unfold shift
  split <;> split <;> omega

theorem attached_lookup {front stem : Matrix} {i : Nat} (hi : i < stem.length) :
    (attached front stem)[front.length + i]?.getD [] =
      (stem[i]?.getD []).map (fun p => p + front.length) := by
  simp only [attached, List.getElem?_append_right (by omega : front.length ≤ front.length + i), Nat.add_sub_cancel_left,
    translated, List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]

theorem copy_attached (front stem : Matrix) (last : Column) (row root b : Nat) :
    copy (attached front stem) (last.map (fun p => p + front.length)) row
        (front.length + root) (stem.length - root) b =
      translated front.length (copy stem last row root (stem.length - root) b) := by
  simp only [copy, translated, List.map_map]
  apply List.map_congr_left
  intro i hi
  dsimp only [Function.comp_def]
  have hib := List.mem_range.mp hi
  have hr : root < stem.length := by omega
  by_cases hz : i = 0
  · rw [if_pos hz, if_pos hz, attached_lookup hr]
    simp only [← List.map_take, ← List.map_drop, List.map_append, List.map_map]
    congr 1
    apply congrArg (fun f => (last.take row).map f)
    funext p
    exact shift_offset root (b * (stem.length - root)) front.length p
  · rw [if_neg hz, if_neg hz, Nat.add_assoc front.length root i,
      attached_lookup (by omega : root + i < stem.length)]
    simp only [List.map_map]
    apply congrArg (fun f => (stem[root + i]?.getD []).map f)
    funext p
    exact shift_offset root ((b + 1) * (stem.length - root)) front.length p

theorem expandTail_attached (front stem : Matrix) (last : Column) (n : Nat) :
    expandTail (attached front stem) (last.map (fun p => p + front.length)) n =
      attached front (expandTail stem last n) := by
  cases hc : last.getLast? with
  | none =>
      have he := List.getLast?_eq_none_iff.mp hc
      subst last
      rfl
  | some root =>
      have hm : (last.map (fun p => p + front.length)).getLast? = some (front.length + root) := by
        simp [List.getLast?_map, hc, Nat.add_comm]
      have hrow : (last.map (fun p => p + front.length)).length - 1 = last.length - 1 := by simp
      have hwidth : (attached front stem).length - (front.length + root) = stem.length - root := by
        simp only [attached, List.length_append, translated_length]
        omega
      simp only [expandTail, hc, hm, hrow, hwidth]
      simp only [attached, translated_append, List.append_assoc]
      apply congrArg (fun tail => front ++ (translated front.length stem ++ tail))
      simp only [translated, List.map_flatMap]
      apply congrArg (fun g => (List.range n).flatMap g)
      funext b
      exact copy_attached front stem last (last.length - 1) root b

/-- A nonempty appended block expands independently, with all parent indices
translated. This is an algorithmic equality, even before graph invariants. -/
theorem attached_expand (front tail : Matrix) (hne : tail ≠ []) (n : Nat) :
    expand (attached front tail) n = attached front (expand tail n) := by
  obtain ⟨stem, last, rfl⟩ := exists_last hne
  have he : attached front (stem ++ [last]) = attached front stem ++ [last.map (fun p => p + front.length)] := by
    simp [attached, translated, List.append_assoc]
  rw [he, expand_append, expand_append]
  exact expandTail_attached front stem last n

/-- Extend the W commutation lemma to arbitrary finite parent lists. If its
control lies outside the front, both bad blocks have width zero. -/
theorem liftW_expand_nonzero_all {stem : Matrix} {last : Column} (hl : last ≠ []) (n : Nat) :
    expand (liftW (stem ++ [last])) n = liftW (expand (stem ++ [last]) n) := by
  cases hc : last.getLast? with
  | none => exact False.elim (hl (List.getLast?_eq_none_iff.mp hc))
  | some root =>
      rw [liftW_append]
      simp only [List.map_cons, List.map_nil, expand_append]
      by_cases hr : root < stem.length
      · exact (liftW_expandTail hc hr n).symm
      · have hz : stem.length - root = 0 := by omega
        have hz' : (liftW stem).length - (root + 1) = 0 := by rw [liftW_length]; omega
        have hm : (raiseColumn last).getLast? = some (root + 1) := by
          simp [raiseColumn, hl, List.getLast?_map, hc]
        have hempty (s : Matrix) (c : Column) (r p : Nat) :
            (List.range n).flatMap (copy s c r p 0) = [] := by
          apply List.flatMap_eq_nil_iff.mpr
          intro b _
          simp [copy]
        simp only [expandTail, hc, hm, hz, hz', hempty, List.append_nil]

theorem blockCopies_succ (s : Matrix) (n : Nat) :
    blockCopies s (n + 1) = attached (blockCopies s n) s := by
  have hlen : ∀ k, (blockCopies s k).length = k * s.length := by
    intro k
    induction k with
    | zero => simp [blockCopies]
    | succ k ih =>
        rw [blockCopies, List.range_succ, List.flatMap_append]
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
        change (blockCopies s k ++ translated (k * s.length) s).length = (k + 1) * s.length
        rw [List.length_append, ih, translated_length, Nat.add_mul]
        simp
  rw [blockCopies, List.range_succ, List.flatMap_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  change blockCopies s n ++ translated (n * s.length) s = attached (blockCopies s n) s
  rw [attached, hlen]

#print axioms attached_expand
#print axioms liftW_expand_nonzero_all

end LaverLowerBounds.ParentBMS
