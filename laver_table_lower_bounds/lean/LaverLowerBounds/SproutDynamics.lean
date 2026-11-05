import LaverLowerBounds.BinaryBush

set_option autoImplicit false

namespace LaverLowerBounds.ParentBMS

/-- Attach a template root and k one-row leaves pointing to that root. -/
def sprout (stem : Matrix) (template : Column) (k : Nat) : Matrix :=
  stem ++ [template] ++ List.replicate k [stem.length]

theorem sprout_length (stem : Matrix) (template : Column) (k : Nat) :
    (sprout stem template k).length = stem.length + (k + 1) := by simp [sprout]

theorem sprout_at_root (stem : Matrix) (template : Column) (k : Nat) :
    (sprout stem template k)[stem.length]? = some template := by simp [sprout, List.append_assoc]

theorem sprout_at_leaf (stem : Matrix) (template : Column) {k i : Nat} (hi : i < k) :
    (sprout stem template k)[stem.length + 1 + i]? = some [stem.length] := by
  rw [sprout, List.getElem?_append_right (by simp)]
  simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel_left]
  exact List.getElem?_replicate_of_lt hi

theorem copy_sprout (stem : Matrix) (template : Column) (k : Nat) :
    copy (sprout stem template k) [stem.length] 0 stem.length (k + 1) 0 =
      template :: List.replicate k [stem.length + (k + 1)] := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < k + 1
  · rw [copy_zero, List.getElem?_map, List.getElem?_range hi]
    simp only [Option.map_some]
    cases i with
    | zero => simp [sprout_at_root]
    | succ i =>
        simp only [Nat.succ_ne_zero, ↓reduceIte]
        have he : stem.length + (i + 1) = stem.length + 1 + i := by omega
        rw [he, sprout_at_leaf stem template (by omega : i < k)]
        simp only [Option.getD_some, List.map_cons, List.map_nil, List.getElem?_cons_succ,
          List.getElem?_replicate_of_lt (by omega : i < k)]
        simp [shift]
  · rw [List.getElem?_eq_none (by rw [copy_length]; omega),
      List.getElem?_eq_none (by simp; omega)]

/-- Every nonroot step simply replaces a rank-(k+1) sprout by two rank-k
sprouts. All root-template parents remain fixed in the earlier background. -/
theorem sprout_split (stem : Matrix) (template : Column) (k : Nat) :
    expand (sprout stem template (k + 1)) 1 =
      sprout (sprout stem template k) template k := by
  have he : sprout stem template (k + 1) = sprout stem template k ++ [[stem.length]] := by
    simp only [sprout, List.replicate_succ', List.append_assoc]
  rw [he, expand_append]
  have hc : ([stem.length] : Column).getLast? = some stem.length := rfl
  rw [expandTail_one_positive hc]
  have hw : (sprout stem template k).length - stem.length = k + 1 := by rw [sprout_length]; omega
  simp only [List.length_singleton, Nat.sub_self, hw]
  rw [copy_sprout]
  simp [sprout, List.append_assoc]

def ParentsAtLeast (root : Nat) (s : Matrix) : Prop := ∀ c ∈ s, ∀ p ∈ c, root ≤ p

theorem map_shift_of_lower {c : Column} {root width : Nat}
    (hc : ∀ p ∈ c, root ≤ p) : c.map (shift root width) = c.map (fun p => p + width) := by
  apply List.map_congr_left
  intro p hp
  simp only [shift, if_neg (by have := hc p hp; omega : ¬ p < root)]

/-- At a root event, the remaining decorated forest is copied by a plain
translation. Only the preceding block needs the ordinary BMS head adjustment. -/
theorem copy_pending_suffix (front block pending : Matrix) (template : Column) (row : Nat)
    (hb : block ≠ []) (hp : ParentsAtLeast front.length pending) :
    (copy (front ++ block ++ pending) template row front.length
      (block.length + pending.length) 0).drop block.length =
      translated (block.length + pending.length) pending := by
  have hbp : 0 < block.length := by cases block <;> simp_all
  apply List.ext_getElem?
  intro i
  by_cases hi : i < pending.length
  · rw [List.getElem?_drop, copy_zero, List.getElem?_map,
      List.getElem?_range (by omega : block.length + i < block.length + pending.length)]
    simp only [Option.map_some, if_neg (by omega : ¬ block.length + i = 0)]
    have he : front.length + (block.length + i) = (front ++ block).length + i := by
      simp only [List.length_append]; omega
    rw [he, List.getElem?_append_right (by omega : (front ++ block).length ≤ (front ++ block).length + i),
      Nat.add_sub_cancel_left]
    simp only [translated, List.getElem?_map, List.getElem?_eq_getElem hi, Option.getD_some, Option.map_some]
    congr 1
    exact map_shift_of_lower (hp pending[i] (List.getElem_mem hi))
  · rw [List.getElem?_eq_none (by rw [List.length_drop, copy_length]; omega),
      List.getElem?_eq_none (by rw [translated_length]; omega)]

def bornBlock (front block pending : Matrix) (template : Column) : Matrix :=
  (copy (front ++ block ++ pending) template (template.length - 1) front.length
    (block.length + pending.length) 0).take block.length

theorem bornBlock_length (front block pending : Matrix) (template : Column) :
    (bornBlock front block pending template).length = block.length := by
  simp only [bornBlock, List.length_take, copy_length]
  omega

theorem sprout_birth (front block pending : Matrix) (template : Column)
    (hb : block ≠ []) (hp : ParentsAtLeast front.length pending)
    (hc : template.getLast? = some front.length) :
    expand (front ++ block ++ pending ++ [template]) 1 =
      (front ++ block ++ pending) ++ bornBlock front block pending template ++
        translated (block.length + pending.length) pending := by
  rw [expand_append, expandTail_one_positive hc]
  have hw : (front ++ block ++ pending).length - front.length = block.length + pending.length := by
    simp only [List.length_append]; omega
  rw [hw]
  have he := List.take_append_drop block.length
    (copy (front ++ block ++ pending) template (template.length - 1) front.length
      (block.length + pending.length) 0)
  rw [copy_pending_suffix front block pending template (template.length - 1) hb hp] at he
  rw [← he]
  simp only [bornBlock, List.append_assoc]

#print axioms sprout_split
#print axioms sprout_birth

end LaverLowerBounds.ParentBMS
