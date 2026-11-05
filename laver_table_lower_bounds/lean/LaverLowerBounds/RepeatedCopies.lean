import LaverLowerBounds.SproutTransport

set_option autoImplicit false

namespace LaverLowerBounds.ParentBMS.CopyFrame

theorem width_pos (f : CopyFrame) : 0 < f.width := by
  have := f.root_lt
  dsimp [width]
  omega

theorem root_add_width (f : CopyFrame) : f.root + f.width = f.stem.length := by
  have := f.root_lt
  dsimp [width]
  omega

theorem out_head (f : CopyFrame) :
    f.out[f.stem.length]? = some (f.last.take f.row ++ (f.stem[f.root]?.getD []).drop f.row) := by
  rw [f.out_eq, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, copy_zero,
    List.getElem?_map, List.getElem?_range f.width_pos]
  simp

theorem out_column (f : CopyFrame) {i : Nat} (hpos : 0 < i) (hi : i < f.width) :
    f.out[f.stem.length + i]? = some ((f.stem[f.root + i]?.getD []).map f.move) := by
  rw [f.out_eq, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, copy_zero,
    List.getElem?_map, List.getElem?_range hi]
  simp only [Option.map_some, if_neg (by omega : ¬ i = 0)]
  rfl

theorem out_head_drop (f : CopyFrame) :
    (f.out[f.stem.length]?.getD []).drop f.row = (f.stem[f.root]?.getD []).drop f.row := by
  rw [f.out_head, Option.getD_some, List.drop_append]
  have hr : f.row ≤ f.last.length := Nat.sub_le _ _
  simp only [List.length_take, Nat.min_eq_left hr, List.drop_take, Nat.sub_self, List.take_zero,
    List.nil_append, List.drop_zero]

theorem move_then_shift (f : CopyFrame) (b p : Nat) :
    shift f.stem.length (b * f.width) (f.move p) = shift f.root ((b + 1) * f.width) p := by
  by_cases hp : p < f.root
  · rw [f.move_low hp]
    simp only [shift, if_pos hp, if_pos (Nat.lt_trans hp f.root_lt)]
  · rw [f.move_high (by omega)]
    have hhigh : ¬ p + f.width < f.stem.length := by have := f.root_add_width; omega
    simp only [shift, if_neg hhigh, if_neg hp, Nat.add_mul, Nat.one_mul]
    omega

theorem copy_next (f : CopyFrame) (b : Nat) :
    copy f.next.stem f.next.last f.next.row f.next.root f.next.width b =
      copy f.stem f.last f.row f.root f.width (b + 1) := by
  rw [f.next_row, f.next_width]
  change copy f.out (f.last.map f.move) f.row f.stem.length f.width b = _
  simp only [copy]
  apply List.map_congr_left
  intro i hi
  have hiw := List.mem_range.mp hi
  by_cases hz : i = 0
  · rw [if_pos hz, if_pos hz, f.out_head_drop]
    simp only [← List.map_take, List.map_map]
    congr 1
    apply congrArg (fun g => (f.last.take f.row).map g)
    funext p
    exact f.move_then_shift b p
  · rw [if_neg hz, if_neg hz, f.out_column (by omega) hiw]
    simp only [Option.getD_some, List.map_map]
    apply congrArg (fun g => (f.stem[f.root + i]?.getD []).map g)
    funext p
    exact f.move_then_shift (b + 1) p

theorem next_expand (f : CopyFrame) (n : Nat) :
    expandTail f.next.stem f.next.last n = expandTail f.stem f.last (n + 1) := by
  simp only [expandTail, f.next.control, f.control]
  change f.next.stem ++ (List.range n).flatMap (copy f.next.stem f.next.last f.next.row f.next.root f.next.width) =
    f.stem ++ (List.range (n + 1)).flatMap (copy f.stem f.last f.row f.root f.width)
  have he : copy f.next.stem f.next.last f.next.row f.next.root f.next.width =
      fun b => copy f.stem f.last f.row f.root f.width (b + 1) := funext f.copy_next
  rw [he, List.range_succ_eq_map]
  simp only [List.flatMap_cons, List.flatMap_map, Nat.succ_eq_add_one]
  change f.out ++ (List.range n).flatMap (fun b => copy f.stem f.last f.row f.root f.width (b + 1)) = _
  rw [f.out_eq, List.append_assoc]

/-- Iterating complete one-copy frames is exactly the ordinary n-th basic
sequence term, not just a larger state or an order-equivalent representation. -/
theorem advance_stem (f : CopyFrame) (n : Nat) :
    (f.advance n).stem = expandTail f.stem f.last n := by
  induction n generalizing f with
  | zero => simp [advance]
  | succ n ih =>
      change (f.next.advance n).stem = _
      rw [ih, f.next_expand]

theorem sprout_index_budget {f : CopyFrame} {x n : Nat}
    (ht : PrefixDescent.Stops (fun s => expand s 1) (sprout f.stem f.last x) n) :
    ∃ k, PrefixDescent.Stops (fun s => expand s 1) (expandTail f.stem f.last (2 ^ x)) k ∧
      (2 ^ (x + 1) - 1) + k ≤ n := by
  obtain ⟨k, hk, hb⟩ := f.sprout_budget ht
  rw [f.advance_stem] at hk
  exact ⟨k, hk, hb⟩

#print axioms advance_stem
#print axioms sprout_index_budget

end LaverLowerBounds.ParentBMS.CopyFrame
