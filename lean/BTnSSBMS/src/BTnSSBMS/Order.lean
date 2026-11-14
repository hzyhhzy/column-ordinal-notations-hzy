import BTnSSBMS.Encoder
import Init.Data.Nat.Compare

namespace BTnSSBMS

theorem listCompare_self (cmp : α → α → Ordering) (refl : ∀ a, cmp a a = .eq)
    (xs : List α) : listCompare cmp xs xs = .eq := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [listCompare, refl, ih]

theorem listCompare_common_prefix (cmp : α → α → Ordering)
    (refl : ∀ a, cmp a a = .eq) (xs a b : List α) :
    listCompare cmp (xs ++ a) (xs ++ b) = listCompare cmp a b := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, listCompare, refl, ih]

theorem natCompare_self (n : Nat) : compare n n = .eq := Nat.compare_eq_eq.mpr rfl

theorem columnCompare_self (xs : List Nat) : listCompare compare xs xs = .eq :=
  listCompare_self compare natCompare_self xs

private theorem replicate_sum (a b : Nat) (value : α) :
    List.replicate (a + b) value = List.replicate a value ++ List.replicate b value := by
  induction a with
  | zero => simp only [Nat.zero_add, List.replicate_zero, List.nil_append]
  | succ a ih => simp only [Nat.succ_add, List.replicate_succ, ih, List.cons_append]

theorem first_slot_below_diagonal (d : Nat) :
    listCompare compare (Encoder.row d (fun _ => 3) 2 0) (List.replicate (d + 2) 3) = .lt := by
  rw [Encoder.row, List.map_const', List.length_range, replicate_sum]
  rw [listCompare_common_prefix compare natCompare_self]
  rfl

/-- The final fixed-ceiling comparison once the required four-column head
has been established. It asserts neither standardness nor a general source bound. -/
theorem four_column_head_below_ceiling (d : Nat) (tail : Matrix) :
    matrixCompare
      (List.replicate (d + 2) 0 :: List.replicate (d + 2) 1 ::
       List.replicate (d + 2) 2 :: Encoder.row d (fun _ => 3) 2 0 :: tail)
      (ceiling d) = .lt := by
  change listCompare (listCompare compare)
    (List.replicate (d + 2) 0 :: List.replicate (d + 2) 1 ::
     List.replicate (d + 2) 2 :: Encoder.row d (fun _ => 3) 2 0 :: tail)
    [List.replicate (d + 2) 0, List.replicate (d + 2) 1,
     List.replicate (d + 2) 2, List.replicate (d + 2) 3] = .lt
  simp only [listCompare, columnCompare_self, first_slot_below_diagonal]

/-- A raw fixed-width descending sequence. This is NOT an expansion-chain
counterexample in the standard BMS domain. -/
def rawZerosThenOne (rows k : Nat) : Matrix :=
  List.replicate k (List.replicate rows 0) ++ [List.replicate rows 1]

theorem rawZerosThenOne_descends (rows k : Nat) (positive : 0 < rows) :
    matrixCompare (rawZerosThenOne rows (k + 1)) (rawZerosThenOne rows k) = .lt := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  unfold matrixCompare rawZerosThenOne
  rw [replicate_sum k 1]
  rw [List.append_assoc, listCompare_common_prefix (listCompare compare) columnCompare_self]
  rfl

end BTnSSBMS
