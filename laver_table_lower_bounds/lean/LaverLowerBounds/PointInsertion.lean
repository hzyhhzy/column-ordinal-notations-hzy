import LaverLowerBounds.FinitePointChain

set_option autoImplicit false

namespace LaverLowerBounds.FiniteTable.PointChain

def insertPoint (point : Nat → Nat) (k value i : Nat) : Nat :=
  if i < k then point i else if i = k then value else point (i - 1)

def insert {m n : Nat} (a : PointChain m n) (k value : Nat) (hk : 0 < k) (hkn : k ≤ n)
    (hlo : a.point (k - 1) < value) (hhi : value < a.point k) : PointChain m (n + 1) where
  point := insertPoint a.point k value
  strict := by
    intro i j hij hj
    unfold insertPoint
    by_cases hjk : j < k
    · rw [if_pos (by omega), if_pos hjk]
      exact a.strict hij (by omega)
    · rw [if_neg hjk]
      by_cases hje : j = k
      · rw [if_pos hje, if_pos (by omega)]
        exact Nat.lt_of_le_of_lt (a.mono (by omega : i ≤ k - 1) (by omega)) hlo
      · rw [if_neg hje]
        by_cases hik : i < k
        · rw [if_pos hik]
          exact a.strict (by omega) (by omega)
        · rw [if_neg hik]
          by_cases hie : i = k
          · rw [if_pos hie]
            exact Nat.lt_of_lt_of_le hhi (a.mono (by omega : k ≤ j - 1) (by omega))
          · rw [if_neg hie]
            exact a.strict (by omega) (by omega)
  bounded := by
    unfold insertPoint
    rw [if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel]
    exact a.bounded

theorem insertPoint_before (point : Nat → Nat) (k value i : Nat) (hi : i < k) :
    insertPoint point k value i = point i := by simp only [insertPoint, if_pos hi]

theorem insertPoint_at (point : Nat → Nat) (k value : Nat) :
    insertPoint point k value k = value := by simp [insertPoint]

theorem insertPoint_after (point : Nat → Nat) (k value i : Nat) (hi : k < i) :
    insertPoint point k value i = point (i - 1) := by
  simp only [insertPoint, if_neg (show ¬ i < k by omega), if_neg (show i ≠ k by omega)]

#print axioms insert

end LaverLowerBounds.FiniteTable.PointChain
