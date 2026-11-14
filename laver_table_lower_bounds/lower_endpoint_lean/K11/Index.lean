import K11.Stability

set_option autoImplicit false
namespace LaverLowerBounds.FiniteTable

/-- The finite, stable critical-point index for row 11 at input γ₄.
A witness is any finite cap at which the index is already resolved. -/
def K11Index (family : BinaryFamily) (r : Nat) : Prop :=
  ∃ m, act family m 11 4 = r ∧ r < m

/-- The resolved-index definition is exactly eventual constancy of the
finite-table indices; this is not a special existence convention. -/
theorem k11Index_iff_eventually (family : BinaryFamily) (r : Nat) :
    K11Index family r ↔ ∃ N, ∀ n, N ≤ n → act family n 11 4 = r := by
  constructor
  · rintro ⟨m, he, hm⟩
    refine ⟨m, ?_⟩
    intro n hmn
    exact (K11.act_stable_of_unsaturated family hmn (by omega)).trans he
  · rintro ⟨N, hN⟩
    let m := max N (r + 1)
    have hNm : N ≤ m := Nat.le_max_left _ _
    have hrm : r + 1 ≤ m := Nat.le_max_right _ _
    exact ⟨m, hN m hNm, by omega⟩

theorem K11Index.unique {family : BinaryFamily} {r s : Nat}
    (hr : K11Index family r) (hs : K11Index family s) : r = s := by
  obtain ⟨M, hM⟩ := (k11Index_iff_eventually family r).mp hr
  obtain ⟨N, hN⟩ := (k11Index_iff_eventually family s).mp hs
  exact (hM (max M N) (Nat.le_max_left _ _)).symm.trans
    (hN (max M N) (Nat.le_max_right _ _))

theorem k11Index_exists_iff (family : BinaryFamily) :
    (∃ r, K11Index family r) ↔ ∃ m, (family m).mul 11 16 ≠ 0 := by
  constructor
  · rintro ⟨r, m, he, hm⟩
    exact ⟨m, (K11.act_unsaturated_iff family m 11 4).mp (by omega)⟩
  · rintro ⟨m, hm⟩
    exact ⟨act family m 11 4, m, rfl, (K11.act_unsaturated_iff family m 11 4).mpr hm⟩

theorem k11Index_absent_iff (family : BinaryFamily) :
    (¬ ∃ r, K11Index family r) ↔ ∀ m, (family m).mul 11 16 = 0 := by
  constructor
  · intro hn m
    by_cases hm : (family m).mul 11 16 = 0
    · exact hm
    · exact False.elim (hn ((k11Index_exists_iff family).mpr ⟨m, hm⟩))
  · intro hz he
    obtain ⟨m, hm⟩ := (k11Index_exists_iff family).mp he
    exact hm (hz m)

#print axioms k11Index_iff_eventually
#print axioms K11Index.unique
#print axioms k11Index_exists_iff
#print axioms k11Index_absent_iff
end LaverLowerBounds.FiniteTable
