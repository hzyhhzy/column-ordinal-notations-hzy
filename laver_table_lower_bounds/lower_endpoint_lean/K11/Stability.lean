import LaverLowerBounds.Signature

set_option autoImplicit false
namespace LaverLowerBounds.FiniteTable.K11

theorem act_unsaturated_iff (family : BinaryFamily) (m a x : Nat) :
    act family m a x < m ↔ (family m).mul a (2 ^ x) ≠ 0 := by
  have hl := act_le family m a x
  have he := le_act_iff family m a x m (Nat.le_refl _)
  constructor
  · intro hu hz
    have := he.mpr hz
    omega
  · intro hz
    by_cases hu : act family m a x < m
    · exact hu
    · exact False.elim (hz (he.mp (by omega)))

/-- Once a capped action value lies strictly below its cap, all larger
finite tables give exactly the same value. This uses table projections,
not an elementary-embedding interpretation. -/
theorem act_stable_of_unsaturated (family : BinaryFamily) {m n a x : Nat}
    (hmn : m ≤ n) (hu : act family m a x < m) :
    act family n a x = act family m a x := by
  have hr : act family m a x ≤ m := act_le family m a x
  have lower : act family m a x ≤ act family n a x := by
    apply (le_act_iff family n a x _ (by omega)).mpr
    exact (le_act_iff family m a x _ hr).mp (Nat.le_refl _)
  have upper : ¬ act family m a x + 1 ≤ act family n a x := by
    intro h
    have hz := (le_act_iff family n a x (act family m a x + 1) (by omega)).mp h
    have bad := (le_act_iff family m a x (act family m a x + 1) (by omega)).mpr hz
    omega
  omega

#print axioms act_stable_of_unsaturated
#print axioms act_unsaturated_iff
end LaverLowerBounds.FiniteTable.K11
