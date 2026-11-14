import K11.Map

set_option autoImplicit false
namespace LaverLowerBounds.FiniteTable
namespace Lined
variable {family : BinaryFamily} {m root : Nat}

/-- The line-product construction retains its complete lower prefix. -/
theorem multiply_tail {a b c t u : Nat} (base : Lined family m root t a b)
    (higher : Lined family m a u b c) (hroot : root < a) :
    Lined family m root (t * 2 ^ u - t) b c := by
  induction higher generalizing t with
  | nil hb => simpa using (Lined.nil (root := root) hb)
  | @cons n b d c owner hsig hstart hnext hlt tail ih =>
    have dc := Nat.lt_of_le_of_lt tail.endpoints.1 tail.endpoints.2
    have rootFixed := fixes_below_signature family m owner root (by omega)
    have mapped := base.map owner (by rw [hnext]; exact dc)
    rw [rootFixed, hstart, hnext] at mapped
    have doubled := base.double hroot hsig hstart hnext dc
    have rest := ih doubled
    have result := mapped.append rest
    have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have ht : t + t ≤ (t + t) * 2 ^ n := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos n)
    have he : t + ((t + t) * 2 ^ n - (t + t)) = t * 2 ^ (n + 1) - t := by
      rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_two, Nat.add_mul]
      rw [Nat.add_mul] at ht
      omega
    rwa [he] at result

theorem split {n a b p : Nat} (line : Lined family m root n a b) (hp : p ≤ n) :
    ∃ c, Lined family m root p a c ∧ Lined family m root (n - p) c b := by
  induction p generalizing n a with
  | zero => exact ⟨a, .nil (Nat.lt_of_le_of_lt line.endpoints.1 line.endpoints.2), by simpa using line⟩
  | succ p ih =>
    cases line with
    | nil _ => omega
    | @cons n a b c owner hs ha hb hab tail =>
      obtain ⟨d, first, rest⟩ := ih tail (by omega)
      refine ⟨d, .cons owner hs ha hb hab first, ?_⟩
      simpa only [Nat.add_sub_add_right] using rest

#print axioms multiply_tail
#print axioms split
end Lined
end LaverLowerBounds.FiniteTable
