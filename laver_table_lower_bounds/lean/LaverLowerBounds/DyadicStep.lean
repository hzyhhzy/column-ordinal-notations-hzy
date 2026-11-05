import LaverLowerBounds.DyadicBounds

set_option autoImplicit false

namespace LaverLowerBounds.FiniteTable

theorem dyadic_flatten_block (family : BinaryFamily) (m N : Nat)
    (hN : 0 < N) (hcap : 2 * N < m) (bound : DyadicBound family m N)
    {r : Nat} (hr : 0 < r) (hrp : r < 2 ^ N) :
    congruent m (2 * N + 1) (2 ^ N * (r + 1)) ((family m).mul (2 ^ N * r) (2 ^ N)) := by
  let p := 2 ^ N
  have hp : 0 < p := Nat.two_pow_pos N
  have square : p * p = 2 ^ (2 * N) := by rw [Nat.two_mul, Nat.pow_add]
  have squareCap : p * p < 2 ^ m := by rw [square]; exact Nat.pow_lt_pow_right (by decide) hcap
  have prBound : p * r + p ≤ p * p := by
    simpa only [Nat.mul_succ] using Nat.mul_le_mul_left p (show r + 1 ≤ p by omega)
  have pBound : p ≤ p * p := by
    have he := Nat.mul_le_mul_left p (show 1 ≤ p by omega)
    simpa only [Nat.mul_one] using he
  have sigBase : N ≤ signature m (p * r) := by
    apply (le_signature m (p * r) N (by omega)).mpr
    exact Nat.mul_mod_right _ _
  have main : ∀ s, 0 < s → s ≤ p →
      congruent m (2 * N + 1) (p * r + s) ((family m).mul (p * r) s) := by
    intro s
    induction s with
    | zero => omega
    | succ s ih =>
        intro hs hsp
        by_cases hz : s = 0
        · subst s
          rw [(family m).mul_one, Nat.mod_eq_of_lt (by omega)]
          exact congruent_refl _ _ _
        · have hspos : 0 < s := by omega
          have hslt : s < p := by omega
          have low : (p * r + s) % p = s := by
            rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hslt]
          have high : (p * r + s) % 2 ^ (2 * N) = p * r + s := by
            rw [← square, Nat.mod_eq_of_lt (by omega)]
          have ppr : p ≤ p * r := by
            have he := Nat.mul_le_mul_left p hr
            simpa only [Nat.mul_one] using he
          have hb := (bound (p * r + s) (by rw [low]; omega)).2 (by rw [high]; omega)
          have cutoff : 2 * N + 1 ≤ act family m (p * r + s) (signature m (p * r)) := by
            have he := act_mono family m (p * r + s) sigBase
            omega
          have step := flatten_step family m (a := p * r) (word := p * r + s)
            (tail := s) (c := 1) (ih hspos (by omega)) cutoff
          rw [(family m).mul_one, Nat.mod_eq_of_lt (by omega),
            (family m).mul_one, Nat.mod_eq_of_lt (by omega)] at step
          simpa only [Nat.add_assoc] using step
  simpa only [Nat.mul_succ] using main p hp (Nat.le_refl _)

/-- The explicit next segment from the preceding reverse-residue bound.
It gives the exact nonsaturated image, not only a lower bound. -/
theorem dyadic_step (family : BinaryFamily) (m N : Nat)
    (hN : 0 < N) (hcap : 2 * N < m) (bound : DyadicBound family m N) :
    signature m (2 ^ N - 1) = 0 ∧
    act family m (2 ^ N - 1) 0 = N ∧
    act family m (2 ^ N - 1) N = 2 * N := by
  let p := 2 ^ N
  have hp : 0 < p := Nat.two_pow_pos N
  have square : p * p = 2 ^ (2 * N) := by rw [Nat.two_mul, Nat.pow_add]
  have squareCap : p * p < 2 ^ m := by rw [square]; exact Nat.pow_lt_pow_right (by decide) hcap
  have pBound : p ≤ p * p := by
    have he := Nat.mul_le_mul_left p (show 1 ≤ p by omega)
    simpa only [Nat.mul_one] using he
  have pcap : p < 2 ^ m := by omega
  have pred : p - 1 + 1 = p := by omega
  have seq : ∀ r, 0 < r → r ≤ p →
      congruent m (2 * N + 1) (p * r) ((family m).mul (p - 1) r) := by
    intro r
    induction r with
    | zero => omega
    | succ r ih =>
        intro hr hrp
        by_cases hz : r = 0
        · subst r
          rw [Nat.mul_one, (family m).mul_one, pred, Nat.mod_eq_of_lt pcap]
          exact congruent_refl _ _ _
        · have hrpos : 0 < r := by omega
          have flat := dyadic_flatten_block family m N hN hcap bound hrpos (by omega : r < p)
          have transported := congruent_mul family m (ih hrpos (by omega))
            (congruent_refl m (2 * N + 1) p)
          have combined := congruent_trans flat transported
          have recurrence := (family m).row_recurrence (p - 1) r
          rw [pred] at recurrence
          rw [← recurrence] at combined
          exact combined
  have residue := seq p hp (Nat.le_refl _)
  have sigSquare : signature m (p * p) = 2 * N := by rw [square, signature_pow m (2 * N) (by omega)]
  have eqSig := signature_agree_below (m := m) (r := 2 * N + 1) (by omega)
    (show p * p % 2 ^ (2 * N + 1) = (family m).mul (p - 1) p % 2 ^ (2 * N + 1) from
      by simpa only [congruent, Nat.min_eq_left (show 2 * N + 1 ≤ m by omega)] using residue)
    (by rw [sigSquare]; omega)
  rw [sigSquare, signature_mul, signature_pow m N (by omega)] at eqSig
  have act0 : act family m (p - 1) 0 = N := by rw [act_zero, pred, signature_pow m N (by omega)]
  have pmod : p % 2 = 0 := by
    exact (pow_mod_zero_iff N 1).mpr hN
  have sig0 : signature m (p - 1) = 0 := by
    by_cases hs : 1 ≤ signature m (p - 1)
    · have hz := (le_signature m (p - 1) 1 (by omega)).mp hs
      change (p - 1) % 2 = 0 at hz
      have ha : (p - 1 + 1) % 2 = 1 := by rw [Nat.add_mod, hz]
      rw [pred, pmod] at ha
      omega
    · omega
  exact ⟨sig0, act0, eqSig.symm⟩

#print axioms dyadic_flatten_block
#print axioms dyadic_step

end LaverLowerBounds.FiniteTable
