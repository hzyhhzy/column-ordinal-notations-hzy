import LaverLowerBounds.DyadicStep

set_option autoImplicit false

namespace LaverLowerBounds.FiniteTable

/-- Simultaneous dyadic construction, proved entirely in finite tables.
The induction reconstructs the auxiliary triples after each exact segment. -/
theorem dyadic_anchors (family : BinaryFamily) (n : Nat) :
    ∀ m, 2 ^ n < m → DyadicAnchors family m n := by
  induction n with
  | zero =>
      intro m hm i hi
      omega
  | succ n ih =>
      intro m hm
      let N := 2 ^ n
      have hN : 0 < N := Nat.two_pow_pos n
      have powNext : 2 ^ (n + 1) = 2 * N := by rw [Nat.pow_succ, Nat.mul_comm]
      have hcap : 2 * N < m := by rwa [powNext] at hm
      have anchors := ih m (show 2 ^ n < m by omega)
      have bounds := anchors_to_bound family m n hcap anchors
      obtain ⟨esig, ezero, enext⟩ := dyadic_step family m N hN hcap bounds
      let e := 2 ^ N - 1
      have affine {x : Nat} (hx : x ≤ N) : act family m e x = N + x :=
        act_rigid family m e N ezero enext hcap hx
      intro i hi
      by_cases hin : i = n
      · subst i
        refine ⟨e, ?_, ?_, ?_⟩
        · simpa only [Nat.sub_self] using esig
        · have hs : 2 ^ (n + 1) - 2 ^ n = N := by rw [powNext]; omega
          simpa only [Nat.sub_self, hs] using ezero
        · have hs : 2 ^ (n + 1) - 2 ^ n = N := by rw [powNext]; omega
          rw [hs, powNext]
          exact enext
      · have hi' : i < n := by omega
        obtain ⟨b, bsig, bfirst, bnext⟩ := anchors i hi'
        have hloPow : 2 ^ (i + 1) ≤ N := Nat.pow_le_pow_right (by decide) (by omega)
        have hmidPow : 2 ^ i ≤ N := Nat.pow_le_pow_right (by decide) (by omega)
        have hroot : act family m e (N - 2 ^ (i + 1)) = 2 ^ (n + 1) - 2 ^ (i + 1) := by
          rw [affine (Nat.sub_le _ _), powNext]
          omega
        have hstart : act family m e (N - 2 ^ i) = 2 ^ (n + 1) - 2 ^ i := by
          rw [affine (Nat.sub_le _ _), powNext]
          omega
        refine ⟨(family m).mul e b, ?_, ?_, ?_⟩
        · rw [signature_mul, bsig]
          exact hroot
        · have he := act_application family m e b (N - 2 ^ (i + 1))
          rw [hroot, bfirst, hstart] at he
          exact he
        · have he := act_application family m e b (N - 2 ^ i)
          rw [hstart, bnext, enext] at he
          simpa only [powNext] using he

theorem standard_segment (family : BinaryFamily) (m n : Nat)
    (hcap : 2 ^ (n + 1) < m) :
    signature m (2 ^ (2 ^ n) - 1) = 0 ∧
    act family m (2 ^ (2 ^ n) - 1) 0 = 2 ^ n ∧
    act family m (2 ^ (2 ^ n) - 1) (2 ^ n) = 2 ^ (n + 1) := by
  have hp := Nat.two_pow_pos n
  have hc : 2 * 2 ^ n < m := by rw [Nat.pow_succ, Nat.mul_comm] at hcap; exact hcap
  have anchors := dyadic_anchors family n m (by omega)
  have result := dyadic_step family m (2 ^ n) hp hc (anchors_to_bound family m n hc anchors)
  simpa only [Nat.pow_succ, Nat.mul_comm (2 ^ n) 2] using result

/-- The actual l-segment line (0;1,2^l), whenever its endpoint is below the cap.
No large-cardinal, global-freeness, period-growth, or table-existence oracle is
used: only the finite defining equations of the supplied BinaryFamily. -/
theorem standard_line (family : BinaryFamily) (m l : Nat) (hcap : 2 ^ l < m) :
    Lined family m 0 l 1 (2 ^ l) := by
  induction l with
  | zero => exact .nil hcap
  | succ l ih =>
      have hlt : 2 ^ l < 2 ^ (l + 1) := Nat.pow_lt_pow_succ (by decide)
      have first := ih (Nat.lt_trans hlt hcap)
      obtain ⟨hsig, hfirst, hnext⟩ := standard_segment family m l hcap
      have last : Lined family m 0 1 (2 ^ l) (2 ^ (l + 1)) :=
        .cons (2 ^ (2 ^ l) - 1) hsig hfirst hnext hlt (.nil hcap)
      exact first.append last

#print axioms dyadic_anchors
#print axioms standard_segment
#print axioms standard_line

end LaverLowerBounds.FiniteTable
