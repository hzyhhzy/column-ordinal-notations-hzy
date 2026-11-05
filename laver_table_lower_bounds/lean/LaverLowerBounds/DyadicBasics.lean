import LaverLowerBounds.SignatureMovement
import LaverLowerBounds.FiniteCongruence

set_option autoImplicit false

namespace LaverLowerBounds.FiniteTable

theorem signature_pow (m r : Nat) (hr : r ≤ m) : signature m (2 ^ r) = r := by
  have hlo := (le_signature m (2 ^ r) r hr).mpr (by simp)
  have hle := signature_le m (2 ^ r)
  by_cases h : r < m
  · have hn : ¬ r + 1 ≤ signature m (2 ^ r) := by
      intro hs
      have he := (le_signature m (2 ^ r) (r + 1) (by omega)).mp hs
      have hf := (pow_mod_zero_iff r (r + 1)).mp he
      omega
    omega
  · omega

theorem act_zero (family : BinaryFamily) (m a : Nat) :
    act family m a 0 = signature m (a + 1) := by
  unfold act
  rw [Nat.pow_zero, (family m).mul_one]
  exact signature_mod_eq (by rw [Nat.mod_mod])

theorem act_distance (family : BinaryFamily) (m a : Nat) {x y : Nat}
    (hxy : x ≤ y) (hy : act family m a y < m) :
    act family m a x + (y - x) ≤ act family m a y := by
  induction y with
  | zero =>
      have : x = 0 := by omega
      subst x
      omega
  | succ y ih =>
      by_cases he : x = y + 1
      · subst x; omega
      · have hx : x ≤ y := by omega
        have hm := act_mono family m a (show y ≤ y + 1 by omega)
        have ih' := ih hx (by omega)
        have hn := act_next family m a y (by omega)
        omega

theorem act_rigid (family : BinaryFamily) (m a N : Nat)
    (h0 : act family m a 0 = N) (hN : act family m a N = 2 * N)
    (hcap : 2 * N < m) {i : Nat} (hi : i ≤ N) : act family m a i = N + i := by
  have hm := act_mono family m a hi
  have hlo := act_distance family m a (show 0 ≤ i by omega) (by omega)
  have hhi := act_distance family m a hi (by omega)
  rw [h0, Nat.sub_zero] at hlo
  omega

theorem act_gt_input (family : BinaryFamily) (m a x : Nat)
    (hs : signature m a ≤ x) (hx : x < m) : x < act family m a x := by
  by_cases hcap : act family m a x < m
  · have hmove := signature_lt_act family m a (by omega)
    have hd := act_distance family m a hs hcap
    omega
  · have := act_le family m a x; omega

/-- An attained nonsaturated critical index occupies a zero bit of the actor.
This is the finite form of Dougherty II, Lemma 2.9. -/
theorem act_residue_lt (family : BinaryFamily) (m a x : Nat)
    (hx : act family m a x < m) :
    a % 2 ^ (act family m a x + 1) < 2 ^ act family m a x := by
  let r := act family m a x
  have hr : r < m := hx
  have hp : (family m).mul a (2 ^ x) % 2 ^ (r + 1) = 2 ^ r :=
    residue_at_signature hr rfl
  rw [(family m).projection (family (r + 1)) (Nat.pow_dvd_pow 2 (by omega)),
    ← (family (r + 1)).mul_mod_left a (2 ^ x)] at hp
  have hg := (family (r + 1)).row_grows (a := a % 2 ^ (r + 1)) (b := 2 ^ x)
    (Nat.mod_lt _ (Nat.two_pow_pos _))
  rw [hp] at hg
  rcases hg with hz | hlt
  · have := Nat.two_pow_pos r; omega
  · exact hlt

theorem act_zero_lt_of_residue (family : BinaryFamily) (m a N : Nat)
    (hNm : N ≤ m) (hres : a % 2 ^ N < 2 ^ N - 1) : act family m a 0 < N := by
  by_cases hn : N ≤ act family m a 0
  · have hz := (le_act_iff family m a 0 N hNm).mp hn
    rw [Nat.pow_zero, (family N).mul_one, ← Nat.mod_add_mod] at hz
    have hp := Nat.two_pow_pos N
    rw [Nat.mod_eq_of_lt (by omega : a % 2 ^ N + 1 < 2 ^ N)] at hz
    omega
  · omega

/-- The last residue case in the reverse induction for the dyadic chain. -/
theorem full_low_block (family : BinaryFamily) (m a N : Nat)
    (hN : 0 < N) (hcap : 2 * N < m) (hres : a % 2 ^ N = 2 ^ N - 1) :
    2 * N ≤ act family m a N ∧
      (2 ^ N < a % 2 ^ (2 * N) → 2 * N < act family m a N) := by
  have hp := Nat.two_pow_pos N
  have h0 : N ≤ act family m a 0 := by
    apply (le_act_iff family m a 0 N (by omega)).mpr
    rw [Nat.pow_zero, (family N).mul_one, ← Nat.mod_add_mod, hres]
    have he : 2 ^ N - 1 + 1 = 2 ^ N := by omega
    rw [he, Nat.mod_self]
  have lower : 2 * N ≤ act family m a N := by
    by_cases hc : act family m a N < m
    · have hd := act_distance family m a (Nat.zero_le N) hc
      omega
    · omega
  refine ⟨lower, ?_⟩
  intro hbig
  by_cases hgt : 2 * N < act family m a N
  · exact hgt
  · have heq : act family m a N = 2 * N := by omega
    have hd := act_distance family m a (Nat.zero_le N) (by omega)
    have hzero : act family m a 0 = N := by omega
    have affine : ∀ i, i ≤ N → act family m a i = N + i :=
      fun _ hi => act_rigid family m a N hzero heq hcap hi
    have residues : ∀ i, i ≤ N → a % 2 ^ (N + i) = a % 2 ^ N := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
          intro hi
          have hiN : i ≤ N := by omega
          have ha : act family m a i = N + i := affine i hiN
          have hb := act_residue_lt family m a i (by omega)
          rw [ha] at hb
          have hm := Nat.mod_mod_of_dvd a (Nat.pow_dvd_pow 2 (show N + i ≤ N + i + 1 by omega))
          rw [Nat.mod_eq_of_lt hb] at hm
          simpa only [Nat.add_assoc] using hm.trans (ih hiN)
    have hr := residues N (Nat.le_refl _)
    rw [← Nat.two_mul, hres] at hr
    omega

theorem adjacent_crossing (f : Nat → Nat) (n target : Nat)
    (h0 : target ≤ f 0) (hn : f n < target) :
    ∃ i, i < n ∧ target ≤ f i ∧ f (i + 1) < target := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases h : f n < target
      · obtain ⟨i, hi, hlo, hhi⟩ := ih h
        exact ⟨i, by omega, hlo, hhi⟩
      · exact ⟨n, by omega, by omega, hn⟩

#print axioms full_low_block

end LaverLowerBounds.FiniteTable
