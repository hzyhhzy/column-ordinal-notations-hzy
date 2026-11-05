import LaverLowerBounds.DyadicBasics

set_option autoImplicit false

namespace LaverLowerBounds.FiniteTable

/-- The auxiliary critical triples used in Dougherty II, Theorem 3.1(a).
All points and actors here live in one finite table. -/
def DyadicAnchors (family : BinaryFamily) (m n : Nat) : Prop :=
  ∀ i, i < n → ∃ e,
    signature m e = 2 ^ n - 2 ^ (i + 1) ∧
    act family m e (2 ^ n - 2 ^ (i + 1)) = 2 ^ n - 2 ^ i ∧
    act family m e (2 ^ n - 2 ^ i) = 2 ^ n

def DyadicBound (family : BinaryFamily) (m N : Nat) : Prop :=
  ∀ a, a % 2 ^ N ≠ 0 →
    2 * N ≤ act family m a N ∧
    (2 ^ N < a % 2 ^ (2 * N) → 2 * N < act family m a N)

/-- The reverse-residue induction, including the strict second clause.
The only input triples are the previously constructed dyadic anchors. -/
theorem anchors_to_bound (family : BinaryFamily) (m n : Nat)
    (hcap : 2 * 2 ^ n < m) (anchors : DyadicAnchors family m n) :
    DyadicBound family m (2 ^ n) := by
  let N := 2 ^ n
  let p := 2 ^ N
  have hN : 0 < N := Nat.two_pow_pos n
  have hp : 0 < p := Nat.two_pow_pos N
  have hNm : N ≤ m := by omega
  have h2Nm : 2 * N ≤ m := by omega
  suffices main : ∀ v a, p - a % p = v → a % p ≠ 0 →
      2 * N ≤ act family m a N ∧
        (p < a % 2 ^ (2 * N) → 2 * N < act family m a N) by
    intro a ha
    exact main (p - a % p) a rfl ha
  intro v
  induction v using Nat.strongRecOn with
  | ind v ih =>
      intro a hv hnonzero
      have hreslt : a % p < p := Nat.mod_lt _ hp
      by_cases hlast : a % p = p - 1
      · exact full_low_block family m a N hN hcap hlast
      · have hres : a % p < p - 1 := by omega
        have hzero : act family m a 0 < N := act_zero_lt_of_residue family m a N hNm hres
        have hsig : signature m a < N := by
          by_cases hs : N ≤ signature m a
          · exact False.elim (hnonzero ((le_signature m a N hNm).mp hs))
          · omega
        have hhigh : N ≤ act family m a (N - 1) := by
          have he := act_gt_input family m a (N - 1) (by omega) (by omega)
          omega
        obtain ⟨i, hi, hstart, hroot⟩ := adjacent_crossing
          (fun i => act family m a (N - 2 ^ i)) n N
          (by simpa only [Nat.pow_zero] using hhigh)
          (by simpa only [N, Nat.sub_self] using hzero)
        obtain ⟨e, esig, eroot, enext⟩ := anchors i hi
        let b := (family m).mul a e
        have bsig : signature m b < N := by
          dsimp [b]
          rw [signature_mul, esig]
          exact hroot
        have bnz : b % p ≠ 0 := by
          intro hz
          have he := (le_signature m b N hNm).mpr hz
          omega
        have bres : a % p < b % p := by
          have hg := (family N).row_grows (a := a % p) (b := e) hreslt
          rw [(family N).mul_mod_left,
            ← (family m).projection (family N) (Nat.pow_dvd_pow 2 hNm)] at hg
          rcases hg with hz | hgt
          · exact False.elim (bnz hz)
          · exact hgt
        have hb := ih (p - b % p) (by omega) b rfl bnz
        have acted : act family m b (act family m a (N - 2 ^ i)) = act family m a N := by
          have he := act_application family m a e (N - 2 ^ i)
          rw [enext] at he
          exact he
        have hmono := act_mono family m b hstart
        rw [acted] at hmono
        refine ⟨Nat.le_trans hb.1 hmono, ?_⟩
        intro hbig
        have bnz2 : b % 2 ^ (2 * N) ≠ 0 := by
          intro hz
          have he := congrArg (fun z => z % p) hz
          rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (show N ≤ 2 * N by omega)), Nat.zero_mod] at he
          exact bnz he
        have bres2 : a % 2 ^ (2 * N) < b % 2 ^ (2 * N) := by
          have hg := (family (2 * N)).row_grows (a := a % 2 ^ (2 * N)) (b := e)
            (Nat.mod_lt _ (Nat.two_pow_pos _))
          rw [(family (2 * N)).mul_mod_left,
            ← (family m).projection (family (2 * N)) (Nat.pow_dvd_pow 2 h2Nm)] at hg
          rcases hg with hz | hgt
          · exact False.elim (bnz2 hz)
          · exact hgt
        exact Nat.lt_of_lt_of_le (hb.2 (Nat.lt_trans hbig bres2)) hmono

#print axioms anchors_to_bound

end LaverLowerBounds.FiniteTable
