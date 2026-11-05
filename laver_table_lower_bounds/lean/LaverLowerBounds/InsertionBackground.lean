import LaverLowerBounds.IteratedFanInsertion

set_option autoImplicit false

namespace LaverLowerBounds.FiniteTable

def OwnedFan.map {family : BinaryFamily} {m h : Nat} (old : OwnedFan family m h) (H : Nat)
    (hcap : act family m H old.fan.endpoint < m) (h0 : act family m H 0 = 0)
    (h1 : act family m H 1 = 1) : OwnedFan family m h where
  fan := old.fan.map H hcap
  owner r := (family m).mul H (old.owner r)
  port r hr := (old.port r hr).transport H 0 (h + 1) (fun _ _ => rfl) (fun _ _ => rfl)
  zero := by change act family m H (old.fan.chain.point 0) = 0; rw [old.zero, h0]
  one := by change act family m H (old.fan.chain.point 1) = 1; rw [old.one, h1]

/-- This package separates actor codes from critical-point indices. They are
different data after transport, even when both were written 2 or 3 originally.
The native package and its bounded transport are proved, not assumed. -/
structure InsertionBackground (family : BinaryFamily) (m : Nat) where
  k : Nat
  sigma : Nat
  r : Nat
  mu : Nat
  a : Nat
  c : Nat
  k_lower : 2 ≤ k
  k_sigma : k < sigma
  sigma_r : sigma < r
  r_mu : r < mu
  mu_a : mu < a
  a_c : a < c
  c_cap : c < m
  j : Nat
  j2 : Nat
  j3 : Nat
  j10 : Nat
  K : Nat
  e : Nat
  j3_bound : j3 < 2 ^ m
  j_signature : signature m j = 0
  j2_signature : signature m j2 = 1
  j3_signature : signature m j3 = 0
  j10_signature : signature m j10 = 1
  e_signature : signature m e = k
  j_zero : act family m j 0 = 1
  j_one : act family m j 1 = k
  j2_one : act family m j2 1 = k
  j3_zero : act family m j3 0 = k
  j3_one : act family m j3 1 = sigma
  j3_next : act family m j3 k = r
  j10_one : act family m j10 1 = k
  j10_next : act family m j10 k = mu
  K_one : act family m K 1 = r
  j2_j : (family m).mul j2 j = j3
  j10_j : (family m).mul j10 j = K
  K_j3 : congruent m sigma K j3
  initial : OwnedFan family m 2
  initial_below : initial.fan.endpoint < a
  delta : Nat
  D_signature : signature m ((family m).mul e j3) = 0
  D_zero : act family m ((family m).mul e j3) 0 = initial.fan.chain.point 3
  D_one : act family m ((family m).mul e j3) 1 = delta
  D_next : act family m ((family m).mul e j3) (initial.fan.chain.point 3) = initial.fan.chain.point 4
  delta_gap : initial.fan.chain.point 3 < delta ∧ delta < initial.fan.chain.point 4
  initial_common : ∀ i, i < 2 → congruent m delta (initial.owner i) ((family m).mul e j3)

def nativeInsertionBackground (family : BinaryFamily) (m : Nat) (hm : PeriodAtLeast32 (family m)) :
    InsertionBackground family m := by
  let s := fanSeed family m hm
  have hd := higherData family m hm
  have split := FanSeed.firstSplit family m hm
  have h9 : 9 ≤ m := Nat.le_of_lt (threshold_gt_nine family m hm)
  have hp : 512 ≤ 2 ^ m := Nat.pow_le_pow_right (n := 2) (by decide) h9
  have sig10 := (ten_low family m hm).1
  have ten1 := (ten_low family m hm).2.1
  have ten2 := (ten_low family m hm).2.2
  exact {
    k := 2, sigma := 3, r := 4, mu := act family m 7 2
    a := theta family m 6, c := theta family m 7
    k_lower := by decide
    k_sigma := by decide
    sigma_r := by decide
    r_mu := Nat.lt_of_lt_of_le (by decide : 4 < 9) hd.mu_lower
    mu_a := Nat.lt_trans hd.mu_lt_five hd.five_lt_six
    a_c := hd.six_lt_seven
    c_cap := Nat.lt_trans hd.seven_lt_eight (Nat.lt_trans hd.eight_lt_upper hd.upper_below)
    j := 1, j2 := 2, j3 := 3, j10 := 10, K := 11, e := s.e
    j3_bound := by omega
    j_signature := signature_from_nine m 1 0 h9 (by decide) (by decide)
    j2_signature := signature_from_nine m 2 1 h9 (by decide) (by decide)
    j3_signature := signature_from_nine m 3 0 h9 (by decide) (by decide)
    j10_signature := sig10
    e_signature := s.termData.e_signature
    j_zero := act_from_low family m 1 0 2 1 h9 (LowProducts.v1_1 (family 9)) (by decide) (by decide)
    j_one := act_from_low family m 1 1 12 2 h9 (LowProducts.v1_2 (family 9)) (by decide) (by decide)
    j2_one := act_from_low family m 2 1 12 2 h9 (LowProducts.v2_2 (family 9)) (by decide) (by decide)
    j3_zero := act_from_low family m 3 0 4 2 h9 (LowProducts.v3_1 (family 9)) (by decide) (by decide)
    j3_one := act_from_low family m 3 1 8 3 h9 (LowProducts.v3_2 (family 9)) (by decide) (by decide)
    j3_next := act_from_low family m 3 2 464 4 h9 (LowProducts.v3_4 (family 9)) (by decide) (by decide)
    j10_one := ten1, j10_next := ten2, K_one := hd.k1
    j2_j := mul_next_small family m 2 h9 (by decide)
    j10_j := mul_next_small family m 10 h9 (by decide)
    K_j3 := congruent_trans (congruent_lower hd.square (by have := hd.mu_lower; omega))
      (congruent_symm (low_square family m h9))
    initial := s.ownedInitial
    initial_below := s.initial_fan_endpoint
    delta := s.firstDelta
    D_signature := split.signature_eq, D_zero := split.zero_image
    D_one := split.one_image, D_next := split.next_image, delta_gap := split.gap
    initial_common := split.common }

namespace InsertionBackground

variable {family : BinaryFamily} {m : Nat}

/-- All required data transport under H(c)<m. No image of theta8 is required. -/
def map (bg : InsertionBackground family m) (H : Nat)
    (h0 : act family m H 0 = 0) (h1 : act family m H 1 = 1)
    (hcap : act family m H bg.c < m) : InsertionBackground family m := by
  have hkc : bg.k < bg.c := by have := bg.k_sigma; have := bg.sigma_r; have := bg.r_mu; have := bg.mu_a; have := bg.a_c; omega
  have hsc : bg.sigma < bg.c := by have := bg.sigma_r; have := bg.r_mu; have := bg.mu_a; have := bg.a_c; omega
  have hrc : bg.r < bg.c := by have := bg.r_mu; have := bg.mu_a; have := bg.a_c; omega
  have hmc : bg.mu < bg.c := Nat.lt_trans bg.mu_a bg.a_c
  have bounded {x : Nat} (hx : x ≤ bg.c) : act family m H x < m :=
    Nat.lt_of_le_of_lt (act_mono family m H hx) hcap
  have hiC : bg.initial.fan.endpoint < bg.c := Nat.lt_trans bg.initial_below bg.a_c
  have hiCap : act family m H bg.initial.fan.endpoint < m := bounded (Nat.le_of_lt hiC)
  let initial := bg.initial.map H hiCap h0 h1
  have dltC : bg.delta < bg.c := by
    have hpoint : bg.initial.fan.chain.point 4 < bg.initial.fan.endpoint :=
      bg.initial.fan.chain.strict (by decide) (Nat.le_refl _)
    exact Nat.lt_trans bg.delta_gap.2 (Nat.lt_trans hpoint hiC)
  have v1ltC : bg.initial.fan.chain.point 4 < bg.c :=
    Nat.lt_trans (bg.initial.fan.chain.strict (by decide : 4 < 7) (Nat.le_refl _)) hiC
  have Dnew : (family m).mul ((family m).mul H bg.e) ((family m).mul H bg.j3) =
      (family m).mul H ((family m).mul bg.e bg.j3) := ((family m).mul_distrib _ _ _).symm
  refine {
    k := act family m H bg.k, sigma := act family m H bg.sigma
    r := act family m H bg.r, mu := act family m H bg.mu
    a := act family m H bg.a, c := act family m H bg.c
    k_lower := Nat.le_trans bg.k_lower (le_act family m H bg.k (by have := bg.c_cap; omega))
    k_sigma := act_strict_below_cap family m H _ _ bg.k_sigma (bounded (Nat.le_of_lt hsc))
    sigma_r := act_strict_below_cap family m H _ _ bg.sigma_r (bounded (Nat.le_of_lt hrc))
    r_mu := act_strict_below_cap family m H _ _ bg.r_mu (bounded (Nat.le_of_lt hmc))
    mu_a := act_strict_below_cap family m H _ _ bg.mu_a (bounded (Nat.le_of_lt bg.a_c))
    a_c := act_strict_below_cap family m H _ _ bg.a_c hcap
    c_cap := hcap
    j := (family m).mul H bg.j, j2 := (family m).mul H bg.j2
    j3 := (family m).mul H bg.j3, j10 := (family m).mul H bg.j10
    K := (family m).mul H bg.K, e := (family m).mul H bg.e
    j3_bound := (family m).mul_lt _ _
    j_signature := by rw [signature_mul, bg.j_signature, h0]
    j2_signature := by rw [signature_mul, bg.j2_signature, h1]
    j3_signature := by rw [signature_mul, bg.j3_signature, h0]
    j10_signature := by rw [signature_mul, bg.j10_signature, h1]
    e_signature := by rw [signature_mul, bg.e_signature]
    j_zero := (application_at family m H bg.j h0 bg.j_zero).trans h1
    j_one := application_at family m H bg.j h1 bg.j_one
    j2_one := application_at family m H bg.j2 h1 bg.j2_one
    j3_zero := application_at family m H bg.j3 h0 bg.j3_zero
    j3_one := application_at family m H bg.j3 h1 bg.j3_one
    j3_next := application_at family m H bg.j3 rfl bg.j3_next
    j10_one := application_at family m H bg.j10 h1 bg.j10_one
    j10_next := application_at family m H bg.j10 rfl bg.j10_next
    K_one := application_at family m H bg.K h1 bg.K_one
    j2_j := by rw [← (family m).mul_distrib, bg.j2_j]
    j10_j := by rw [← (family m).mul_distrib, bg.j10_j]
    K_j3 := congruent_transport family m bg.K_j3 H
    initial := initial
    initial_below := act_strict_below_cap family m H _ _ bg.initial_below (bounded (Nat.le_of_lt bg.a_c))
    delta := act family m H bg.delta
    D_signature := by rw [Dnew, signature_mul, bg.D_signature, h0]
    D_zero := ?_, D_one := ?_, D_next := ?_, delta_gap := ?_, initial_common := ?_ }
  · rw [Dnew]
    exact application_at family m H _ h0 bg.D_zero
  · rw [Dnew]
    exact application_at family m H _ h1 bg.D_one
  · rw [Dnew]
    exact application_at family m H _ rfl bg.D_next
  · exact ⟨act_strict_below_cap family m H _ _ bg.delta_gap.1 (bounded (Nat.le_of_lt dltC)),
      act_strict_below_cap family m H _ _ bg.delta_gap.2 (bounded (Nat.le_of_lt v1ltC))⟩
  · intro i hi
    rw [Dnew]
    exact congruent_transport family m (bg.initial_common i hi) H

#print axioms map

end InsertionBackground

#print axioms nativeInsertionBackground

end LaverLowerBounds.FiniteTable
