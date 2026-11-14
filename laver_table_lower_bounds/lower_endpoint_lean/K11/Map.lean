import K11.Bootstrap

set_option autoImplicit false
namespace LaverLowerBounds.FiniteTable.K11.Core
variable {family : BinaryFamily} {m : Nat}

def map (bg : Core family m) (H : Nat) (h0 : act family m H 0 = 0)
    (h1 : act family m H 1 = 1) (hcap : act family m H bg.mu < m) : Core family m := by
  have kr : bg.k < bg.r := Nat.lt_trans bg.k_sigma bg.sigma_r
  have km : bg.k < bg.mu := Nat.lt_trans kr bg.r_mu
  have sm : bg.sigma < bg.mu := Nat.lt_trans bg.sigma_r bg.r_mu
  have bounded {x : Nat} (hx : x ≤ bg.mu) : act family m H x < m :=
    Nat.lt_of_le_of_lt (act_mono family m H hx) hcap
  refine {
    k := act family m H bg.k, sigma := act family m H bg.sigma
    r := act family m H bg.r, mu := act family m H bg.mu
    k_lower := Nat.le_trans bg.k_lower (le_act family m H bg.k (Nat.le_of_lt bg.k_cap))
    k_sigma := act_strict_below_cap family m H _ _ bg.k_sigma (bounded (Nat.le_of_lt sm))
    sigma_r := act_strict_below_cap family m H _ _ bg.sigma_r (bounded (Nat.le_of_lt bg.r_mu))
    r_mu := act_strict_below_cap family m H _ _ bg.r_mu hcap
    mu_cap := hcap
    j := (family m).mul H bg.j, j2 := (family m).mul H bg.j2
    j3 := (family m).mul H bg.j3, j10 := (family m).mul H bg.j10
    K := (family m).mul H bg.K
    j_signature := by rw [signature_mul, bg.j_signature, h0]
    j2_signature := by rw [signature_mul, bg.j2_signature, h1]
    j3_signature := by rw [signature_mul, bg.j3_signature, h0]
    j10_signature := by rw [signature_mul, bg.j10_signature, h1]
    j_zero := (application_at family m H bg.j h0 bg.j_zero).trans h1
    j_one := application_at family m H bg.j h1 bg.j_one
    j_next := application_at family m H bg.j rfl bg.j_next
    j_j := by rw [← (family m).mul_distrib, bg.j_j]
    j2_one := application_at family m H bg.j2 h1 bg.j2_one
    j3_zero := application_at family m H bg.j3 h0 bg.j3_zero
    j3_one := application_at family m H bg.j3 h1 bg.j3_one
    j3_next := application_at family m H bg.j3 rfl bg.j3_next
    j10_one := application_at family m H bg.j10 h1 bg.j10_one
    j10_next := application_at family m H bg.j10 rfl bg.j10_next
    K_one := application_at family m H bg.K h1 bg.K_one
    j2_j := by rw [← (family m).mul_distrib, bg.j2_j]
    j10_j := by rw [← (family m).mul_distrib, bg.j10_j]
    K_j3 := congruent_transport family m bg.K_j3 H }

#print axioms map
end LaverLowerBounds.FiniteTable.K11.Core
