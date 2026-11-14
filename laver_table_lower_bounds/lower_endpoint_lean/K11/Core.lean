import LaverLowerBounds.InsertionBackground

set_option autoImplicit false

namespace LaverLowerBounds.FiniteTable.K11

/-- The low background alone. Unlike the older package this has no assumed
height-two fan and no high entry point. We construct the first fan below. -/
structure Core (family : BinaryFamily) (m : Nat) where
  k : Nat
  sigma : Nat
  r : Nat
  mu : Nat
  k_lower : 2 ≤ k
  k_sigma : k < sigma
  sigma_r : sigma < r
  r_mu : r < mu
  mu_cap : mu < m
  j : Nat
  j2 : Nat
  j3 : Nat
  j10 : Nat
  K : Nat
  j_signature : signature m j = 0
  j2_signature : signature m j2 = 1
  j3_signature : signature m j3 = 0
  j10_signature : signature m j10 = 1
  j_zero : act family m j 0 = 1
  j_one : act family m j 1 = k
  j_next : act family m j k = r
  j_j : (family m).mul j j = j2
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

namespace Core
variable {family : BinaryFamily} {m : Nat}

theorem k_cap (bg : Core family m) : bg.k < m :=
  Nat.lt_trans bg.k_sigma (Nat.lt_trans bg.sigma_r (Nat.lt_trans bg.r_mu bg.mu_cap))

end Core
end LaverLowerBounds.FiniteTable.K11
