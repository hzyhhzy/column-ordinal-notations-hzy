import LaverLowerBounds.HigherConstants
import LaverLowerBounds.ClosedFan

set_option autoImplicit false

namespace LaverLowerBounds.FiniteTable

theorem application_at (family : BinaryFamily) (m a b : Nat) {x y z : Nat}
    (ha : act family m a x = y) (hb : act family m b x = z) :
    act family m ((family m).mul a b) y = act family m a z := by
  rw [← ha, act_application, hb]

/-- Named finite seed data; the construction below supplies every field from
the threshold hypothesis. The indices are positions in the theta chain. -/
structure FanSeed (family : BinaryFamily) (m : Nat) where
  points : PointChain m 8
  j : Nat
  K : Nat
  zero : points.point 0 = 0
  one : points.point 1 = 1
  j_signature : signature m j = points.point 0
  K_signature : signature m K = points.point 0
  j_image : ∀ i, i ≤ 2 → act family m j (points.point i) = points.point (i + 1)
  K_image : ∀ i, i ≤ 5 → act family m K (points.point i) = points.point (i + 2)
  square : congruent m (points.point 4) K ((family m).comp j j)

def theta (family : BinaryFamily) (m : Nat) : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 4
  | 4 => act family m 7 2
  | 5 => act family m 11 4
  | 6 => act family m 10 4
  | 7 => act family m 11 (act family m 11 4)
  | _ => act family m 9 4

def fanSeed (family : BinaryFamily) (m : Nat) (hm : PeriodAtLeast32 (family m)) : FanSeed family m := by
  have hd := higherData family m hm
  have h9 : 9 ≤ m := Nat.le_of_lt (threshold_gt_nine family m hm)
  have hadj : ∀ i, i < 8 → theta family m i < theta family m (i + 1) := by
    intro i hi
    match i with
    | 0 => change 0 < 1; decide
    | 1 => change 1 < 2; decide
    | 2 => change 2 < 4; decide
    | 3 => exact Nat.lt_of_lt_of_le (by decide : 4 < 9) hd.mu_lower
    | 4 => exact hd.mu_lt_five
    | 5 => exact hd.five_lt_six
    | 6 => exact hd.six_lt_seven
    | 7 => exact hd.seven_lt_eight
    | n + 8 => omega
  let points : PointChain m 8 := PointChain.ofAdjacent (theta family m) hadj
    (Nat.lt_trans hd.eight_lt_upper hd.upper_below)
  refine ⟨points, 1, 11, rfl, rfl, ?_, ?_, ?_, ?_, hd.square⟩
  · exact signature_from_nine m 1 0 h9 (by decide) (by decide)
  · exact signature_from_nine m 11 0 h9 (by decide) (by decide)
  · intro i hi
    match i with
    | 0 => exact act_from_low family m 1 0 2 1 h9 (LowProducts.v1_1 (family 9)) (by decide) (by decide)
    | 1 => exact act_from_low family m 1 1 12 2 h9 (LowProducts.v1_2 (family 9)) (by decide) (by decide)
    | 2 => exact act_from_low family m 1 2 240 4 h9 (LowProducts.v1_4 (family 9)) (by decide) (by decide)
    | n + 3 => omega
  · intro i hi
    match i with
    | 0 => exact hd.k0
    | 1 => exact hd.k1
    | 2 => exact hd.k2
    | 3 => rfl
    | 4 => exact hd.k_mu
    | 5 => rfl
    | n + 6 => omega

#print axioms fanSeed

end LaverLowerBounds.FiniteTable
