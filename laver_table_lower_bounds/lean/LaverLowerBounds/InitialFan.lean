import LaverLowerBounds.InitialTerms

set_option autoImplicit false

namespace LaverLowerBounds.FiniteTable.FanSeed

variable {family : BinaryFamily} {m : Nat}

def initialPoint (s : FanSeed family m) : Nat → Nat
  | 0 => s.points.point 0
  | 1 => s.points.point 1
  | 2 => s.points.point 2
  | 3 => s.points.point 3
  | 4 => s.points.point 5
  | 5 => s.alpha
  | 6 => s.zeta
  | _ => s.rho

def initialOwner (s : FanSeed family m) (row : Nat) : Nat := if row = 0 then s.f else s.J

theorem initial_port (s : FanSeed family m) {row : Nat} (hr : row < 2) :
    BandPort family m s.initialPoint 0 3 (row + 1) (s.initialOwner row) := by
  have hd := s.termData
  match row with
  | 0 =>
      refine ⟨hd.f_signature, ?_, hd.f3⟩
      intro t ht
      match t with
      | 0 => exact hd.f0
      | 1 => exact hd.f1
      | n + 2 => omega
  | 1 =>
      refine ⟨hd.J_signature, ?_, hd.J3⟩
      intro t ht
      match t with
      | 0 => exact hd.J0
      | 1 => exact hd.J1
      | 2 => exact hd.J2
      | n + 3 => omega
  | n + 2 => omega

def initialFan (s : FanSeed family m) : ClosedFan family m 2 := by
  have hd := s.termData
  have h56 : s.points.point 5 < s.alpha := Nat.lt_trans hd.five_lt_beta hd.beta_lt_alpha
  have hadj : ∀ i, i < 7 → s.initialPoint i < s.initialPoint (i + 1) := by
    intro i hi
    match i with
    | 0 => exact s.points.strict (by decide : 0 < 1) (by decide)
    | 1 => exact s.points.strict (by decide : 1 < 2) (by decide)
    | 2 => exact s.points.strict (by decide : 2 < 3) (by decide)
    | 3 => exact s.points.strict (by decide : 3 < 5) (by decide)
    | 4 => exact h56
    | 5 => exact hd.alpha_lt_zeta
    | 6 => exact hd.zeta_lt_rho
    | n + 7 => omega
  exact {
    chain := PointChain.ofAdjacent s.initialPoint hadj
      (Nat.lt_trans hd.rho_lt_six (s.points.below (by decide)))
    ports r hr := ⟨s.initialOwner r, s.initial_port hr⟩
    closer := s.L2
    closer_signature := hd.L2_signature
    closer_first := hd.L2_first
    closer_next := hd.L2_next }

theorem initial_fan_endpoint (s : FanSeed family m) :
    s.initialFan.endpoint < s.points.point 6 := s.termData.rho_lt_six

theorem initial_fan_bottom (s : FanSeed family m) :
    s.initialFan.chain.point 0 = 0 ∧ s.initialFan.chain.point 1 = 1 := ⟨s.zero, s.one⟩

#print axioms initialFan

end LaverLowerBounds.FiniteTable.FanSeed
