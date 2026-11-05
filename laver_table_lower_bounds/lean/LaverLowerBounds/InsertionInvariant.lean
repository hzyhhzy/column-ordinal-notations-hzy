import LaverLowerBounds.TransportWord

set_option autoImplicit false

namespace LaverLowerBounds.FiniteTable

structure InsertionInvariant {family : BinaryFamily} {m h : Nat} (old : OwnedFan family m h) where
  P : List Nat
  Q : Nat
  U : Nat
  Q_signature : signature m Q = 2
  U_signature : 2 ≤ signature m U
  Q_four_below : act family m Q 4 < m
  high_factors : WordAboveOne m P
  epsilon : Nat
  epsilon_above : old.fan.chain.point (h + 2) < epsilon
  common : ∀ r, r < h → congruent m epsilon (old.owner r) (old.owner 0)
  first : old.owner 0 = wordTerm family m (P ++ [(family m).mul Q 10, U]) 3

namespace InsertionInvariant

variable {family : BinaryFamily} {m h : Nat} {old : OwnedFan family m h}

def whole (ctx : InsertionInvariant old) := ctx.P ++ [(family m).mul ctx.Q 10, ctx.U]
def W (ctx : InsertionInvariant old) := wordTerm family m ctx.whole 2
def Z (ctx : InsertionInvariant old) := wordTerm family m ctx.P ((family m).mul ctx.Q 3)
def D (ctx : InsertionInvariant old) := (family m).mul ctx.W ctx.Z
def delta (ctx : InsertionInvariant old) := act family m ctx.W (wordAct family m ctx.P (act family m ctx.Q 3))

structure Rebuild (ctx : InsertionInvariant old) : Prop where
  W_signature_above : 1 < signature m ctx.W
  signature_eq : signature m ctx.D = 0
  zero_image : act family m ctx.D 0 = old.fan.chain.point (h + 1)
  one_image : act family m ctx.D 1 = ctx.delta
  next_image : act family m ctx.D (old.fan.chain.point (h + 1)) = old.fan.chain.point (h + 2)
  gap : old.fan.chain.point (h + 1) < ctx.delta ∧ ctx.delta < old.fan.chain.point (h + 2)
  common : ∀ r, r < h → congruent m ctx.delta (old.owner r) ctx.D

theorem rebuild (ctx : InsertionInvariant old) (hm : PeriodAtLeast32 (family m)) (hh : 1 ≤ h) :
    Rebuild ctx := by
  have low := insertionLowData family m hm ctx.Q ctx.U ctx.Q_signature ctx.U_signature ctx.Q_four_below
  have h9 : 9 ≤ m := Nat.le_of_lt (threshold_gt_nine family m hm)
  have sig2 : signature m 2 = 1 := signature_from_nine m 2 1 h9 (by decide) (by decide)
  have j21 := act_from_low family m 2 1 12 2 h9 (LowProducts.v2_2 (family 9)) (by decide) (by decide)
  have j30 := act_from_low family m 3 0 4 2 h9 (LowProducts.v3_1 (family 9)) (by decide) (by decide)
  have n2 : (family m).mul 2 1 = 3 := mul_next_small family m 2 h9 (by decide)
  let T := (family m).mul ctx.Q 10
  let X := (family m).mul T ((family m).mul ctx.U 1)
  let Y := wordTerm family m ctx.whole 1
  let root := wordAct family m ctx.P (act family m ctx.Q 2)
  let middle := wordAct family m ctx.P (act family m ctx.Q 3)
  let upper := wordAct family m ctx.P (act family m ctx.Q 4)
  have P0 : wordAct family m ctx.P 0 = 0 := word_fixes_low family m ctx.high_factors (by decide)
  have P1 : wordAct family m ctx.P 1 = 1 := word_fixes_low family m ctx.high_factors (by decide)
  have T0 : act family m T 0 = 0 := fixes_below_signature family m T 0 (by rw [low.T_signature]; decide)
  have U0 : act family m ctx.U 0 = 0 := fixes_below_signature family m ctx.U 0 (by have := ctx.U_signature; omega)
  have U1 : act family m ctx.U 1 = 1 := fixes_below_signature family m ctx.U 1 (by have := ctx.U_signature; omega)
  have whole0 : wordAct family m ctx.whole 0 = 0 := by
    rw [whole, wordAct_append]
    simp only [wordAct, U0]
    change wordAct family m ctx.P (act family m T 0) = 0
    rw [T0, P0]
  have whole1 : wordAct family m ctx.whole 1 = root := by
    rw [whole, wordAct_append]
    simp only [wordAct, U1, low.T_one]
    rfl
  have Yeq : Y = wordTerm family m ctx.P X := by
    dsimp [Y, whole]
    rw [wordTerm_append]
    rfl
  have Y0 : act family m Y 0 = root := by
    have he := word_action family m ctx.P X 0
    rw [← Yeq, P0, low.X_zero] at he
    exact he
  have Y1 : act family m Y 1 = upper := by
    have he := word_action family m ctx.P X 1
    rw [← Yeq, P1, low.X_one] at he
    exact he
  have Zsig : signature m ctx.Z = 0 := by
    rw [Z, word_signature, low.Z_signature, P0]
  have Z0 : act family m ctx.Z 0 = root := by
    have he := word_action family m ctx.P ((family m).mul ctx.Q 3) 0
    rw [P0, low.Z_zero] at he
    exact he
  have Z1 : act family m ctx.Z 1 = middle := by
    have he := word_action family m ctx.P ((family m).mul ctx.Q 3) 1
    rw [P1, low.Z_one] at he
    exact he
  have Zroot : act family m ctx.Z root = upper := by
    have he := word_action family m ctx.P ((family m).mul ctx.Q 3) (act family m ctx.Q 2)
    rw [low.Z_next] at he
    exact he
  have YZ : congruent m middle Y ctx.Z := by
    have he := word_congruent family m ctx.P low.common
    rw [← Yeq] at he
    exact he
  have ownWhole : old.owner 0 = wordTerm family m ctx.whole 3 := ctx.first
  have ownWY : old.owner 0 = (family m).mul ctx.W Y := by
    rw [ownWhole, ← n2, word_application]
    rfl
  have Wsig : signature m ctx.W = root := by rw [W, word_signature, sig2, whole1]
  have q2cap : act family m ctx.Q 2 ≤ m := act_le family m ctx.Q 2
  have rootAbove : 1 < root := by
    have he := signature_lt_act family m ctx.Q (by rw [ctx.Q_signature]; omega)
    rw [ctx.Q_signature] at he
    have hb := (word_bounds family m ctx.P q2cap).1
    omega
  have W0 : act family m ctx.W 0 = 0 := fixes_below_signature family m ctx.W 0 (by rw [Wsig]; omega)
  have W1 : act family m ctx.W 1 = 1 := fixes_below_signature family m ctx.W 1 (by rw [Wsig]; exact rootAbove)
  have port := old.port 0 (by omega)
  have own0 : act family m (old.owner 0) 0 = old.fan.chain.point (h + 1) := by
    have he := port.image 0 (by decide)
    simpa only [Nat.add_zero, old.zero] using he
  have own1 : act family m (old.owner 0) 1 = old.fan.chain.point (h + 2) := by
    have he := port.image 1 (by decide)
    simpa only [Nat.zero_add, old.one, Nat.add_assoc] using he
  have whole2 : wordAct family m ctx.whole 2 = old.fan.chain.point (h + 1) := by
    have he := word_action family m ctx.whole 3 0
    rw [whole0, j30, ← ownWhole, own0] at he
    exact he.symm
  have Wroot : act family m ctx.W root = old.fan.chain.point (h + 1) := by
    have he := word_action family m ctx.whole 2 1
    rw [whole1, j21, whole2] at he
    exact he
  have Wupper : act family m ctx.W upper = old.fan.chain.point (h + 2) := by
    have he := application_at family m ctx.W Y W1 Y1
    rw [← ownWY, own1] at he
    exact he.symm
  have V1cap : old.fan.chain.point (h + 2) < m := old.fan.chain.below (by omega)
  have upperLe : upper ≤ m := (word_bounds family m ctx.P (Nat.le_of_lt ctx.Q_four_below)).2
  have upperCap : upper < m := by
    have he := le_act family m ctx.W upper upperLe
    rw [Wupper] at he
    omega
  have midUpper : middle < upper := word_strict family m ctx.P low.gap.2
    (Nat.le_of_lt ctx.Q_four_below) upperCap
  have rootMid : root < middle := word_strict family m ctx.P low.gap.1
    (act_le family m ctx.Q 3) (Nat.lt_trans midUpper upperCap)
  have gapHi : ctx.delta < old.fan.chain.point (h + 2) := by
    have he := act_strict_below_cap family m ctx.W middle upper midUpper (by rw [Wupper]; exact V1cap)
    rwa [Wupper] at he
  have gapLo : old.fan.chain.point (h + 1) < ctx.delta := by
    have he := act_strict_below_cap family m ctx.W root middle rootMid (Nat.lt_trans gapHi V1cap)
    rwa [Wroot] at he
  have ownerD : congruent m ctx.delta (old.owner 0) ctx.D := by
    have he := congruent_transport family m YZ ctx.W
    rw [← ownWY] at he
    exact he
  refine ⟨by rw [Wsig]; exact rootAbove, ?_, ?_, ?_, ?_, ⟨gapLo, gapHi⟩, ?_⟩
  · rw [D, signature_mul, Zsig, W0]
  · exact (application_at family m ctx.W ctx.Z W0 Z0).trans Wroot
  · exact application_at family m ctx.W ctx.Z W1 Z1
  · exact (application_at family m ctx.W ctx.Z Wroot Zroot).trans Wupper
  · intro r hr
    exact congruent_trans (congruent_lower (ctx.common r hr)
      (Nat.le_of_lt (Nat.lt_trans gapHi ctx.epsilon_above))) ownerD

#print axioms rebuild

end InsertionInvariant
end LaverLowerBounds.FiniteTable
