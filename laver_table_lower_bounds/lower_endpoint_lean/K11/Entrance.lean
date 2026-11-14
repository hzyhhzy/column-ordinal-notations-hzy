import K11.Lines
import K11.LocalData

set_option autoImplicit false
namespace LaverLowerBounds.FiniteTable.K11

structure Entrance (family : BinaryFamily) (m : Nat) where
  bg : Core family m
  eta : Nat
  zeta : Nat
  endpoint : Nat
  f : Nat
  xi_eta : bg.mu < eta
  eta_zeta : eta < zeta
  f0 : act family m f 0 = bg.k
  f1 : act family m f 1 = eta
  fk : act family m f bg.k = zeta
  line : Lined family m bg.k 252 zeta endpoint
  target : endpoint = act family m 11 4

theorem source_tail_of_unsaturated (family : BinaryFamily) (m : Nat) (h9 : 9 ≤ m)
    (ht : act family m 11 4 < m) :
    Lined family m 0 6 4 (act family m 7 2) := by
  have hd := localData family m h9 ht
  have s1 := signature_from_nine m 1 0 h9 (by decide) (by decide)
  have s3 := signature_from_nine m 3 0 h9 (by decide) (by decide)
  have j0 := act_from_low family m 1 0 2 1 h9 (LowProducts.v1_1 (family 9)) (by decide) (by decide)
  have j1 := act_from_low family m 1 1 12 2 h9 (LowProducts.v1_2 (family 9)) (by decide) (by decide)
  have j2 := act_from_low family m 1 2 240 4 h9 (LowProducts.v1_4 (family 9)) (by decide) (by decide)
  have t0 := act_from_low family m 3 0 4 2 h9 (LowProducts.v3_1 (family 9)) (by decide) (by decide)
  have t2 := act_from_low family m 3 2 464 4 h9 (LowProducts.v3_4 (family 9)) (by decide) (by decide)
  let J12 := (family m).mul 11 1
  let J13 := (family m).mul J12 1
  have sig12 : signature m J12 = 2 := by dsimp [J12]; rw [signature_mul, s1, hd.k0]
  have u0 : act family m J12 0 = 0 := fixes_below_signature family m J12 0 (by omega)
  have u1 : act family m J12 1 = 1 := fixes_below_signature family m J12 1 (by omega)
  have u2 : act family m J12 2 = 4 := (application_at family m 11 1 hd.k0 j0).trans hd.k1
  have u4 : act family m J12 4 = act family m 7 2 := (application_at family m 11 1 hd.k1 j1).trans hd.k2
  have v0 : act family m J13 0 = 1 := (application_at family m J12 1 u0 j0).trans u1
  have v1 : act family m J13 1 = 4 := (application_at family m J12 1 u1 j1).trans u2
  have v4 : act family m J13 4 = act family m 7 2 := (application_at family m J12 1 u2 j2).trans u4
  have two : Lined family m 0 2 1 4 := .cons 1 s1 j0 j1 (by decide)
    (.cons 3 s3 t0 t2 (by decide) (.nil (by omega)))
  have mucap : act family m 7 2 < m := Nat.lt_trans hd.mu_lt_five ht
  have high := two.map J13 (by rw [v4]; exact mucap)
  rw [v0, v1, v4] at high
  exact two.multiply_tail high (by decide)

/-- All the new low-point geometry is derived from ordinary finite-table
equations. No embedding, count, long-line, or fan hypothesis is supplied. -/
def entrance_of_unsaturated (family : BinaryFamily) (m : Nat) (h9 : 9 ≤ m)
    (ht : act family m 11 4 < m) : Entrance family m := by
  have hd := localData family m h9 ht
  let mu := act family m 7 2
  let theta := act family m 11 4
  have thetaCap : theta < m := ht
  have muCap : mu < m := Nat.lt_trans hd.mu_lt_five thetaCap
  have muLow : 9 ≤ mu := hd.mu_lower
  have sig1 := signature_from_nine m 1 0 h9 (by decide) (by decide)
  have sig2 := signature_from_nine m 2 1 h9 (by decide) (by decide)
  have sig3 := signature_from_nine m 3 0 h9 (by decide) (by decide)
  have sig4 := signature_from_nine m 4 2 h9 (by decide) (by decide)
  have p10 := act_from_low family m 1 0 2 1 h9 (LowProducts.v1_1 (family 9)) (by decide) (by decide)
  have p11 := act_from_low family m 1 1 12 2 h9 (LowProducts.v1_2 (family 9)) (by decide) (by decide)
  have p12 := act_from_low family m 1 2 240 4 h9 (LowProducts.v1_4 (family 9)) (by decide) (by decide)
  have p21 := act_from_low family m 2 1 12 2 h9 (LowProducts.v2_2 (family 9)) (by decide) (by decide)
  have p22 := act_from_low family m 2 2 304 4 h9 (LowProducts.v2_4 (family 9)) (by decide) (by decide)
  have p30 := act_from_low family m 3 0 4 2 h9 (LowProducts.v3_1 (family 9)) (by decide) (by decide)
  have p31 := act_from_low family m 3 1 8 3 h9 (LowProducts.v3_2 (family 9)) (by decide) (by decide)
  have p32 := act_from_low family m 3 2 464 4 h9 (LowProducts.v3_4 (family 9)) (by decide) (by decide)
  have p42 := act_from_low family m 4 2 8 3 h9 (LowProducts.v4_4 (family 9)) (by decide) (by decide)
  have p43 : act family m 4 3 = 4 := by
    have he := next_small family m 3 1 h9 (by decide)
    rwa [p31, p11, p32] at he
  have p70 := act_from_low family m 7 0 8 3 h9 (LowProducts.v7_1 (family 9)) (by decide) (by decide)
  have p71 := act_from_low family m 7 1 496 4 h9 (LowProducts.v7_2 (family 9)) (by decide) (by decide)
  have n1 := mul_next_small family m 1 h9 (by decide)
  have n2 := mul_next_small family m 2 h9 (by decide)
  let Q := (family m).mul 11 3
  have qs : signature m Q = 2 := by dsimp [Q]; rw [signature_mul, sig3, hd.k0]
  have q0 : act family m Q 0 = 0 := fixes_below_signature family m Q 0 (by omega)
  have q1 : act family m Q 1 = 1 := fixes_below_signature family m Q 1 (by omega)
  have q2 : act family m Q 2 = mu := (application_at family m 11 3 hd.k0 p30).trans hd.k2
  have qm : act family m Q mu = theta := application_at family m 11 3 hd.k2 p32
  let delta := act family m Q 3
  let chi := act family m Q 4
  have chiTheta : chi < theta := by
    have he := act_strict_below_cap family m Q 4 mu (by omega) (by rw [qm]; exact thetaCap)
    rwa [qm] at he
  have chiCap : chi < m := Nat.lt_trans chiTheta thetaCap
  have deltaChi : delta < chi := act_strict_below_cap family m Q 3 4 (by decide) chiCap
  have muDelta : mu < delta := by
    have he := act_strict_below_cap family m Q 2 3 (by decide) (Nat.lt_trans deltaChi chiCap)
    rwa [q2] at he
  let G := (family m).mul Q 1
  let G2 := (family m).mul Q 2
  let G3 := (family m).mul Q 3
  let G4 := (family m).mul Q 4
  let B := (family m).mul Q 7
  have gs : signature m G = 0 := by dsimp [G]; rw [signature_mul, sig1, q0]
  have g2s : signature m G2 = 1 := by dsimp [G2]; rw [signature_mul, sig2, q1]
  have g3s : signature m G3 = 0 := by dsimp [G3]; rw [signature_mul, sig3, q0]
  have g4s : signature m G4 = mu := by dsimp [G4]; rw [signature_mul, sig4, q2]
  have g0 : act family m G 0 = 1 := (application_at family m Q 1 q0 p10).trans q1
  have g1 : act family m G 1 = mu := (application_at family m Q 1 q1 p11).trans q2
  have gm : act family m G mu = chi := application_at family m Q 1 q2 p12
  have g21 : act family m G2 1 = mu := (application_at family m Q 2 q1 p21).trans q2
  have g2m : act family m G2 mu = chi := application_at family m Q 2 q2 p22
  have g30 : act family m G3 0 = mu := (application_at family m Q 3 q0 p30).trans q2
  have g31 : act family m G3 1 = delta := application_at family m Q 3 q1 p31
  have g3m : act family m G3 mu = chi := application_at family m Q 3 q2 p32
  have g4m : act family m G4 mu = delta := application_at family m Q 4 q2 p42
  have g4d : act family m G4 delta = chi := application_at family m Q 4 rfl p43
  have b0 : act family m B 0 = delta := application_at family m Q 7 q0 p70
  have b1 : act family m B 1 = chi := application_at family m Q 7 q1 p71
  have bm : act family m B mu = theta := (application_at family m Q 7 q2 rfl).trans qm
  have gg : (family m).mul G G = G2 := by dsimp [G, G2]; rw [← (family m).mul_distrib, n1]
  have g2g : (family m).mul G2 G = G3 := by dsimp [G2, G3, G]; rw [← (family m).mul_distrib, n2]
  let xi := act family m B 2
  have xiTheta : xi < theta := by
    have he := act_strict_below_cap family m B 2 mu (by omega) (by rw [bm]; exact thetaCap)
    rwa [bm] at he
  have xiCap : xi < m := Nat.lt_trans xiTheta thetaCap
  have chiXi : chi < xi := by
    have he := act_strict_below_cap family m B 1 2 (by decide) xiCap
    rwa [b1] at he
  let E := (family m).mul B 1
  have es : signature m E = delta := by dsimp [E]; rw [signature_mul, sig1, b0]
  have e0 : act family m E 0 = 0 := fixes_below_signature family m E 0 (by omega)
  have e1 : act family m E 1 = 1 := fixes_below_signature family m E 1 (by omega)
  have em : act family m E mu = mu := fixes_below_signature family m E mu (by omega)
  have ed : act family m E delta = chi := (application_at family m B 1 b0 p10).trans b1
  have ec : act family m E chi = xi := application_at family m B 1 b1 p11
  let J := (family m).mul E G2
  let K := (family m).mul J G
  have js : signature m J = 1 := by dsimp [J]; rw [signature_mul, g2s, e1]
  have j0 : act family m J 0 = 0 := fixes_below_signature family m J 0 (by omega)
  have j1 : act family m J 1 = mu := (application_at family m E G2 e1 g21).trans em
  have jm : act family m J mu = xi := (application_at family m E G2 em g2m).trans ec
  have k0 : act family m K 0 = mu := (application_at family m J G j0 g0).trans j1
  have km : act family m K mu = xi := (application_at family m J G j1 g1).trans jm
  have eg3one : act family m ((family m).mul E G3) 1 = chi := (application_at family m E G3 e1 g31).trans ed
  have congr : congruent m (act family m J delta) ((family m).mul E G3) K := by
    have he := congruent_transport family m (app_critical family m E G) J
    rw [es] at he
    have eq : (family m).mul J ((family m).mul E G) = (family m).mul E G3 := by
      dsimp [J]
      rw [← (family m).mul_distrib]
      change (family m).mul E ((family m).mul G2 G) = (family m).mul E G3
      rw [g2g]
    rwa [eq] at he
  have cut : chi < act family m J delta := by
    have he := act_mono family m J (Nat.le_of_lt muDelta)
    rw [jm] at he
    omega
  have k1 : act family m K 1 = chi := by
    have he := congruent_read family m congr (by rw [eg3one]; exact cut)
    exact he.symm.trans eg3one
  have kc : congruent m delta K G3 := by
    have deltaCap : delta ≤ m := by omega
    have lower := congruent_lower congr (le_act family m J delta deltaCap)
    have old := app_critical family m E G3
    rw [es] at old
    exact congruent_trans (congruent_symm lower) old
  let bg : Core family m := {
    k := mu, sigma := delta, r := chi, mu := xi
    k_lower := by omega, k_sigma := muDelta, sigma_r := deltaChi, r_mu := chiXi, mu_cap := xiCap
    j := G, j2 := G2, j3 := G3, j10 := J, K := K
    j_signature := gs, j2_signature := g2s, j3_signature := g3s, j10_signature := js
    j_zero := g0, j_one := g1, j_next := gm, j_j := gg, j2_one := g21
    j3_zero := g30, j3_one := g31, j3_next := g3m
    j10_one := j1, j10_next := jm, K_one := k1, j2_j := g2g, j10_j := rfl, K_j3 := kc }
  let S := (family m).mul B 3
  let eta := act family m S chi
  let zeta := act family m B 4
  have ss : signature m S = delta := by dsimp [S]; rw [signature_mul, sig3, b0]
  have sm : act family m S mu = mu := fixes_below_signature family m S mu (by omega)
  have s0 : act family m S 0 = 0 := fixes_below_signature family m S 0 (by omega)
  have s1 : act family m S 1 = 1 := fixes_below_signature family m S 1 (by omega)
  have sd : act family m S delta = xi := application_at family m B 3 b0 p30
  have sx : act family m S xi = zeta := application_at family m B 3 rfl p32
  have zTheta : zeta < theta := by
    have he := act_strict_below_cap family m B 4 mu (by omega) (by rw [bm]; exact thetaCap)
    rwa [bm] at he
  have zCap : zeta < m := Nat.lt_trans zTheta thetaCap
  have etaZ : eta < zeta := by
    have he := act_strict_below_cap family m S chi xi chiXi (by rw [sx]; exact zCap)
    rwa [sx] at he
  have xiEta : xi < eta := by
    have he := act_strict_below_cap family m S delta chi deltaChi (Nat.lt_trans etaZ zCap)
    rwa [sd] at he
  let f := (family m).mul S K
  have f0 : act family m f 0 = mu := (application_at family m S K s0 k0).trans sm
  have f1 : act family m f 1 = eta := application_at family m S K s1 k1
  have fm : act family m f mu = zeta := (application_at family m S K sm km).trans sx
  have one : Lined family m mu 1 delta chi :=
    .cons G4 g4s g4m g4d deltaChi (.nil chiCap)
  have two := one.double muDelta es ed ec xiCap
  have four := two.double muDelta ss sd sx zCap
  have high := (source_tail_of_unsaturated family m h9 ht).map B (by rw [bm]; exact thetaCap)
  rw [b0, bm] at high
  have tail := four.multiply_tail high muDelta
  exact { bg := bg, eta := eta, zeta := zeta, endpoint := theta, f := f
          xi_eta := xiEta, eta_zeta := etaZ, f0 := f0, f1 := f1, fk := fm
          line := tail, target := rfl }

theorem source_tail (family : BinaryFamily) (m : Nat) (hm : PeriodAtLeast32 (family m)) :
    Lined family m 0 6 4 (act family m 7 2) :=
  source_tail_of_unsaturated family m (Nat.le_of_lt (threshold_gt_nine family m hm))
    (k_four_unsaturated family m hm)

def entrance (family : BinaryFamily) (m : Nat) (hm : PeriodAtLeast32 (family m)) : Entrance family m :=
  entrance_of_unsaturated family m (Nat.le_of_lt (threshold_gt_nine family m hm))
    (k_four_unsaturated family m hm)

#print axioms source_tail_of_unsaturated
#print axioms entrance_of_unsaturated
#print axioms entrance
end LaverLowerBounds.FiniteTable.K11
