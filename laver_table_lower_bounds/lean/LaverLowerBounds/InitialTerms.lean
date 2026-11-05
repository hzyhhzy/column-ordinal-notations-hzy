import LaverLowerBounds.FanSeed

set_option autoImplicit false

namespace LaverLowerBounds.FiniteTable.FanSeed

variable {family : BinaryFamily} {m : Nat}

def a (s : FanSeed family m) := (family m).mul s.K s.K
def b (s : FanSeed family m) := (family m).mul s.K s.j
def c (s : FanSeed family m) := (family m).mul s.a s.b
def d (s : FanSeed family m) := (family m).mul s.c s.K
def e (s : FanSeed family m) := (family m).mul s.d s.j
def f (s : FanSeed family m) := (family m).mul s.e s.K
def g (s : FanSeed family m) := (family m).mul s.f s.K
def r (s : FanSeed family m) := (family m).mul s.g s.f
def p (s : FanSeed family m) := (family m).mul s.f s.b
def q (s : FanSeed family m) := (family m).mul s.r s.d
def J (s : FanSeed family m) := (family m).mul s.p s.f
def L2 (s : FanSeed family m) := (family m).mul s.q s.g
def A (s : FanSeed family m) := (family m).mul s.c s.d
def L3 (s : FanSeed family m) := (family m).mul s.A ((family m).mul s.j s.j)
def alpha (s : FanSeed family m) := act family m s.e (s.points.point 4)
def beta (s : FanSeed family m) := act family m s.f (s.points.point 2)
def zeta (s : FanSeed family m) := act family m s.f (s.points.point 4)
def rho (s : FanSeed family m) := act family m s.r (s.points.point 5)

structure TermData (s : FanSeed family m) : Prop where
  b_signature : signature m s.b = s.points.point 2
  b2 : act family m s.b (s.points.point 2) = s.points.point 3
  b3 : act family m s.b (s.points.point 3) = s.points.point 4
  b4 : act family m s.b (s.points.point 4) = s.points.point 5
  e_signature : signature m s.e = s.points.point 2
  e2 : act family m s.e (s.points.point 2) = s.points.point 3
  e3 : act family m s.e (s.points.point 3) = s.points.point 5
  e5 : act family m s.e (s.points.point 5) = s.points.point 6
  f_signature : signature m s.f = s.points.point 0
  f0 : act family m s.f (s.points.point 0) = s.points.point 3
  f1 : act family m s.f (s.points.point 1) = s.points.point 5
  f3 : act family m s.f (s.points.point 3) = s.alpha
  f5 : act family m s.f (s.points.point 5) = s.points.point 6
  p_signature : signature m s.p = s.beta
  J_signature : signature m s.J = s.points.point 0
  J0 : act family m s.J (s.points.point 0) = s.points.point 3
  J1 : act family m s.J (s.points.point 1) = s.points.point 5
  J2 : act family m s.J (s.points.point 2) = s.alpha
  J3 : act family m s.J (s.points.point 3) = s.zeta
  L2_signature : signature m s.L2 = s.points.point 3
  L2_first : act family m s.L2 (s.points.point 3) = s.zeta
  L2_next : act family m s.L2 s.zeta = s.rho
  five_lt_beta : s.points.point 5 < s.beta
  beta_lt_alpha : s.beta < s.alpha
  alpha_lt_zeta : s.alpha < s.zeta
  zeta_lt_rho : s.zeta < s.rho
  rho_lt_six : s.rho < s.points.point 6
  L3_signature : signature m s.L3 = s.points.point 3
  L3_first : act family m s.L3 (s.points.point 3) = s.points.point 6
  L3_next : act family m s.L3 (s.points.point 6) = s.points.point 7

theorem termData (s : FanSeed family m) : TermData s := by
  let t := s.points.point
  have k0 := s.K_image 0 (by decide)
  have k1 := s.K_image 1 (by decide)
  have k2 := s.K_image 2 (by decide)
  have k3 := s.K_image 3 (by decide)
  have k4 := s.K_image 4 (by decide)
  have k5 := s.K_image 5 (by decide)
  have j0 := s.j_image 0 (by decide)
  have j1 := s.j_image 1 (by decide)
  have j2 := s.j_image 2 (by decide)
  have lt {i j : Nat} (hij : i < j) (hj : j ≤ 8) : t i < t j := s.points.strict hij hj
  have t6cap : t 6 < m := s.points.below (by decide)
  have t7cap : t 7 < m := s.points.below (by decide)
  have a2 : act family m s.a (t 2) = t 4 := (application_at family m s.K s.K k0 k0).trans k2
  have a3 : act family m s.a (t 3) = t 5 := (application_at family m s.K s.K k1 k1).trans k3
  have a4 : act family m s.a (t 4) = t 6 := (application_at family m s.K s.K k2 k2).trans k4
  have a5 : act family m s.a (t 5) = t 7 := (application_at family m s.K s.K k3 k3).trans k5
  have bsig : signature m s.b = t 2 := by change signature m ((family m).mul s.K s.j) = _; rw [signature_mul, s.j_signature]; exact k0
  have b2 : act family m s.b (t 2) = t 3 := (application_at family m s.K s.j k0 j0).trans k1
  have b3 : act family m s.b (t 3) = t 4 := (application_at family m s.K s.j k1 j1).trans k2
  have b4 : act family m s.b (t 4) = t 5 := (application_at family m s.K s.j k2 j2).trans k3
  have csig : signature m s.c = t 4 := by change signature m ((family m).mul s.a s.b) = _; rw [signature_mul, bsig]; exact a2
  have c4 : act family m s.c (t 4) = t 5 := (application_at family m s.a s.b a2 b2).trans a3
  have c5 : act family m s.c (t 5) = t 6 := (application_at family m s.a s.b a3 b3).trans a4
  have c6 : act family m s.c (t 6) = t 7 := (application_at family m s.a s.b a4 b4).trans a5
  have cfix {i : Nat} (hi : i < 4) : act family m s.c (t i) = t i :=
    fixes_below_signature family m s.c (t i) (by rw [csig]; exact lt hi (by decide))
  have dsig : signature m s.d = t 0 := by change signature m ((family m).mul s.c s.K) = _; rw [signature_mul, s.K_signature]; exact cfix (by decide)
  have d0 : act family m s.d (t 0) = t 2 := (application_at family m s.c s.K (cfix (by decide)) k0).trans (cfix (by decide))
  have d1 : act family m s.d (t 1) = t 3 := (application_at family m s.c s.K (cfix (by decide)) k1).trans (cfix (by decide))
  have d2 : act family m s.d (t 2) = t 5 := (application_at family m s.c s.K (cfix (by decide)) k2).trans c4
  have d3 : act family m s.d (t 3) = t 6 := (application_at family m s.c s.K (cfix (by decide)) k3).trans c5
  have esig : signature m s.e = t 2 := by change signature m ((family m).mul s.d s.j) = _; rw [signature_mul, s.j_signature]; exact d0
  have e2 : act family m s.e (t 2) = t 3 := (application_at family m s.d s.j d0 j0).trans d1
  have e3 : act family m s.e (t 3) = t 5 := (application_at family m s.d s.j d1 j1).trans d2
  have e5 : act family m s.e (t 5) = t 6 := (application_at family m s.d s.j d2 j2).trans d3
  have efix {i : Nat} (hi : i < 2) : act family m s.e (t i) = t i :=
    fixes_below_signature family m s.e (t i) (by rw [esig]; exact lt hi (by decide))
  have fsig : signature m s.f = t 0 := by change signature m ((family m).mul s.e s.K) = _; rw [signature_mul, s.K_signature]; exact efix (by decide)
  have f0 : act family m s.f (t 0) = t 3 := (application_at family m s.e s.K (efix (by decide)) k0).trans e2
  have f1 : act family m s.f (t 1) = t 5 := (application_at family m s.e s.K (efix (by decide)) k1).trans e3
  have f3 : act family m s.f (t 3) = s.alpha := application_at family m s.e s.K e2 k2
  have f5 : act family m s.f (t 5) = t 6 := (application_at family m s.e s.K e3 k3).trans e5
  have alpha6 : s.alpha < t 6 := by
    have he := act_strict_below_cap family m s.e (t 4) (t 5) (lt (by decide) (by decide)) (by omega)
    exact e5 ▸ he
  have betaAlpha : s.beta < s.alpha := by
    have he := act_strict_below_cap family m s.f (t 2) (t 3) (lt (by decide) (by decide)) (by omega)
    exact f3 ▸ he
  have fiveBeta : t 5 < s.beta := by
    have he := act_strict_below_cap family m s.f (t 1) (t 2) (lt (by decide) (by decide)) (by change s.beta < m; omega)
    exact f1 ▸ he
  have zeta6 : s.zeta < t 6 := by
    have he := act_strict_below_cap family m s.f (t 4) (t 5) (lt (by decide) (by decide)) (by omega)
    exact f5 ▸ he
  have alphaZeta : s.alpha < s.zeta := by
    have he := act_strict_below_cap family m s.f (t 3) (t 4) (lt (by decide) (by decide)) (by change s.zeta < m; omega)
    exact f3 ▸ he
  have gsig : signature m s.g = t 3 := by change signature m ((family m).mul s.f s.K) = _; rw [signature_mul, s.K_signature]; exact f0
  have g3 : act family m s.g (t 3) = s.beta := application_at family m s.f s.K f0 k0
  have g5 : act family m s.g (t 5) = s.alpha := (application_at family m s.f s.K f1 k1).trans f3
  have gBeta : act family m s.g s.beta = s.zeta := application_at family m s.f s.K (rfl : act family m s.f (t 2) = s.beta) k2
  have gAlpha : act family m s.g s.alpha = t 6 := (application_at family m s.f s.K f3 k3).trans f5
  have gfix {i : Nat} (hi : i < 3) : act family m s.g (t i) = t i :=
    fixes_below_signature family m s.g (t i) (by rw [gsig]; exact lt hi (by decide))
  have r0 : act family m s.r (t 0) = s.beta := (application_at family m s.g s.f (gfix (by decide)) f0).trans g3
  have r1 : act family m s.r (t 1) = s.alpha := (application_at family m s.g s.f (gfix (by decide)) f1).trans g5
  have r2 : act family m s.r (t 2) = s.zeta := (application_at family m s.g s.f (gfix (by decide)) (rfl : act family m s.f (t 2) = s.beta)).trans gBeta
  have rBeta : act family m s.r s.beta = t 6 := (application_at family m s.g s.f g3 f3).trans gAlpha
  have rho6 : s.rho < t 6 := by
    have he := act_strict_below_cap family m s.r (t 5) s.beta fiveBeta (by omega)
    exact rBeta ▸ he
  have zetaRho : s.zeta < s.rho := by
    have he := act_strict_below_cap family m s.r (t 2) (t 5) (lt (by decide) (by decide)) (by change s.rho < m; omega)
    exact r2 ▸ he
  have psig : signature m s.p = s.beta := by change signature m ((family m).mul s.f s.b) = _; rw [signature_mul, bsig]; rfl
  have pBeta : act family m s.p s.beta = s.alpha := (application_at family m s.f s.b (rfl : act family m s.f (t 2) = s.beta) b2).trans f3
  have pAlpha : act family m s.p s.alpha = s.zeta := application_at family m s.f s.b f3 b3
  have pfix {i : Nat} (hi : i ≤ 5) : act family m s.p (t i) = t i :=
    fixes_below_signature family m s.p (t i) (by rw [psig]; exact Nat.lt_of_le_of_lt (s.points.mono hi (by decide)) fiveBeta)
  have qsig : signature m s.q = s.beta := by change signature m ((family m).mul s.r s.d) = _; rw [signature_mul, dsig]; exact r0
  have qBeta : act family m s.q s.beta = s.zeta := (application_at family m s.r s.d r0 d0).trans r2
  have qZeta : act family m s.q s.zeta = s.rho := application_at family m s.r s.d r2 d2
  have q3fix : act family m s.q (t 3) = t 3 :=
    fixes_below_signature family m s.q (t 3) (by rw [qsig]; exact Nat.lt_trans (lt (by decide) (by decide)) fiveBeta)
  have jsig : signature m s.J = t 0 := by change signature m ((family m).mul s.p s.f) = _; rw [signature_mul, fsig]; exact pfix (by decide)
  have J0 : act family m s.J (t 0) = t 3 := (application_at family m s.p s.f (pfix (by decide)) f0).trans (pfix (by decide))
  have J1 : act family m s.J (t 1) = t 5 := (application_at family m s.p s.f (pfix (by decide)) f1).trans (pfix (by decide))
  have J2 : act family m s.J (t 2) = s.alpha := (application_at family m s.p s.f (pfix (by decide)) (rfl : act family m s.f (t 2) = s.beta)).trans pBeta
  have J3 : act family m s.J (t 3) = s.zeta := (application_at family m s.p s.f (pfix (by decide)) f3).trans pAlpha
  have l2sig : signature m s.L2 = t 3 := by change signature m ((family m).mul s.q s.g) = _; rw [signature_mul, gsig]; exact q3fix
  have l2first : act family m s.L2 (t 3) = s.zeta := (application_at family m s.q s.g q3fix g3).trans qBeta
  have l2next : act family m s.L2 s.zeta = s.rho := (application_at family m s.q s.g qBeta gBeta).trans qZeta
  have a1 : act family m s.A (t 1) = t 3 := (application_at family m s.c s.d (cfix (by decide)) d1).trans (cfix (by decide))
  have a2' : act family m s.A (t 2) = t 6 := (application_at family m s.c s.d (cfix (by decide)) d2).trans c5
  have a3' : act family m s.A (t 3) = t 7 := (application_at family m s.c s.d (cfix (by decide)) d3).trans c6
  have jjsig : signature m ((family m).mul s.j s.j) = t 1 := by rw [signature_mul, s.j_signature]; exact j0
  have jj1 : act family m ((family m).mul s.j s.j) (t 1) = t 2 := (application_at family m s.j s.j j0 j0).trans j1
  have jj2 : act family m ((family m).mul s.j s.j) (t 2) = t 3 := (application_at family m s.j s.j j1 j1).trans j2
  have l3sig : signature m s.L3 = t 3 := by change signature m ((family m).mul s.A _) = _; rw [signature_mul, jjsig]; exact a1
  have l3first : act family m s.L3 (t 3) = t 6 := (application_at family m s.A _ a1 jj1).trans a2'
  have l3next : act family m s.L3 (t 6) = t 7 := (application_at family m s.A _ a2' jj2).trans a3'
  exact ⟨bsig, b2, b3, b4, esig, e2, e3, e5, fsig, f0, f1, f3, f5, psig,
    jsig, J0, J1, J2, J3, l2sig, l2first, l2next, fiveBeta, betaAlpha, alphaZeta,
    zetaRho, rho6, l3sig, l3first, l3next⟩

#print axioms termData

end LaverLowerBounds.FiniteTable.FanSeed
