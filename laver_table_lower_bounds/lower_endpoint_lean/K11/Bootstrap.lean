import K11.Iteration

set_option autoImplicit false

namespace LaverLowerBounds.FiniteTable.K11.Core
variable {family : BinaryFamily} {m : Nat}

def firstPoint (bg : Core family m) (T : Nat) : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => act family m T 1
  | 3 => act family m ((family m).mul T bg.j) 1
  | 4 => act family m T bg.k
  | _ => act family m T bg.r

structure First (bg : Core family m) (Q : Nat) where
  fan : OwnedFan family m 1
  endpoint : fan.fan.endpoint = act family m ((family m).mul Q bg.j10) bg.r
  Dsig : signature m ((family m).mul Q bg.j3) = 0
  Dzero : act family m ((family m).mul Q bg.j3) 0 = fan.fan.chain.point 2
  Done : act family m ((family m).mul Q bg.j3) 1 = act family m Q bg.sigma
  Dnext : act family m ((family m).mul Q bg.j3) (fan.fan.chain.point 2) = fan.fan.chain.point 3
  gap : fan.fan.chain.point 2 < act family m Q bg.sigma ∧
    act family m Q bg.sigma < fan.fan.chain.point 3
  common : ∀ i, i < 1 → congruent m (act family m Q bg.sigma)
    (fan.owner i) ((family m).mul Q bg.j3)

def first (bg : Core family m) (Q : Nat) (hQ : signature m Q = bg.k)
    (hcap : act family m ((family m).mul Q bg.j10) bg.r < m) : First bg Q := by
  let T := (family m).mul Q bg.j10
  let A := (family m).mul T bg.j
  let L := (family m).mul T bg.j2
  have hk := bg.k_lower
  have q0 : act family m Q 0 = 0 := fixes_below_signature family m Q 0 (by omega)
  have q1 : act family m Q 1 = 1 := fixes_below_signature family m Q 1 (by omega)
  have tsig : signature m T = 1 := by dsimp [T]; rw [signature_mul, bg.j10_signature, q1]
  have t0 : act family m T 0 = 0 := fixes_below_signature family m T 0 (by omega)
  have t1 : 1 < act family m T 1 := by
    have he := signature_lt_act family m T (by have := bg.k_cap; omega)
    rwa [tsig] at he
  have tkcap : act family m T bg.k < m := Nat.lt_of_le_of_lt
    (act_mono family m T (Nat.le_of_lt (Nat.lt_trans bg.k_sigma bg.sigma_r))) hcap
  have qr : act family m Q bg.r < m := by
    have ka : act family m ((family m).mul T bg.j) (act family m T 1) = act family m T bg.k :=
      application_at family m T bg.j rfl bg.j_one
    have cj := congruent_transport family m (app_critical family m Q bg.j) T
    have ld : (family m).mul T ((family m).mul Q bg.j) = (family m).mul Q bg.K := by
      dsimp [T]; rw [← (family m).mul_distrib, bg.j10_j]
    rw [hQ, ld] at cj
    have alow := act_strict_below_cap family m ((family m).mul T bg.j) 1
      (act family m T 1) t1 (by rw [ka]; exact tkcap)
    rw [ka] at alow
    have read := congruent_read family m (congruent_symm cj) alow
    have image := application_at family m Q bg.K q1 bg.K_one
    rw [image] at read
    omega
  have low := bg.lowData Q 0 hQ (by rw [signature_zero]; exact Nat.le_of_lt bg.k_cap) qr
  have xeq : (family m).mul T ((family m).mul 0 bg.j) = A := by
    rw [(family m).zero_mul, (family m).mul_mod_right]
  have a0 : act family m A 0 = act family m T 1 := application_at family m T bg.j t0 bg.j_zero
  have a1 : act family m A 1 = act family m Q bg.r := by
    have he := low.X_one
    change act family m ((family m).mul T ((family m).mul 0 bg.j)) 1 = _ at he
    rwa [xeq] at he
  have ak : act family m A (act family m T 1) = act family m T bg.k :=
    application_at family m T bg.j rfl bg.j_one
  have a1tk : act family m A 1 < act family m T bg.k := by
    have he := act_strict_below_cap family m A 1 (act family m T 1) t1 (by rw [ak]; exact tkcap)
    rwa [ak] at he
  have ta1 : act family m T 1 < act family m A 1 := by rw [low.T_one, a1]; exact Nat.lt_trans low.gap.1 low.gap.2
  have tkr : act family m T bg.k < act family m T bg.r :=
    act_strict_below_cap family m T _ _ (Nat.lt_trans bg.k_sigma bg.sigma_r) hcap
  have j2k : act family m bg.j2 bg.k = bg.r := by
    have he := act_application family m bg.j bg.j 1
    rwa [bg.j_j, bg.j_one, bg.j_next] at he
  let point := firstPoint bg T
  have adjacent : ∀ i, i < 5 → point i < point (i + 1) := by
    intro i hi
    match i with
    | 0 => exact Nat.zero_lt_one
    | 1 => exact t1
    | 2 => exact ta1
    | 3 => exact a1tk
    | 4 => exact tkr
    | n + 5 => omega
  have port : BandPort family m point 0 2 1 A := by
    refine ⟨?_, ?_, ak⟩
    · change signature m A = 0
      dsimp [A]; rw [signature_mul, bg.j_signature, t0]
    · intro t ht
      match t with
      | 0 => exact a0
      | 1 => rfl
      | n + 2 => omega
  let fan : ClosedFan family m 1 := {
    chain := PointChain.ofAdjacent point adjacent hcap
    ports := by
      intro i hi
      have hi0 : i = 0 := by omega
      subst i
      exact ⟨A, port⟩
    closer := L
    closer_signature := by dsimp [L]; rw [signature_mul, bg.j2_signature]; rfl
    closer_first := application_at family m T bg.j2 rfl bg.j2_one
    closer_next := application_at family m T bg.j2 rfl j2k }
  let owned : OwnedFan family m 1 := {
    fan := fan, owner := fun _ => A
    port := by
      intro i hi
      have hi0 : i = 0 := by omega
      subst i
      exact port
    zero := rfl, one := rfl }
  refine ⟨owned, rfl, low.Z_signature, ?_, low.Z_one, ?_, ?_, ?_⟩
  · change act family m ((family m).mul Q bg.j3) 0 = act family m T 1
    rw [low.Z_zero, low.T_one]
  · change act family m ((family m).mul Q bg.j3) (act family m T 1) = act family m A 1
    rw [low.T_one, low.Z_next, a1]
  · change act family m T 1 < act family m Q bg.sigma ∧ act family m Q bg.sigma < act family m A 1
    rw [low.T_one, a1]; exact low.gap
  · intro i hi
    change congruent m (act family m Q bg.sigma) A ((family m).mul Q bg.j3)
    have he := low.common
    change congruent m _ ((family m).mul T ((family m).mul 0 bg.j)) _ at he
    rwa [xeq] at he

def secondContext (bg : Core family m) (Q R : Nat)
    (hQ : signature m Q = bg.k) (hR : signature m R = bg.k)
    (hc : act family m ((family m).mul Q bg.j10) bg.r < m)
    (hRc : act family m R bg.r < m)
    (ins : OwnedFan.Insertion (bg.first Q hQ hc).fan ((family m).mul R bg.j10)
      ((family m).mul Q bg.j3) (act family m Q bg.sigma)) : Context bg ins.next := by
  refine {
    P := [], Q := R, U := Q, Q_signature := hR, U_signature := by omega
    Q_four_below := hRc, high_factors := by simp [WordAboveOne]
    epsilon := act family m ((family m).mul R bg.j10) (act family m Q bg.sigma)
    epsilon_above := ins.gap, common := ?_, first := ?_ }
  · intro i hi
    rw [ins.owners 0]
    exact ins.common i hi
  · rw [ins.owners 0]
    rfl

theorem line_to_fan (bg : Core family m) {n a b : Nat}
    (line : Lined family m bg.k n a b) (hn : 2 ≤ n) (ha : bg.mu ≤ a) :
    ∃ fan : OwnedFan family m n, fan.fan.endpoint < b := by
  cases line with
  | nil _ => omega
  | @cons n a b c Q hQ hQa hQb hab tail =>
    have bcap := Nat.lt_of_le_of_lt tail.endpoints.1 tail.endpoints.2
    have start : bg.r < a := Nat.lt_of_lt_of_le bg.r_mu ha
    obtain ⟨_, hfirst⟩ := bg.segment_actor hQ hQa hQb ha start bcap
    let first := bg.first Q hQ (Nat.lt_trans hfirst bcap)
    have firstCap : first.fan.fan.endpoint < b := by rw [first.endpoint]; exact hfirst
    cases tail with
    | nil _ => omega
    | @cons n b d c R hR hRb hRd hbd rest =>
      have dcap := Nat.lt_of_le_of_lt rest.endpoints.1 rest.endpoints.2
      have muB : bg.mu ≤ b := Nat.le_trans ha (Nat.le_of_lt hab)
      have rB : bg.r < b := Nat.lt_of_lt_of_le bg.r_mu muB
      have rcap : act family m R bg.r < m := by
        have he := act_strict_below_cap family m R bg.r b rB (by rw [hRd]; exact dcap)
        rw [hRd] at he; omega
      obtain ⟨hT, hbound⟩ := bg.segment_actor hR hRb hRd muB firstCap dcap
      let ins := first.fan.insert ((family m).mul R bg.j10) ((family m).mul Q bg.j3)
        (act family m Q bg.sigma) (by decide) hT first.Dsig first.Dzero first.Done
        first.Dnext first.gap first.common (Nat.lt_trans hbound dcap)
      let ctx := bg.secondContext Q R hQ hR (Nat.lt_trans hfirst bcap) rcap ins
      have nextCap : ins.next.fan.endpoint < d := by rw [ins.endpoint_image]; exact hbound
      have result := bg.grow_fan_along_line rest ins.next ctx (by decide)
        (Nat.le_trans muB (Nat.le_of_lt hbd)) nextCap
      have height : n + 1 + 1 = 2 + n := by omega
      rw [height]
      exact result

#print axioms first
#print axioms line_to_fan
end LaverLowerBounds.FiniteTable.K11.Core
