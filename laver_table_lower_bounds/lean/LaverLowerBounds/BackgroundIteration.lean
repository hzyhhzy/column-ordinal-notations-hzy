import LaverLowerBounds.BackgroundInvariant

set_option autoImplicit false

namespace LaverLowerBounds.FiniteTable.InsertionBackground

variable {family : BinaryFamily} {m : Nat} {bg : InsertionBackground family m}

namespace Context

variable {h : Nat} {old : OwnedFan family m h}

def advance (ctx : Context bg old) (hh : 1 ≤ h)
    (Q : Nat) (hQ : signature m Q = bg.k) (hcap : act family m Q bg.r < m)
    (ins : OwnedFan.Insertion old ((family m).mul Q bg.j10) ctx.D ctx.delta) : Context bg ins.next := by
  let T := (family m).mul Q bg.j10
  let Pnew := (family m).mul T ctx.W :: pushWord family m T ctx.P
  have rebuilt := ctx.rebuild hh
  refine {
    P := Pnew
    Q := Q
    U := ctx.Q
    Q_signature := hQ
    U_signature := by rw [ctx.Q_signature]; exact Nat.le_refl _
    Q_four_below := hcap
    high_factors := ?_
    epsilon := act family m T ctx.delta
    epsilon_above := ins.gap
    common := ?_
    first := ?_ }
  · intro e he
    rcases List.mem_cons.mp he with he | he
    · subst e
      rw [signature_mul]
      exact Nat.lt_of_lt_of_le rebuilt.W_signature_above (le_act family m T _ (signature_le _ _))
    · exact pushWord_above family m T ctx.high_factors e he
  · intro r hr
    have he := ins.common r hr
    have hzero := ins.owners 0
    change ins.next.owner 0 = (family m).mul T ctx.D at hzero
    rw [hzero]
    exact he
  · rw [ins.owners 0]
    change (family m).mul T ((family m).mul ctx.W ctx.Z) =
      wordTerm family m (Pnew ++ [T, ctx.Q]) bg.j3
    rw [List.cons_append]
    change (family m).mul T ((family m).mul ctx.W ctx.Z) =
      (family m).mul ((family m).mul T ctx.W)
        (wordTerm family m (pushWord family m T ctx.P ++ [T, ctx.Q]) bg.j3)
    rw [wordTerm_append]
    change (family m).mul T ((family m).mul ctx.W ctx.Z) =
      (family m).mul ((family m).mul T ctx.W)
        (wordTerm family m (pushWord family m T ctx.P) ((family m).mul T ((family m).mul ctx.Q bg.j3)))
    rw [pushWord_term]
    exact (family m).mul_distrib T ctx.W ctx.Z

end Context

def firstContext (bg : InsertionBackground family m)
    (Q : Nat) (hQ : signature m Q = bg.k) (hcap : act family m Q bg.r < m)
    (ins : OwnedFan.Insertion bg.initial ((family m).mul Q bg.j10)
      ((family m).mul bg.e bg.j3) bg.delta) : Context bg ins.next := by
  let T := (family m).mul Q bg.j10
  have hk := bg.k_lower
  have hkm : bg.k ≤ m := by rw [← bg.e_signature]; exact signature_le _ _
  have zero3 : (family m).mul 0 bg.j3 = bg.j3 := by
    rw [(family m).zero_mul, Nat.mod_eq_of_lt bg.j3_bound]
  refine {
    P := [(family m).mul T bg.e]
    Q := Q
    U := 0
    Q_signature := hQ
    U_signature := by rw [signature_zero]; exact hkm
    Q_four_below := hcap
    high_factors := ?_
    epsilon := act family m T bg.delta
    epsilon_above := ins.gap
    common := ?_
    first := ?_ }
  · intro e he
    have he' : e = (family m).mul T bg.e := by simpa using he
    subst e
    rw [signature_mul, bg.e_signature]
    exact Nat.lt_of_lt_of_le (by omega : 1 < bg.k) (le_act family m T bg.k hkm)
  · intro r hr
    have he := ins.common r hr
    have hzero := ins.owners 0
    change ins.next.owner 0 = (family m).mul T ((family m).mul bg.e bg.j3) at hzero
    rw [hzero]
    exact he
  · rw [ins.owners 0]
    change (family m).mul T ((family m).mul bg.e bg.j3) =
      wordTerm family m ([(family m).mul T bg.e] ++ [T, 0]) bg.j3
    simp only [List.singleton_append, wordTerm, zero3]
    exact (family m).mul_distrib T bg.e bg.j3

theorem grow_fan_along_line (bg : InsertionBackground family m)
    {n a b : Nat} (line : Lined family m bg.k n a b) :
    ∀ {h : Nat} (old : OwnedFan family m h) (_ctx : Context bg old),
      1 ≤ h → bg.a ≤ a → old.fan.endpoint < a →
      ∃ next : OwnedFan family m (h + n), next.fan.endpoint < b := by
  induction line with
  | nil _ =>
      intro h old _ _ _ hc
      exact ⟨old, hc⟩
  | @cons n a b c Q hsig hroot hnext hab tail ih =>
      intro h old ctx hh ha hc
      have hr : bg.r < a := Nat.lt_of_lt_of_le (Nat.lt_trans bg.r_mu bg.mu_a) ha
      have hbcap : b < m := Nat.lt_of_le_of_lt tail.endpoints.1 tail.endpoints.2
      have hQcap : act family m Q bg.r < m := by
        have he := act_strict_below_cap family m Q bg.r a hr (by rw [hnext]; exact hbcap)
        rw [hnext] at he
        omega
      have split := ctx.rebuild hh
      obtain ⟨hT, hbound⟩ := bg.segment_actor hsig hroot hnext ha hc hbcap
      let ins := old.insert ((family m).mul Q bg.j10) ctx.D ctx.delta hh hT
        split.signature_eq split.zero_image split.one_image split.next_image split.gap split.common
        (Nat.lt_trans hbound hbcap)
      let ctx' := ctx.advance hh Q hsig hQcap ins
      have hnew : ins.next.fan.endpoint < b := by rw [ins.endpoint_image]; exact hbound
      have result := ih ins.next ctx' (by omega) (Nat.le_trans ha (Nat.le_of_lt hab)) hnew
      have hheight : h + (n + 1) = (h + 1) + n := by omega
      rw [hheight]
      exact result

/-- The insertion theorem for an arbitrary bounded background. The input line
is arbitrary: it need not be the image of a native root-2 line. -/
theorem line_to_fan (bg : InsertionBackground family m)
    {n a b : Nat} (line : Lined family m bg.k n a b) (ha : bg.a ≤ a) :
    ∃ fan : OwnedFan family m (n + 2), fan.fan.endpoint < b := by
  cases line with
  | nil _ =>
      exact ⟨bg.initial, Nat.lt_of_lt_of_le bg.initial_below ha⟩
  | @cons n a b c Q hsig hroot hnext hab tail =>
      have hr : bg.r < a := Nat.lt_of_lt_of_le (Nat.lt_trans bg.r_mu bg.mu_a) ha
      have hbcap : b < m := Nat.lt_of_le_of_lt tail.endpoints.1 tail.endpoints.2
      have hQcap : act family m Q bg.r < m := by
        have he := act_strict_below_cap family m Q bg.r a hr (by rw [hnext]; exact hbcap)
        rw [hnext] at he
        omega
      have hc : bg.initial.fan.endpoint < a := Nat.lt_of_lt_of_le bg.initial_below ha
      obtain ⟨hT, hbound⟩ := bg.segment_actor hsig hroot hnext ha hc hbcap
      let ins := bg.initial.insert ((family m).mul Q bg.j10) ((family m).mul bg.e bg.j3) bg.delta
        (by decide) hT bg.D_signature bg.D_zero bg.D_one bg.D_next
        bg.delta_gap bg.initial_common (Nat.lt_trans hbound hbcap)
      let ctx := bg.firstContext Q hsig hQcap ins
      have hnew : ins.next.fan.endpoint < b := by rw [ins.endpoint_image]; exact hbound
      have result := bg.grow_fan_along_line tail ins.next ctx (by decide)
        (Nat.le_trans ha (Nat.le_of_lt hab)) hnew
      have hheight : n + 1 + 2 = 3 + n := by omega
      rw [hheight]
      exact result

#print axioms Context.advance
#print axioms firstContext
#print axioms line_to_fan

end LaverLowerBounds.FiniteTable.InsertionBackground
