import LaverLowerBounds.InsertionInvariant

set_option autoImplicit false

namespace LaverLowerBounds.FiniteTable

namespace InsertionInvariant

variable {family : BinaryFamily} {m h : Nat} {old : OwnedFan family m h}

def advance (ctx : InsertionInvariant old) (hm : PeriodAtLeast32 (family m)) (hh : 1 ≤ h)
    (Q : Nat) (hQ : signature m Q = 2) (hcap : act family m Q 4 < m)
    (ins : OwnedFan.Insertion old ((family m).mul Q 10) ctx.D ctx.delta) : InsertionInvariant ins.next := by
  let T := (family m).mul Q 10
  let Pnew := (family m).mul T ctx.W :: pushWord family m T ctx.P
  have rebuild := ctx.rebuild hm hh
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
      exact Nat.lt_of_lt_of_le rebuild.W_signature_above (le_act family m T _ (signature_le _ _))
    · exact pushWord_above family m T ctx.high_factors e he
  · intro r hr
    have he := ins.common r hr
    have hzero := ins.owners 0
    change ins.next.owner 0 = (family m).mul T ctx.D at hzero
    rw [hzero]
    exact he
  · rw [ins.owners 0]
    change (family m).mul T ((family m).mul ctx.W ctx.Z) =
      wordTerm family m (Pnew ++ [T, ctx.Q]) 3
    rw [List.cons_append]
    change (family m).mul T ((family m).mul ctx.W ctx.Z) =
      (family m).mul ((family m).mul T ctx.W)
        (wordTerm family m (pushWord family m T ctx.P ++ [T, ctx.Q]) 3)
    rw [wordTerm_append]
    change (family m).mul T ((family m).mul ctx.W ctx.Z) =
      (family m).mul ((family m).mul T ctx.W)
        (wordTerm family m (pushWord family m T ctx.P) ((family m).mul T ((family m).mul ctx.Q 3)))
    rw [pushWord_term]
    exact (family m).mul_distrib T ctx.W ctx.Z

end InsertionInvariant

namespace FanSeed

def firstInvariant (family : BinaryFamily) (m : Nat) (hm : PeriodAtLeast32 (family m))
    (Q : Nat) (hQ : signature m Q = 2) (hcap : act family m Q 4 < m)
    (ins : OwnedFan.Insertion (fanSeed family m hm).ownedInitial ((family m).mul Q 10)
      (fanSeed family m hm).firstD (fanSeed family m hm).firstDelta) : InsertionInvariant ins.next := by
  let s := fanSeed family m hm
  let T := (family m).mul Q 10
  have h9 : 9 ≤ m := Nat.le_of_lt (threshold_gt_nine family m hm)
  have sigE : signature m s.e = 2 := s.termData.e_signature
  have hpow : 512 ≤ 2 ^ m := Nat.pow_le_pow_right (n := 2) (by decide) h9
  have zero3 : (family m).mul 0 3 = 3 := by rw [(family m).zero_mul, Nat.mod_eq_of_lt (by omega)]
  refine {
    P := [(family m).mul T s.e]
    Q := Q
    U := 0
    Q_signature := hQ
    U_signature := by rw [signature_zero]; omega
    Q_four_below := hcap
    high_factors := ?_
    epsilon := act family m T s.firstDelta
    epsilon_above := ins.gap
    common := ?_
    first := ?_ }
  · intro e he
    have he' : e = (family m).mul T s.e := by simpa using he
    subst e
    rw [signature_mul, sigE]
    exact Nat.lt_of_lt_of_le (by decide : 1 < 2) (le_act family m T 2 (by omega))
  · intro r hr
    have he := ins.common r hr
    have hzero := ins.owners 0
    change ins.next.owner 0 = (family m).mul T s.firstD at hzero
    rw [hzero]
    exact he
  · rw [ins.owners 0]
    change (family m).mul T ((family m).mul s.e 3) =
      wordTerm family m ([(family m).mul T s.e] ++ [T, 0]) 3
    simp only [List.singleton_append, wordTerm, zero3]
    exact (family m).mul_distrib T s.e 3

end FanSeed

theorem grow_fan_along_line (family : BinaryFamily) (m : Nat) (hm : PeriodAtLeast32 (family m))
    {n a b : Nat} (line : Lined family m 2 n a b) :
    ∀ {h : Nat} (old : OwnedFan family m h) (_ctx : InsertionInvariant old),
      1 ≤ h → theta family m 6 ≤ a → old.fan.endpoint < a →
      ∃ next : OwnedFan family m (h + n), next.fan.endpoint < b := by
  induction line with
  | nil _ =>
      intro h old _ _ _ hc
      exact ⟨old, hc⟩
  | @cons n a b c Q hsig hroot hnext hab tail ih =>
      intro h old ctx hh ha hc
      have hd := higherData family m hm
      have hmu : act family m 7 2 < a := Nat.lt_of_lt_of_le (Nat.lt_trans hd.mu_lt_five hd.five_lt_six) ha
      have h4 : 4 < a := by have := hd.mu_lower; omega
      have hbcap : b < m := Nat.lt_of_le_of_lt tail.endpoints.1 tail.endpoints.2
      have hQcap : act family m Q 4 < m := by
        have he := act_strict_below_cap family m Q 4 a h4 (by rw [hnext]; exact hbcap)
        rw [hnext] at he
        omega
      have split := ctx.rebuild hm hh
      obtain ⟨hT, hbound⟩ := insertion_actor family m hm hsig hroot hnext hmu hc hbcap
      let ins := old.insert ((family m).mul Q 10) ctx.D ctx.delta hh hT
        split.signature_eq split.zero_image split.one_image split.next_image split.gap split.common
        (Nat.lt_trans hbound hbcap)
      let ctx' := ctx.advance hm hh Q hsig hQcap ins
      have hnew : ins.next.fan.endpoint < b := by rw [ins.endpoint_image]; exact hbound
      have result := ih ins.next ctx' (by omega) (Nat.le_trans ha (Nat.le_of_lt hab)) hnew
      have hheight : h + (n + 1) = (h + 1) + n := by omega
      rw [hheight]
      exact result

/-- OLD section 6, now a concrete finite-table construction for every finite
input line. The number of insertions is arbitrary, not a tested small bound. -/
theorem line_to_fan (family : BinaryFamily) (m : Nat) (hm : PeriodAtLeast32 (family m))
    {n a b : Nat} (line : Lined family m 2 n a b) (ha : theta family m 6 ≤ a) :
    ∃ fan : OwnedFan family m (n + 2), fan.fan.endpoint < b := by
  let s := fanSeed family m hm
  cases line with
  | nil _ =>
      exact ⟨s.ownedInitial, Nat.lt_of_lt_of_le s.initial_fan_endpoint ha⟩
  | @cons n a b c Q hsig hroot hnext hab tail =>
      have hd := higherData family m hm
      have hmu : act family m 7 2 < a := Nat.lt_of_lt_of_le (Nat.lt_trans hd.mu_lt_five hd.five_lt_six) ha
      have h4 : 4 < a := by have := hd.mu_lower; omega
      have hbcap : b < m := Nat.lt_of_le_of_lt tail.endpoints.1 tail.endpoints.2
      have hQcap : act family m Q 4 < m := by
        have he := act_strict_below_cap family m Q 4 a h4 (by rw [hnext]; exact hbcap)
        rw [hnext] at he
        omega
      have hc : s.ownedInitial.fan.endpoint < a := Nat.lt_of_lt_of_le s.initial_fan_endpoint ha
      have split := FanSeed.firstSplit family m hm
      obtain ⟨hT, hbound⟩ := insertion_actor family m hm hsig hroot hnext hmu hc hbcap
      let ins := s.ownedInitial.insert ((family m).mul Q 10) s.firstD s.firstDelta
        (by decide) hT split.signature_eq split.zero_image split.one_image split.next_image
        split.gap split.common (Nat.lt_trans hbound hbcap)
      let ctx := FanSeed.firstInvariant family m hm Q hsig hQcap ins
      have hnew : ins.next.fan.endpoint < b := by rw [ins.endpoint_image]; exact hbound
      have result := grow_fan_along_line family m hm tail ins.next ctx (by decide)
        (Nat.le_trans ha (Nat.le_of_lt hab)) hnew
      have hheight : n + 1 + 2 = 3 + n := by omega
      rw [hheight]
      exact result

theorem initial_height_eighteen (family : BinaryFamily) (m : Nat) (hm : PeriodAtLeast32 (family m)) :
    ∃ fan : OwnedFan family m 18, fan.fan.endpoint < (fanSeed family m hm).entry := by
  obtain ⟨endpoint, line, hbound⟩ := FanSeed.initial_sixteen_line family m hm
  obtain ⟨fan, hfan⟩ := line_to_fan family m hm line (Nat.le_refl _)
  exact ⟨fan, Nat.lt_trans hfan hbound⟩

#print axioms InsertionInvariant.advance
#print axioms line_to_fan
#print axioms initial_height_eighteen

end LaverLowerBounds.FiniteTable
