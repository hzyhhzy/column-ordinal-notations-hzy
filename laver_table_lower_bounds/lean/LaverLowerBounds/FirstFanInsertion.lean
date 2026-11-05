import LaverLowerBounds.FanInsertion

set_option autoImplicit false

namespace LaverLowerBounds.FiniteTable

theorem ten_low (family : BinaryFamily) (m : Nat) (hm : PeriodAtLeast32 (family m)) :
    signature m 10 = 1 ∧ act family m 10 1 = 2 ∧ act family m 10 2 = act family m 7 2 := by
  have h9 : 9 ≤ m := Nat.le_of_lt (threshold_gt_nine family m hm)
  have p11 := act_from_low family m 1 1 12 2 h9 (LowProducts.v1_2 (family 9)) (by decide) (by decide)
  have p101 := act_from_low family m 10 1 508 2 h9 (LowProducts.v10_2 (family 9)) (by decide) (by decide)
  have hd := higherData family m hm
  have he := next_small family m 10 1 h9 (by decide)
  rw [p101, p11, hd.k2] at he
  exact ⟨signature_from_nine m 10 1 h9 (by decide) (by decide), p101, he.symm⟩

/-- One input line segment supplies the actual insertion actor Q*j10, with a
strict cap bound. This estimate is uniform over the current fan height. -/
theorem insertion_actor (family : BinaryFamily) (m : Nat) (hm : PeriodAtLeast32 (family m))
    {Q a b C : Nat} (hsig : signature m Q = 2) (ha : act family m Q 2 = a)
    (hb : act family m Q a = b) (hmu : act family m 7 2 < a) (hC : C < a) (hcap : b < m) :
    signature m ((family m).mul Q 10) = 1 ∧ act family m ((family m).mul Q 10) C < b := by
  obtain ⟨sig10, p101, p102⟩ := ten_low family m hm
  have q1 : act family m Q 1 = 1 := fixes_below_signature family m Q 1 (by rw [hsig]; decide)
  have tsig : signature m ((family m).mul Q 10) = 1 := by rw [signature_mul, sig10, q1]
  have ta : act family m ((family m).mul Q 10) a = act family m Q (act family m 7 2) :=
    application_at family m Q 10 ha p102
  have hab : act family m Q (act family m 7 2) < b := by
    have he := act_strict_below_cap family m Q _ a hmu (by rw [hb]; exact hcap)
    rwa [hb] at he
  have ht := act_strict_below_cap family m ((family m).mul Q 10) C a hC (by rw [ta]; omega)
  exact ⟨tsig, Nat.lt_trans ht (by rw [ta]; exact hab)⟩

namespace FanSeed

variable {family : BinaryFamily} {m : Nat}

def firstD (s : FanSeed family m) := (family m).mul s.e 3
def firstDelta (s : FanSeed family m) := act family m s.e 3

structure FirstSplit (s : FanSeed family m) : Prop where
  signature_eq : signature m s.firstD = 0
  zero_image : act family m s.firstD 0 = s.ownedInitial.fan.chain.point 3
  one_image : act family m s.firstD 1 = s.firstDelta
  next_image : act family m s.firstD (s.ownedInitial.fan.chain.point 3) = s.ownedInitial.fan.chain.point 4
  gap : s.ownedInitial.fan.chain.point 3 < s.firstDelta ∧ s.firstDelta < s.ownedInitial.fan.chain.point 4
  common : ∀ r, r < 2 → congruent m s.firstDelta (s.ownedInitial.owner r) s.firstD

theorem firstSplit (family : BinaryFamily) (m : Nat) (hm : PeriodAtLeast32 (family m)) :
    FirstSplit (fanSeed family m hm) := by
  let s := fanSeed family m hm
  have hd := s.termData
  have hh := higherData family m hm
  have h9 : 9 ≤ m := Nat.le_of_lt (threshold_gt_nine family m hm)
  have sig3 : signature m 3 = 0 := signature_from_nine m 3 0 h9 (by decide) (by decide)
  have p30 := act_from_low family m 3 0 4 2 h9 (LowProducts.v3_1 (family 9)) (by decide) (by decide)
  have p31 := act_from_low family m 3 1 8 3 h9 (LowProducts.v3_2 (family 9)) (by decide) (by decide)
  have p32 := act_from_low family m 3 2 464 4 h9 (LowProducts.v3_4 (family 9)) (by decide) (by decide)
  have esig : signature m s.e = 2 := hd.e_signature
  have e0 : act family m s.e 0 = 0 := fixes_below_signature family m s.e 0 (by omega)
  have e1 : act family m s.e 1 = 1 := fixes_below_signature family m s.e 1 (by omega)
  have e2 : act family m s.e 2 = 4 := hd.e2
  have e4 : act family m s.e 4 = s.points.point 5 := hd.e3
  have e4cap : act family m s.e 4 < m := by rw [e4]; exact s.points.below (by decide)
  have deltaCap : s.firstDelta < m :=
    Nat.lt_trans (act_strict_below_cap family m s.e 3 4 (by decide) e4cap) e4cap
  have gaplo : 4 < s.firstDelta := by
    have he := act_strict_below_cap family m s.e 2 3 (by decide) deltaCap
    rw [e2] at he
    exact he
  have gaphi : s.firstDelta < s.points.point 5 := by
    have he := act_strict_below_cap family m s.e 3 4 (by decide) e4cap
    rwa [e4] at he
  have k3 : congruent m 3 11 3 := congruent_trans
    (congruent_lower hh.square (by have := hh.mu_lower; omega))
    (congruent_symm (low_square family m h9))
  have cf : congruent m s.firstDelta s.f s.firstD := congruent_transport family m k3 s.e
  have cj : congruent m s.firstDelta s.J s.f := by
    have he := app_critical family m s.p s.f
    apply congruent_lower he
    rw [hd.p_signature]
    exact Nat.le_of_lt (Nat.lt_trans gaphi hd.five_lt_beta)
  refine ⟨?_, ?_, ?_, ?_, ⟨gaplo, gaphi⟩, ?_⟩
  · change signature m ((family m).mul s.e 3) = 0
    rw [signature_mul, sig3, e0]
  · exact (application_at family m s.e 3 e0 p30).trans e2
  · exact application_at family m s.e 3 e1 p31
  · exact (application_at family m s.e 3 e2 p32).trans e4
  · intro r hr
    match r with
    | 0 => exact cf
    | 1 => exact congruent_trans cj cf
    | n + 2 => omega

/-- The first genuine enlargement is now assembled from the actual q5 entrance.
This is an integration theorem, not the final Lambda+omega+1 bound. -/
theorem height_three_fan (family : BinaryFamily) (m : Nat) (hm : PeriodAtLeast32 (family m)) :
    ∃ fan : OwnedFan family m 3, fan.fan.endpoint < (fanSeed family m hm).entry := by
  let s := fanSeed family m hm
  have split := firstSplit family m hm
  have hd := s.termData
  have hhi := higherData family m hm
  obtain ⟨endpt, line, hend⟩ := initial_sixteen_line family m hm
  cases line with
  | @cons n a b c Q hsig hroot hnext hab tail =>
      have hbcap : b < m := Nat.lt_of_le_of_lt tail.endpoints.1 tail.endpoints.2
      have hmu : act family m 7 2 < theta family m 6 := Nat.lt_trans hhi.mu_lt_five hhi.five_lt_six
      have hC : s.ownedInitial.fan.endpoint < theta family m 6 := s.initial_fan_endpoint
      obtain ⟨hT, hbound⟩ := insertion_actor family m hm hsig hroot hnext hmu hC hbcap
      let result := s.ownedInitial.insert ((family m).mul Q 10) s.firstD s.firstDelta
        (by decide) hT split.signature_eq split.zero_image split.one_image split.next_image
        split.gap split.common (Nat.lt_trans hbound hbcap)
      refine ⟨result.next, ?_⟩
      rw [result.endpoint_image]
      exact Nat.lt_trans hbound (Nat.lt_of_le_of_lt tail.endpoints.1 hend)

theorem threshold_three_count (family : BinaryFamily) (m : Nat) (hm : PeriodAtLeast32 (family m)) :
    ∃ n, PrefixDescent.Stops (fun a => ParentBMS.expand a 1) (ParentBMS.triple 3) n ∧ n < m := by
  obtain ⟨fan, _⟩ := height_three_fan family m hm
  obtain ⟨n, hn, hnb⟩ := fan.fan.counting_bound (by decide)
  exact ⟨n, hn, Nat.lt_trans hnb fan.fan.chain.bounded⟩

#print axioms firstSplit
#print axioms height_three_fan
#print axioms threshold_three_count

end FanSeed
end LaverLowerBounds.FiniteTable
