import LaverLowerBounds.BandTermination

set_option autoImplicit false

namespace LaverLowerBounds.FiniteTable

open ParentBMS

/-- U_0,...,U_h,V_0,...,V_(h+1),C, together with the actual port owners
and a closing actor L : V_0 -> V_(h+1) -> C. -/
structure ClosedFan (family : BinaryFamily) (m h : Nat) where
  chain : PointChain m (2 * (h + 1) + 1)
  ports : ∀ r, r < h → ∃ e, BandPort family m chain.point 0 (h + 1) (r + 1) e
  closer : Nat
  closer_signature : signature m closer = chain.point (h + 1)
  closer_first : act family m closer (chain.point (h + 1)) = chain.point (2 * (h + 1))
  closer_next : act family m closer (chain.point (2 * (h + 1))) = chain.point (2 * (h + 1) + 1)

namespace ClosedFan

variable {family : BinaryFamily} {m h : Nat}

def endpoint (fan : ClosedFan family m h) : Nat := fan.chain.point (2 * (h + 1) + 1)

def map (fan : ClosedFan family m h) (e : Nat) (hcap : act family m e fan.endpoint < m) :
    ClosedFan family m h where
  chain := fan.chain.map family e hcap
  ports r hr := by
    obtain ⟨owner, port⟩ := fan.ports r hr
    exact ⟨(family m).mul e owner, port.transport e 0 (h + 1)
      (fun _ _ => rfl) (fun _ _ => rfl)⟩
  closer := (family m).mul e fan.closer
  closer_signature := by rw [signature_mul, fan.closer_signature]; rfl
  closer_first := by change act family m _ (act family m e _) = _; rw [act_application, fan.closer_first]; rfl
  closer_next := by change act family m _ (act family m e _) = _; rw [act_application, fan.closer_next]; rfl

theorem triple_shape (h : Nat) : Shape h 0 (triple h) := by
  intro j c hj
  have hlen : j < 3 := by simpa [triple] using (List.getElem?_eq_some_iff.mp hj).1
  have hc : c = [] ∨ c = List.replicate h 0 := by
    match j with
    | 0 => simp [triple] at hj; exact Or.inl hj
    | 1 => simp [triple] at hj; exact Or.inr hj.symm
    | 2 => simp [triple] at hj; exact Or.inr hj.symm
    | n + 3 => omega
  rcases hc with rfl | rfl
  · simp
  · have hjpos : 0 < j ∨ h = 0 := by
      by_cases hz : j = 0
      · subst j
        have he : List.replicate h 0 = [] := by simpa [triple] using hj.symm
        have := congrArg List.length he
        simp only [List.length_replicate, List.length_nil] at this
        exact Or.inr this
      · exact Or.inl (by omega)
    constructor
    · simp
    · intro p hp
      have hpzero : p = 0 := (List.mem_replicate.mp hp).2
      have hhpos : h ≠ 0 := (List.mem_replicate.mp hp).1
      omega

theorem represented (fan : ClosedFan family m h) :
    ∃ b : BandRepresentation family m h (triple h), b.endpoint = fan.endpoint := by
  let w := h + 1
  have hw : 0 < w := by dsimp [w]; omega
  let raw := fan.chain.splice family fan.closer w (2 * w) w (by omega) (by omega)
    (by omega) (by simpa only [Nat.two_mul] using fan.closer_first)
    (by simpa only [Nat.two_mul] using fan.closer_next)
  let points := raw.reindex ((triple h).length * w) (by simp [triple]; omega)
  have kept : ∀ i, i ≤ 2 * w → points.point i = fan.chain.point i := by
    intro i hi
    change PointChain.splicePoints family m fan.closer (w + w) w fan.chain.point i = _
    exact PointChain.splicePoints_kept _ _ _ _ _ _ (by omega)
  have image : ∀ t, t ≤ w → points.point (2 * w + t) = act family m fan.closer (fan.chain.point (w + t)) := by
    intro t ht
    change PointChain.splicePoints family m fan.closer (w + w) w fan.chain.point (2 * w + t) = _
    have hind : 2 * w + t = (w + t) + w := by omega
    rw [hind]
    apply PointChain.splicePoints_image
    intro hlow
    have ht0 : t = 0 := by omega
    subst t
    simpa only [Nat.add_zero, Nat.two_mul] using fan.closer_first
  have hports : ∀ j c r p, (triple h)[j]? = some c → c[r]? = some p →
      ∃ e, BandPort family m points.point (p * (h + 1)) (j * (h + 1)) (r + 1) e := by
    intro j c r p hj hp
    have hjlt : j < 3 := by simpa [triple] using (List.getElem?_eq_some_iff.mp hj).1
    match j with
    | 0 => simp [triple] at hj; subst c; simp at hp
    | 1 =>
        simp [triple] at hj
        subst c
        have hr : r < h := by simpa using (List.getElem?_eq_some_iff.mp hp).1
        have hpzero : p = 0 := (List.mem_replicate.mp (List.mem_of_getElem? hp)).2
        subst p
        obtain ⟨e, port⟩ := fan.ports r hr
        refine ⟨e, ?_⟩
        simp only [Nat.zero_mul, Nat.one_mul]
        exact port.congrPoints (fun t ht => kept _ (by dsimp [w]; omega))
          (fun t ht => kept _ (by dsimp [w]; omega))
    | 2 =>
        simp [triple] at hj
        subst c
        have hr : r < h := by simpa using (List.getElem?_eq_some_iff.mp hp).1
        have hpzero : p = 0 := (List.mem_replicate.mp (List.mem_of_getElem? hp)).2
        subst p
        obtain ⟨e, port⟩ := fan.ports r hr
        refine ⟨(family m).mul fan.closer e, ?_⟩
        simp only [Nat.zero_mul]
        apply port.transport fan.closer 0 (2 * (h + 1))
        · intro t ht
          rw [kept _ (by dsimp [w]; omega)]
          symm
          apply fixes_below_signature
          rw [fan.closer_signature]
          exact fan.chain.strict (by omega) (by omega)
        · intro t ht
          exact image t (by dsimp [w]; omega)
    | n + 3 => omega
  let b : BandRepresentation family m h (triple h) := {
    shape := triple_shape h
    points := points
    ports := hports }
  refine ⟨b, ?_⟩
  change points.point ((triple h).length * w) = _
  have hind : (triple h).length * w = 2 * w + w := by simp [triple]; omega
  calc
    points.point ((triple h).length * w) = points.point (2 * w + w) := congrArg points.point hind
    _ = act family m fan.closer (fan.chain.point (w + w)) := image w (Nat.le_refl _)
    _ = fan.endpoint := by simpa only [Nat.two_mul, endpoint, w] using fan.closer_next

theorem counting_bound (fan : ClosedFan family m h) (hh : 3 ≤ h) :
    ∃ n, PrefixDescent.Stops (fun s => expand s 1) (triple h) n ∧ n < fan.endpoint := by
  obtain ⟨b, hb⟩ := fan.represented
  obtain ⟨n, hn, hnb⟩ := b.triple_stops_below_endpoint hh
  exact ⟨n, hn, by omega⟩

theorem count_lt (fan : ClosedFan family m h) (hh : 3 ≤ h) {n : Nat}
    (hn : PrefixDescent.Stops (fun s => expand s 1) (triple h) n) : n < fan.endpoint := by
  obtain ⟨b, hb⟩ := fan.represented
  have := b.triple_count_below_endpoint hh hn
  omega

#print axioms map
#print axioms represented
#print axioms counting_bound

end ClosedFan
end LaverLowerBounds.FiniteTable
