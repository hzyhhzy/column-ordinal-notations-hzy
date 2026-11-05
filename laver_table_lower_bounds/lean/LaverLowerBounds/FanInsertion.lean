import LaverLowerBounds.InitialWindow
import LaverLowerBounds.SignatureMovement
import LaverLowerBounds.PointInsertion

set_option autoImplicit false

namespace LaverLowerBounds.FiniteTable

/-- A closed fan with chosen owners and the two bottom points fixed to 0,1. -/
structure OwnedFan (family : BinaryFamily) (m h : Nat) where
  fan : ClosedFan family m h
  owner : Nat → Nat
  port : ∀ r, r < h → BandPort family m fan.chain.point 0 (h + 1) (r + 1) (owner r)
  zero : fan.chain.point 0 = 0
  one : fan.chain.point 1 = 1

def FanSeed.ownedInitial {family : BinaryFamily} {m : Nat} (s : FanSeed family m) :
    OwnedFan family m 2 where
  fan := s.initialFan
  owner := s.initialOwner
  port _r hr := s.initial_port hr
  zero := s.zero
  one := s.one

namespace OwnedFan

variable {family : BinaryFamily} {m h : Nat}

def insertedOwner (old : OwnedFan family m h) (T D : Nat) : Nat → Nat
  | 0 => (family m).mul T D
  | r + 1 => (family m).mul T (old.owner r)

/-- Besides existence, retain the exact coordinates and common cutoff needed
to iterate the insertion rule. All action images are guarded below m. -/
structure Insertion (old : OwnedFan family m h) (T D delta : Nat) where
  next : OwnedFan family m (h + 1)
  owners : ∀ r, next.owner r = old.insertedOwner T D r
  endpoint_image : next.fan.endpoint = act family m T old.fan.endpoint
  source_image : ∀ i, 1 ≤ i → i ≤ h →
    next.fan.chain.point (i + 1) = act family m T (old.fan.chain.point i)
  target_zero : next.fan.chain.point (h + 2) = act family m T (old.fan.chain.point (h + 1))
  target_image : ∀ i, 1 ≤ i → i ≤ h + 1 →
    next.fan.chain.point (h + i + 3) = act family m T (old.fan.chain.point (h + i + 1))
  target_one : next.fan.chain.point (h + 3) = act family m ((family m).mul T D) 1
  gap : next.fan.chain.point (h + 3) < act family m T delta
  common : ∀ r, r < h + 1 → congruent m (act family m T delta) (next.owner r) ((family m).mul T D)

def insert (old : OwnedFan family m h) (T D delta : Nat) (hh : 1 ≤ h)
    (hT : signature m T = 1) (hD : signature m D = 0)
    (hD0 : act family m D 0 = old.fan.chain.point (h + 1))
    (hD1 : act family m D 1 = delta)
    (hDv : act family m D (old.fan.chain.point (h + 1)) = old.fan.chain.point (h + 2))
    (hdelta : old.fan.chain.point (h + 1) < delta ∧ delta < old.fan.chain.point (h + 2))
    (hcommon : ∀ r, r < h → congruent m delta (old.owner r) D)
    (hcap : act family m T old.fan.endpoint < m) : Insertion old T D delta := by
  let w := h + 1
  let point := old.fan.chain.point
  have point0 : point 0 = 0 := old.zero
  have point1 : point 1 = 1 := old.one
  let newD := (family m).mul T D
  let v := act family m newD 1
  have hm : 1 < m := by rw [← old.one]; exact old.fan.chain.below (by omega)
  have t0 : act family m T 0 = 0 := fixes_below_signature family m T 0 (by rw [hT]; decide)
  have t1 : 1 < act family m T 1 := by
    have he := signature_lt_act family m T (by omega)
    rwa [hT] at he
  have hiV : point (w + 1) < old.fan.endpoint := old.fan.chain.strict (by dsimp [w]; omega) (Nat.le_refl _)
  have tv1cap : act family m T (point (w + 1)) < m :=
    Nat.lt_trans (act_strict_below_cap family m T _ _ hiV hcap) hcap
  have tdlt : act family m T delta < act family m T (point (w + 1)) :=
    act_strict_below_cap family m T _ _ hdelta.2 tv1cap
  have tdCap : act family m T delta < m := Nat.lt_trans tdlt tv1cap
  have nd0 : act family m newD 0 = act family m T (point w) := application_at family m T D t0 hD0
  have ndT1 : act family m newD (act family m T 1) = act family m T delta :=
    application_at family m T D rfl hD1
  have vlt : v < act family m T delta := by
    have he := act_strict_below_cap family m newD 1 (act family m T 1) t1 (by rw [ndT1]; exact tdCap)
    rw [ndT1] at he
    exact he
  have vlo : act family m T (point w) < v := by
    have he := act_strict_below_cap family m newD 0 1 (by decide) (Nat.lt_trans vlt tdCap)
    rw [nd0] at he
    exact he
  have vhi : v < act family m T (point (w + 1)) := Nat.lt_trans vlt tdlt
  let mapped := old.fan.chain.map family T hcap
  let first := mapped.insert 1 1 (by decide) (by omega)
    (by change act family m T (point 0) < 1; rw [point0, t0]; decide)
    (by change 1 < act family m T (point 1); rw [point1]; exact t1)
  have first_after {i : Nat} (hi : 1 < i) : first.point i = act family m T (point (i - 1)) := by
    exact PointChain.insertPoint_after _ _ _ _ hi
  have hlo : first.point (w + 2 - 1) < v := by
    rw [first_after (by dsimp [w]; omega)]
    have he : w + 2 - 1 - 1 = w := by omega
    rw [he]
    exact vlo
  have hhi : v < first.point (w + 2) := by
    rw [first_after (by dsimp [w]; omega)]
    have he : w + 2 - 1 = w + 1 := by omega
    rw [he]
    exact vhi
  let second := first.insert (w + 2) v (by dsimp [w]; omega) (by dsimp [w]; omega) hlo hhi
  let points := second.reindex (2 * ((h + 1) + 1) + 1) (by omega)
  have np0 : points.point 0 = 0 := by
    change PointChain.insertPoint _ (w + 2) v 0 = 0
    rw [PointChain.insertPoint_before _ _ _ _ (by omega)]
    change PointChain.insertPoint _ 1 1 0 = 0
    rw [PointChain.insertPoint_before _ _ _ _ (by decide)]
    change act family m T (point 0) = 0
    rw [point0, t0]
  have np1 : points.point 1 = 1 := by
    change PointChain.insertPoint _ (w + 2) v 1 = 1
    rw [PointChain.insertPoint_before _ _ _ _ (by dsimp [w]; omega)]
    change PointChain.insertPoint mapped.point 1 1 1 = 1
    exact PointChain.insertPoint_at _ _ _
  have nplow {i : Nat} (hlo : 1 < i) (hhi : i < w + 2) :
      points.point i = act family m T (point (i - 1)) := by
    change PointChain.insertPoint _ (w + 2) v i = _
    rw [PointChain.insertPoint_before _ _ _ _ hhi]
    exact first_after hlo
  have npmid : points.point (w + 2) = v := PointChain.insertPoint_at _ _ _
  have nphigh {i : Nat} (hi : w + 2 < i) :
      points.point i = act family m T (point (i - 2)) := by
    change PointChain.insertPoint _ (w + 2) v i = _
    rw [PointChain.insertPoint_after _ _ _ _ hi, first_after (by dsimp [w] at hi; omega)]
    have he : i - 1 - 1 = i - 2 := by omega
    rw [he]
  have nv0 : points.point (w + 1) = act family m T (point w) := by
    rw [nplow (by dsimp [w]; omega) (by omega), Nat.add_sub_cancel]
  have nv {i : Nat} (hi : 1 ≤ i) :
      points.point (w + i + 2) = act family m T (point (w + i)) := by
    rw [nphigh (by omega), Nat.add_sub_cancel]
  have nend : points.point (2 * (h + 2) + 1) = act family m T old.fan.endpoint := by
    rw [nphigh (by dsimp [w]; omega)]
    have he : 2 * (h + 2) + 1 - 2 = 2 * (h + 1) + 1 := by omega
    rw [he]
    rfl
  have common : ∀ r, r < h + 1 → congruent m (act family m T delta) (old.insertedOwner T D r) newD := by
    intro r hr
    cases r with
    | zero => exact congruent_refl _ _ _
    | succ r => exact congruent_transport family m (hcommon r (by omega)) T
  have ports : ∀ r, r < h + 1 →
      BandPort family m points.point 0 ((h + 1) + 1) (r + 1) (old.insertedOwner T D r) := by
    intro r hr
    cases r with
    | zero =>
        refine ⟨?_, ?_, ?_⟩
        · change signature m newD = points.point 0
          rw [signature_mul, hD, t0, np0]
        · intro t ht
          match t with
          | 0 =>
              simp only [Nat.add_zero]
              change act family m newD (points.point 0) = points.point (w + 1)
              rw [np0, nv0, nd0]
          | 1 =>
              change act family m newD (points.point 1) = points.point (w + 1 + 1)
              rw [np1]
              simpa only [Nat.add_assoc] using npmid.symm
          | t + 2 => omega
        · change act family m newD (points.point (w + 1)) = points.point (w + 1 + 1 + 1)
          rw [nv0, act_application, hDv]
          have he := nv (i := 1) (Nat.le_refl _)
          simpa only [Nat.add_assoc, w] using he.symm
    | succ r =>
        have oldPort := old.port r (by omega)
        have isig : signature m (old.owner r) = 0 := oldPort.signature_eq.trans old.zero
        refine ⟨?_, ?_, ?_⟩
        · change signature m ((family m).mul T (old.owner r)) = points.point 0
          rw [signature_mul, isig, t0, np0]
        · intro t ht
          match t with
          | 0 =>
              simp only [Nat.add_zero]
              change act family m ((family m).mul T (old.owner r)) (points.point 0) = points.point (w + 1)
              rw [np0, nv0]
              have he := oldPort.image 0 (by omega)
              simp only [Nat.add_zero, old.zero] at he
              exact application_at family m T (old.owner r) t0 he
          | 1 =>
              change act family m ((family m).mul T (old.owner r)) (points.point 1) = points.point (w + 1 + 1)
              rw [np1]
              have he := congruent_read family m (congruent_symm (common (r + 1) hr)) vlt
              have hg : points.point (w + 1 + 1) = v := by simpa only [Nat.add_assoc] using npmid
              rw [hg]
              exact he.symm
          | t + 2 =>
              have hsmall : t + 1 ≤ r + 1 := by omega
              have hs : points.point (0 + (t + 2)) = act family m T (point (t + 1)) := by
                rw [nplow (by omega) (by dsimp [w]; omega)]
                have he : 0 + (t + 2) - 1 = t + 1 := by omega
                rw [he]
              change act family m ((family m).mul T (old.owner r)) (points.point (0 + (t + 2))) =
                points.point (w + 1 + (t + 2))
              rw [hs, act_application]
              have oldImage := oldPort.image (t + 1) hsmall
              simp only [Nat.zero_add] at oldImage
              change act family m T (act family m (old.owner r) (old.fan.chain.point (t + 1))) = _
              rw [oldImage]
              have he := nv (i := t + 1) (by omega)
              have hind : w + (t + 1) + 2 = w + 1 + (t + 2) := by omega
              rw [hind] at he
              exact he.symm
        · change act family m ((family m).mul T (old.owner r)) (points.point (w + 1)) =
            points.point (w + 1 + (r + 1 + 1) + 1)
          rw [nv0, act_application, oldPort.next]
          have he := nv (i := r + 2) (by omega)
          have hind : w + (r + 2) + 2 = w + 1 + (r + 1 + 1) + 1 := by omega
          have hind' : w + (r + 2) = h + 1 + (r + 1) + 1 := by dsimp [w]; omega
          rw [hind, hind'] at he
          exact he.symm
  have closerSig : signature m ((family m).mul T old.fan.closer) = points.point (h + 2) := by
    rw [signature_mul, old.fan.closer_signature]
    exact nv0.symm
  have closerFirst : act family m ((family m).mul T old.fan.closer) (points.point (h + 2)) =
      points.point (2 * (h + 2)) := by
    change act family m _ (points.point (w + 1)) = _
    rw [nv0, act_application, old.fan.closer_first]
    have he := nv (i := w) (by dsimp [w]; omega)
    have hindex : w + w + 2 = 2 * (h + 2) := by dsimp [w]; omega
    rw [hindex] at he
    simpa only [Nat.two_mul, w] using he.symm
  have closerNext : act family m ((family m).mul T old.fan.closer) (points.point (2 * (h + 2))) =
      points.point (2 * (h + 2) + 1) := by
    have he := nv (i := w) (by dsimp [w]; omega)
    have hindex : w + w + 2 = 2 * (h + 2) := by dsimp [w]; omega
    rw [hindex] at he
    rw [he, act_application]
    have hindex2 : w + w = 2 * (h + 1) := by dsimp [w]; omega
    rw [hindex2, old.fan.closer_next, nend]
    rfl
  let newFan : ClosedFan family m (h + 1) := {
    chain := points
    ports r hr := ⟨old.insertedOwner T D r, ports r hr⟩
    closer := (family m).mul T old.fan.closer
    closer_signature := closerSig
    closer_first := closerFirst
    closer_next := closerNext }
  let next : OwnedFan family m (h + 1) := {
    fan := newFan
    owner := old.insertedOwner T D
    port := ports
    zero := np0
    one := np1 }
  refine ⟨next, fun _ => rfl, nend, ?_, nv0, ?_, npmid, ?_, common⟩
  · intro i hi hih
    change points.point (i + 1) = _
    rw [nplow (by omega) (by dsimp [w]; omega), Nat.add_sub_cancel]
  · intro i hi _
    have he := nv hi
    simpa only [w, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using he
  · change points.point (h + 3) < act family m T delta
    have he : h + 3 = w + 2 := by rfl
    rw [he, npmid]
    exact vlt

#print axioms insert

end OwnedFan
end LaverLowerBounds.FiniteTable
