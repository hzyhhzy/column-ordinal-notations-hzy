import LaverLowerBounds.FiniteLines

set_option autoImplicit false

namespace LaverLowerBounds.FiniteTable

/-- A strictly increasing list of integer critical-point indices, including
its final endpoint. Values outside 0..length are unused. -/
structure PointChain (cap length : Nat) where
  point : Nat → Nat
  strict : ∀ {i j}, i < j → j ≤ length → point i < point j
  bounded : point length < cap

namespace PointChain

variable {cap length : Nat}

def ofAdjacent (point : Nat → Nat) (step : ∀ i, i < length → point i < point (i + 1))
    (bound : point length < cap) : PointChain cap length where
  point := point
  strict := by
    intro i j hij hj
    induction j generalizing i with
    | zero => omega
    | succ j ih =>
        have hs := step j (by omega)
        by_cases he : i = j
        · subst i; exact hs
        · exact Nat.lt_trans (ih (by omega) (by omega)) hs
  bounded := bound

theorem mono (a : PointChain cap length) {i j : Nat} (hij : i ≤ j) (hj : j ≤ length) :
    a.point i ≤ a.point j := by
  rcases Nat.eq_or_lt_of_le hij with he | he
  · simp only [he, Nat.le_refl]
  · exact Nat.le_of_lt (a.strict he hj)

theorem below (a : PointChain cap length) {i : Nat} (hi : i ≤ length) :
    a.point i < cap := Nat.lt_of_le_of_lt (a.mono hi (Nat.le_refl _)) a.bounded

theorem distance (a : PointChain cap length) {i j : Nat} (hij : i ≤ j) (hj : j ≤ length) :
    a.point i + (j - i) ≤ a.point j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction d with
  | zero => simp
  | succ d ih =>
      have hprev := ih (by omega)
      have hnext := a.strict (show i + d < i + (d + 1) by omega) hj
      omega

theorem index_le (a : PointChain cap length) {i : Nat} (hi : i ≤ length) : i ≤ a.point i := by
  have := a.distance (Nat.zero_le i) hi
  omega

def truncate (a : PointChain cap length) (k : Nat) (hk : k ≤ length) : PointChain cap k where
  point := a.point
  strict hij hj := a.strict hij (Nat.le_trans hj hk)
  bounded := a.below hk

def reindex (a : PointChain cap length) (k : Nat) (hk : length = k) : PointChain cap k where
  point := a.point
  strict hij hj := a.strict hij (by omega)
  bounded := by change a.point k < cap; rw [← hk]; exact a.bounded

def map (family : BinaryFamily) {m n : Nat} (a : PointChain m n) (e : Nat)
    (hcap : act family m e (a.point n) < m) : PointChain m n where
  point i := act family m e (a.point i)
  strict hij hj := act_strict_below_cap family m e _ _ (a.strict hij hj)
    (Nat.lt_of_le_of_lt (act_mono family m e (a.mono hj (Nat.le_refl _))) hcap)
  bounded := hcap

/-- Splice a strictly increasing image interval immediately after a retained
prefix. This is the numerical part of one actual BMS band copy. -/
def splicePoints (family : BinaryFamily) (m actor cut offset : Nat)
    (point : Nat → Nat) (i : Nat) : Nat :=
  if i ≤ cut then point i else act family m actor (point (i - offset))

theorem splicePoints_kept (family : BinaryFamily) (m actor cut offset : Nat)
    (point : Nat → Nat) {i : Nat} (hi : i ≤ cut) :
    splicePoints family m actor cut offset point i = point i := by
  simp only [splicePoints, if_pos hi]

theorem splicePoints_image (family : BinaryFamily) (m actor left offset : Nat)
    (point : Nat → Nat) {i : Nat}
    (hagree : i ≤ left → act family m actor (point i) = point (i + offset)) :
    splicePoints family m actor (left + offset) offset point (i + offset) =
      act family m actor (point i) := by
  unfold splicePoints
  split
  · exact (hagree (by omega)).symm
  · simp

def splice (family : BinaryFamily) {m n : Nat} (a : PointChain m n)
    (actor left right offset : Nat) (hlr : left < right) (hr : right ≤ n)
    (hc : left + offset + 1 ≤ n)
    (hleft : act family m actor (a.point left) = a.point (left + offset))
    (hright : act family m actor (a.point right) = a.point (left + offset + 1)) :
    PointChain m (right + offset) where
  point := splicePoints family m actor (left + offset) offset a.point
  strict := by
    intro i j hij hj
    have hend : act family m actor (a.point right) < m := by rw [hright]; exact a.below hc
    unfold splicePoints
    by_cases hjc : j ≤ left + offset
    · rw [if_pos (by omega), if_pos hjc]
      exact a.strict hij (by omega)
    · rw [if_neg hjc]
      have hjs : j - offset ≤ right := by omega
      have hjcap : act family m actor (a.point (j - offset)) < m :=
        Nat.lt_of_le_of_lt (act_mono family m actor (a.mono hjs hr)) hend
      by_cases hic : i ≤ left + offset
      · rw [if_pos hic]
        have hljs : left < j - offset := by omega
        have hs := act_strict_below_cap family m actor (a.point left)
          (a.point (j - offset)) (a.strict hljs (by omega)) hjcap
        rw [hleft] at hs
        exact Nat.lt_of_le_of_lt (a.mono hic (by omega)) hs
      · rw [if_neg hic]
        exact act_strict_below_cap family m actor _ _
          (a.strict (by omega) (by omega)) hjcap
  bounded := by
    unfold splicePoints
    rw [if_neg (by omega)]
    simp only [Nat.add_sub_cancel_right]
    rw [hright]
    exact a.below hc

theorem splice_endpoint (family : BinaryFamily) {m n : Nat} (a : PointChain m n)
    (actor left right offset : Nat) (hlr : left < right) (hr : right ≤ n)
    (hc : left + offset + 1 ≤ n)
    (hleft : act family m actor (a.point left) = a.point (left + offset))
    (hright : act family m actor (a.point right) = a.point (left + offset + 1)) :
    (a.splice family actor left right offset hlr hr hc hleft hright).point (right + offset) =
      a.point (left + offset + 1) := by
  change splicePoints family m actor (left + offset) offset a.point (right + offset) = _
  rw [splicePoints, if_neg (by omega)]
  simp only [Nat.add_sub_cancel_right]
  exact hright

end PointChain

/-- One parent port, with depth numbered from 1. -/
structure BandPort (family : BinaryFamily) (m : Nat) (point : Nat → Nat)
    (source target depth owner : Nat) : Prop where
  signature_eq : signature m owner = point source
  image : ∀ t, t ≤ depth → act family m owner (point (source + t)) = point (target + t)
  next : act family m owner (point target) = point (target + depth + 1)

namespace BandPort

theorem congrPoints {family : BinaryFamily} {m source target depth owner : Nat}
    {point nextPoint : Nat → Nat} (port : BandPort family m point source target depth owner)
    (hs : ∀ t, t ≤ depth → nextPoint (source + t) = point (source + t))
    (ht : ∀ t, t ≤ depth + 1 → nextPoint (target + t) = point (target + t)) :
    BandPort family m nextPoint source target depth owner where
  signature_eq := by simpa only [Nat.add_zero] using port.signature_eq.trans (hs 0 (by omega)).symm
  image t hd := by rw [hs t hd, port.image t hd, ht t (by omega)]
  next := by
    have hzero := ht 0 (by omega)
    simp only [Nat.add_zero] at hzero
    rw [hzero, port.next]
    simpa only [Nat.add_assoc] using (ht (depth + 1) (Nat.le_refl _)).symm

theorem transport {family : BinaryFamily} {m source target depth owner : Nat}
    {point nextPoint : Nat → Nat} (port : BandPort family m point source target depth owner)
    (e newSource newTarget : Nat)
    (hs : ∀ t, t ≤ depth → nextPoint (newSource + t) = act family m e (point (source + t)))
    (ht : ∀ t, t ≤ depth + 1 → nextPoint (newTarget + t) = act family m e (point (target + t))) :
    BandPort family m nextPoint newSource newTarget depth ((family m).mul e owner) where
  signature_eq := by
    rw [signature_mul, port.signature_eq]
    simpa only [Nat.add_zero] using (hs 0 (Nat.zero_le _)).symm
  image t hd := by
    rw [hs t hd, act_application, port.image t hd, ht t (by omega)]
  next := by
    have hzero := ht 0 (Nat.zero_le _)
    simp only [Nat.add_zero] at hzero
    rw [hzero, act_application, port.next]
    simpa only [Nat.add_assoc] using (ht (depth + 1) (Nat.le_refl _)).symm

end BandPort

#print axioms PointChain.splice
#print axioms BandPort.transport

end LaverLowerBounds.FiniteTable
