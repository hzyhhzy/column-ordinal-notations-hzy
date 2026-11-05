import LaverLowerBounds.FinitePointChain
import LaverLowerBounds.ParentShape

set_option autoImplicit false

namespace LaverLowerBounds.FiniteTable

theorem band_index_lt {j c h t : Nat} (hj : j < c) (ht : t ≤ h) :
    j * (h + 1) + t < c * (h + 1) := by
  have hm := Nat.mul_le_mul_right (h + 1) (show j + 1 ≤ c by omega)
  rw [Nat.add_mul] at hm
  simp only [Nat.one_mul] at hm
  omega

theorem band_index_le {j c h t : Nat} (hj : j < c) (ht : t ≤ h + 1) :
    j * (h + 1) + t ≤ c * (h + 1) := by
  have hm := Nat.mul_le_mul_right (h + 1) (show j + 1 ≤ c by omega)
  rw [Nat.add_mul] at hm
  simp only [Nat.one_mul] at hm
  omega

/-- The actual spliced point array and its exact coordinate laws. -/
structure BandCopyGeometry (family : BinaryFamily) (m h x root depth owner : Nat)
    (old : PointChain m ((x + 1) * (h + 1))) where
  points : PointChain m ((x + (x - root)) * (h + 1))
  kept : ∀ i, i ≤ x * (h + 1) + depth → points.point i = old.point i
  image : ∀ j, root ≤ j → j < x → ∀ t, t ≤ h + 1 →
    points.point ((j + (x - root)) * (h + 1) + t) =
      act family m owner (old.point (j * (h + 1) + t))
  fixes : ∀ j, j < root → ∀ t, t ≤ h →
    act family m owner (old.point (j * (h + 1) + t)) = old.point (j * (h + 1) + t)
  endpoint : points.point ((x + (x - root)) * (h + 1)) =
    old.point (x * (h + 1) + depth + 1)

def makeBandCopyGeometry (family : BinaryFamily) {m h x root depth owner : Nat}
    (old : PointChain m ((x + 1) * (h + 1)))
    (hr : root < x) (hd : depth ≤ h)
    (port : BandPort family m old.point (root * (h + 1)) (x * (h + 1)) depth owner) :
    BandCopyGeometry family m h x root depth owner old := by
  let w := h + 1
  let d := x - root
  have hsum : root + d = x := by dsimp [d]; omega
  have hm : root * w + d * w = x * w := by rw [← Nat.add_mul, hsum]
  have hcut : root * w + depth + d * w = x * w + depth := by omega
  have hlr : root * w + depth < x * w := band_index_lt hr hd
  have hx : x * w ≤ (x + 1) * w := Nat.mul_le_mul_right _ (by omega)
  have hc : root * w + depth + d * w + 1 ≤ (x + 1) * w := by
    rw [hcut, Nat.add_mul]
    dsimp [w]
    omega
  have hleft : act family m owner (old.point (root * w + depth)) =
      old.point (root * w + depth + d * w) := by
    rw [hcut]
    exact port.image depth (Nat.le_refl _)
  have hright : act family m owner (old.point (x * w)) =
      old.point (root * w + depth + d * w + 1) := by rw [hcut]; exact port.next
  let raw := old.splice family owner (root * w + depth) (x * w) (d * w) hlr hx hc hleft hright
  have hlen : x * w + d * w = (x + d) * w := (Nat.add_mul _ _ _).symm
  let points : PointChain m ((x + d) * w) := {
    point := raw.point
    strict := by intro i j hij hj; exact raw.strict hij (by omega)
    bounded := by change raw.point ((x + d) * w) < m; rw [← hlen]; exact raw.bounded }
  have hp : ∀ i, points.point i =
      PointChain.splicePoints family m owner (x * w + depth) (d * w) old.point i := by
    intro i
    change PointChain.splicePoints family m owner (root * w + depth + d * w) (d * w) old.point i = _
    rw [hcut]
  refine ⟨points, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hp]
    exact PointChain.splicePoints_kept _ _ _ _ _ _ hi
  · intro j hj hjx t ht
    rw [hp]
    have hind : (j + d) * w + t = (j * w + t) + d * w := by rw [Nat.add_mul]; omega
    rw [hind, ← hcut]
    apply PointChain.splicePoints_image
    intro hlow
    have hjroot : j = root := by
      by_cases he : j = root
      · exact he
      · have hx' := band_index_lt (show root < j by omega) hd
        change root * w + depth < j * w at hx'
        omega
    subst j
    have htd : t ≤ depth := by omega
    have he := port.image t htd
    have ha : root * w + t + d * w = x * w + t := by omega
    rw [ha]
    exact he
  · intro j hj t ht
    apply fixes_below_signature
    rw [port.signature_eq]
    apply old.strict (band_index_lt hj ht)
    exact Nat.le_trans (Nat.mul_le_mul_right _ (by omega : root ≤ x)) hx
  · rw [hp]
    have hind : (x + d) * w = x * w + d * w := Nat.add_mul _ _ _
    rw [hind, ← hcut]
    have he := old.splice_endpoint family owner (root * w + depth) (x * w) (d * w)
      hlr hx hc hleft hright
    change PointChain.splicePoints _ _ _ _ _ _ _ = _ at he
    rw [hcut] at he
    rw [hcut]
    exact he

namespace BandCopyGeometry

theorem copy_port {family : BinaryFamily} {m h x root depth owner : Nat}
    {old : PointChain m ((x + 1) * (h + 1))}
    (g : BandCopyGeometry family m h x root depth owner old)
    {j p k e : Nat} (hj : root ≤ j) (hjx : j < x) (hp : p < j) (hk : k ≤ h)
    (port : BandPort family m old.point (p * (h + 1)) (j * (h + 1)) k e) :
    BandPort family m g.points.point
      (ParentBMS.shift root (x - root) p * (h + 1))
      ((j + (x - root)) * (h + 1)) k ((family m).mul owner e) := by
  apply port.transport owner
  · intro t ht
    unfold ParentBMS.shift
    split
    · rename_i hpr
      rw [g.fixes p hpr t (by omega)]
      apply g.kept
      have := band_index_lt (show p < x by omega) (show t ≤ h by omega)
      omega
    · rename_i hpr
      exact g.image p (by omega) (by omega) t (by omega)
  · intro t ht
    exact g.image j hj hjx t (by omega)

end BandCopyGeometry

#print axioms makeBandCopyGeometry
#print axioms BandCopyGeometry.copy_port

end LaverLowerBounds.FiniteTable
