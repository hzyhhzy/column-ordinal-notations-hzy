import LaverLowerBounds.BandCopyGeometry
import LaverLowerBounds.ParentCopyOrigins
import LaverLowerBounds.BandBudget

set_option autoImplicit false

namespace LaverLowerBounds.FiniteTable

open ParentBMS

/-- Concrete weak-band witnesses in an actual finite Laver table. There is no
abstract assumption that copying or termination is valid. -/
structure BandRepresentation (family : BinaryFamily) (m h : Nat) (s : Matrix) where
  shape : Shape h 0 s
  points : PointChain m (s.length * (h + 1))
  ports : ∀ j c r p, s[j]? = some c → c[r]? = some p →
    ∃ owner, BandPort family m points.point (p * (h + 1)) (j * (h + 1)) (r + 1) owner

namespace BandRepresentation

variable {family : BinaryFamily} {m h : Nat}

def endpoint {s : Matrix} (b : BandRepresentation family m h s) : Nat :=
  b.points.point (s.length * (h + 1))

def state {s : Matrix} (b : BandRepresentation family m h s) (hh : 3 ≤ h) : BandBudget.State where
  endpoint := b.endpoint
  columns := s.length
  ready := ready h s
  room := by
    have hi := b.points.index_le (Nat.le_refl _)
    have hm := Nat.mul_le_mul_left s.length (show 2 ≤ h + 1 by omega)
    rw [Nat.mul_comm s.length 2] at hm
    exact Nat.le_trans hm hi

theorem endpoint_below {s : Matrix} (b : BandRepresentation family m h s) : b.endpoint < m :=
  b.points.bounded

theorem positive_copy {stem : Matrix} {last : Column} {root : Nat}
    (b : BandRepresentation family m h (stem ++ [last])) (he : last.getLast? = some root) :
    ∃ next : BandRepresentation family m h (expandTail stem last 1),
      next.endpoint = b.points.point (stem.length * (h + 1) + last.length + 1) := by
  obtain ⟨hlh, hlp⟩ := shape_last b.shape
  have hr : root < stem.length := by simpa using hlp root (List.mem_of_getLast? he)
  have hlpos : 0 < last.length := by
    apply List.length_pos_iff.mpr
    intro hz
    simp [hz] at he
  have hrow : last[last.length - 1]? = some root := by rw [← List.getLast?_eq_getElem?]; exact he
  obtain ⟨owner, active⟩ := b.ports stem.length last (last.length - 1) root (by simp) hrow
  have hdepth : last.length - 1 + 1 = last.length := by omega
  rw [hdepth] at active
  let old := b.points.reindex ((stem.length + 1) * (h + 1)) (by simp)
  let g := makeBandCopyGeometry family old hr hlh active
  have hlen : (expandTail stem last 1).length = stem.length + (stem.length - root) := by
    rw [expandTail_one_positive he]
    simp only [List.length_append, copy_length]
  let points := g.points.reindex ((expandTail stem last 1).length * (h + 1)) (by rw [hlen])
  have hports : ∀ j c r p, (expandTail stem last 1)[j]? = some c → c[r]? = some p →
      ∃ e, BandPort family m points.point (p * (h + 1)) (j * (h + 1)) (r + 1) e := by
    intro j c r p hj hp
    have origin := expandTail_port_origin b.shape he hj hp
    cases origin with
    | kept col hjx hcol hparent =>
        have hcol' : (stem ++ [last])[j]? = some col := by
          rw [List.getElem?_append_left hjx]; exact hcol
        obtain ⟨hc, hpar⟩ := b.shape j col hcol'
        have hrowlt := (List.getElem?_eq_some_iff.mp hparent).1
        have hpj : p < j := by simpa using hpar p (List.mem_of_getElem? hparent)
        obtain ⟨e, port⟩ := b.ports j col r p hcol' hparent
        refine ⟨e, port.congrPoints ?_ ?_⟩
        · intro t ht
          apply g.kept
          have := band_index_lt (show p < stem.length by omega) (show t ≤ h by omega)
          omega
        · intro t ht
          apply g.kept
          have := band_index_le hjx (show t ≤ h + 1 by omega)
          omega
    | low hjx hrlo hparent =>
        subst j
        have hpx : p < stem.length := by simpa using hlp p (List.mem_of_getElem? hparent)
        obtain ⟨e, port⟩ := b.ports stem.length last r p (by simp) hparent
        refine ⟨e, port.congrPoints ?_ ?_⟩
        · intro t ht
          apply g.kept
          have := band_index_lt hpx (show t ≤ h by omega)
          omega
        · intro t ht
          exact g.kept _ (by omega)
    | copied q col oldParent hroot hqx hcol hparent hjq hpp =>
        have hcol' : (stem ++ [last])[q]? = some col := by
          rw [List.getElem?_append_left hqx]; exact hcol
        obtain ⟨hc, hpar⟩ := b.shape q col hcol'
        have hrowlt := (List.getElem?_eq_some_iff.mp hparent).1
        have hpq : oldParent < q := by simpa using hpar oldParent (List.mem_of_getElem? hparent)
        obtain ⟨e, port⟩ := b.ports q col r oldParent hcol' hparent
        rw [hjq, hpp]
        exact ⟨(family m).mul owner e, g.copy_port hroot hqx hpq (by omega) port⟩
  let next : BandRepresentation family m h (expandTail stem last 1) := {
    shape := expandTail_one_shape b.shape
    points := points
    ports := hports }
  refine ⟨next, ?_⟩
  change g.points.point ((expandTail stem last 1).length * (h + 1)) = _
  rw [hlen]
  exact g.endpoint

theorem delete_last {stem : Matrix} (b : BandRepresentation family m h (stem ++ [[]])) :
    ∃ next : BandRepresentation family m h stem,
      next.endpoint + (h + 1) ≤ b.endpoint := by
  let points := b.points.truncate (stem.length * (h + 1)) (by
    simp only [List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul]
    omega)
  let next : BandRepresentation family m h stem := {
    shape := shape_stem b.shape
    points := points
    ports := by
      intro j c r p hj hp
      have hit := (List.getElem?_eq_some_iff.mp hj).1
      exact b.ports j c r p (by rw [List.getElem?_append_left hit]; exact hj) hp }
  refine ⟨next, ?_⟩
  have hb := b.points.distance (show stem.length * (h + 1) ≤ (stem ++ [[]]).length * (h + 1) by
    simp only [List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul]; omega)
    (Nat.le_refl _)
  change b.points.point (stem.length * (h + 1)) + (h + 1) ≤ b.endpoint
  simpa only [List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul,
    Nat.add_sub_cancel_left, endpoint] using hb

#print axioms positive_copy
#print axioms delete_last

end BandRepresentation
end LaverLowerBounds.FiniteTable
