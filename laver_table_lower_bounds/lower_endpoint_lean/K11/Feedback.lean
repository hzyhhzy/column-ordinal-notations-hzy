import K11.Entrance
import LaverLowerBounds.StandardLine
import LaverLowerBounds.TripleCount

set_option autoImplicit false
namespace LaverLowerBounds.FiniteTable.K11.Entrance
variable {family : BinaryFamily} {m : Nat}

theorem feedback (e : Entrance family m) {Q a b h : Nat}
    (hQ : signature m Q = e.bg.k) (hQa : act family m Q e.bg.k = a)
    (hQb : act family m Q a = b) (hz : e.zeta ≤ a) (hb : b < m)
    (old : OwnedFan family m h) (hh : 3 ≤ h) (hc : old.fan.endpoint < a)
    (hm : 2 ≤ Nat.log2 (ParentBMS.tripleCount h)) :
    ∃ next : OwnedFan family m (Nat.log2 (ParentBMS.tripleCount h)), next.fan.endpoint < b := by
  have hk := e.bg.k_lower
  have q0 : act family m Q 0 = 0 := fixes_below_signature family m Q 0 (by omega)
  have q1 : act family m Q 1 = 1 := fixes_below_signature family m Q 1 (by omega)
  let P := (family m).mul Q e.f
  let c := act family m Q e.eta
  let d := act family m Q e.zeta
  have db : d ≤ b := by
    have he := act_mono family m Q hz
    rwa [hQb] at he
  have cd : c < d := act_strict_below_cap family m Q _ _ e.eta_zeta (by omega)
  have xc : act family m Q e.bg.mu < c := act_strict_below_cap family m Q _ _ e.xi_eta (by omega)
  have p0 : act family m P 0 = a := (application_at family m Q e.f q0 e.f0).trans hQa
  have p1 : act family m P 1 = c := application_at family m Q e.f q1 e.f1
  have pa : act family m P a = d := application_at family m Q e.f hQa e.fk
  let D := ParentBMS.tripleCount h
  let l := Nat.log2 D
  have budget : D < old.fan.endpoint := old.fan.tripleCount_lt hh
  have cap : old.fan.endpoint < m := old.fan.chain.bounded
  have positive : D ≠ 0 := by have := ParentBMS.tripleCount_ge_three h; omega
  have power : 2 ^ l ≤ D := (Nat.le_log2 positive).mp (Nat.le_refl _)
  have small : 2 ^ l < a := by omega
  have out : act family m P (2 ^ l) < d := by
    have he := act_strict_below_cap family m P _ a small (by rw [pa]; omega)
    rwa [pa] at he
  have std := standard_line family m l (by omega : 2 ^ l < m)
  have line := std.map P (by omega : act family m P (2 ^ l) < m)
  rw [p0, p1] at line
  let bg := e.bg.map Q q0 q1 (by omega : act family m Q e.bg.mu < m)
  have line' : Lined family m bg.k l c (act family m P (2 ^ l)) := by
    change Lined family m (act family m Q e.bg.k) l c _
    rw [hQa]; exact line
  obtain ⟨fan, hfan⟩ := bg.line_to_fan line' hm (Nat.le_of_lt xc)
  exact ⟨fan, Nat.lt_of_lt_of_le (Nat.lt_trans hfan out) db⟩

#print axioms feedback
end LaverLowerBounds.FiniteTable.K11.Entrance
