import OrdinalFormal.Domains
import OrdinalFormal.ExpansionValidity
import OrdinalFormal.RPDGeometry

/-!
Coordinate validity of every graph in the actual generated standard domains.
Release copy: only the generic, RPD and LRD declarations are retained.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace OrdinalFormal.StandardValidity
open Columns ExpansionValidity

universe u
variable {Row : Type u}

theorem valid_nil : Valid ([] : Graph Row) := by
  intro j e he
  simp at he

theorem valid_append_column {g : Graph Row} (hg : Valid g) (c : Column Row)
    (hc : ∀ e ∈ c, e.root ≤ e.parent ∧ e.parent < g.length) :
    Valid (g ++ [c]) := by
  apply (validFrom_zero_iff _).mp
  apply validFrom_append _ _ _ ((validFrom_zero_iff _).mpr hg)
  intro i e he
  cases i with
  | zero => simpa using hc e (by simpa using he)
  | succ i => simp at he

theorem valid_append_empty {g : Graph Row} (hg : Valid g) :
    Valid (g ++ [[]]) :=
  valid_append_column hg [] (by simp)

theorem rpd_seed_valid (n : Nat) : Valid (RPD.seed n) := by
  rw [RPDGeometry.seed_eq]
  change Valid ([[]] ++ [RPDGeometry.star (n + 1)])
  apply valid_append_column (valid_append_empty (Row := Nat) valid_nil)
  intro e he
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp he
  simp [RPDGeometry.starEntry]

theorem rpd_fs_valid {g : RPD.Diagram} (hg : Valid g) (n : Nat) :
    Valid (RPD.fs g n) := expand_valid _ _ g n hg

theorem rpd_standard_valid {g : RPD.Diagram} (h : RPD.Standard (.finite g)) :
    Valid g := by
  obtain ⟨n, hn⟩ := (RPD.standard_finite_iff g).mp h
  exact reach_preserves [] RPD.fs Valid (fun _ hg n => rpd_fs_valid hg n)
    hn (rpd_seed_valid n)

theorem lrd_seed_valid : Valid LRD.seed := by
  change Valid ([[]] ++ [[⟨LRD.Row.limit, 0, 0⟩]])
  apply valid_append_column (valid_append_empty (Row := LRD.Row) valid_nil)
  intro e he
  simp only [List.mem_singleton] at he
  subst e
  decide

theorem lrd_fs_valid {g : LRD.Diagram} (hg : Valid g) (n : Nat) :
    Valid (LRD.fs g n) := expand_valid _ _ g n hg

theorem lrd_standard_valid {g : LRD.Diagram} (h : LRD.Standard g) : Valid g := by
  induction h with
  | seed => exact lrd_seed_valid
  | child _ n ih => exact lrd_fs_valid ih n

end OrdinalFormal.StandardValidity
