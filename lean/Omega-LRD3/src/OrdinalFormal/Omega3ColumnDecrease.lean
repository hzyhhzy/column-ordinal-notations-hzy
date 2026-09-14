import OrdinalFormal.Omega3Comparison
import OrdinalFormal.Omega3RowDomain
import OrdinalFormal.GeneratedColumnDecrease
import OrdinalFormal.Omega3Validity

/-!
# Actual Omega-LRD3 standard-column decrease

Structural-depth induction supplies the generated package's lower rows.
This is a strict comparison theorem, not a well-foundedness assumption or
conclusion. In particular no accessibility of any seed is used.
-/

namespace OrdinalFormal.Omega3ColumnDecrease
open Columns OmegaLRD3 GenericSortedColumns
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 4096

theorem toGraph_ne_nil {a : Diagram} (ha : a ≠ .nil) : a.toGraph ≠ [] := by
  intro h
  have he := congrArg Diagram.ofGraph h
  rw [Diagram.ofGraph_toGraph] at he
  exact ha he

theorem nil_lt {a : Diagram} (ha : a ≠ .nil) : cmp .nil a = .lt := by
  rw [Omega3Comparison.cmp_eq_graphCompare]
  have hn := toGraph_ne_nil ha
  cases hg : a.toGraph with
  | nil => exact False.elim (hn hg)
  | cons c cs => rfl

theorem seed_canonical (d : Nat) : Canonical cmp (seed d).toGraph := by
  induction d with
  | zero => simp [seed, Diagram.toGraph, Canonical]
  | succ d ih =>
    intro c hc
    simp only [seed, Diagram.toGraph, Edges.toList_ofList,
      List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact ih c hc
    · by_cases hd : d = 0
      · simp only [hd, ↓reduceIte]
        exact ⟨.nil, by simp⟩
      · simp only [hd, ↓reduceIte]
        exact normalized_column_canonical cmp Omega3Comparison.compareLaws _

theorem fs_canonical {a : Diagram} (ha : Canonical cmp a.toGraph) (n : Nat) :
    Canonical cmp (fs a n).toGraph := by
  rw [fs_toGraph]
  exact expand_canonical cmp Omega3Comparison.compareLaws rowPackage ha n

theorem standard_canonical {a : Diagram} (ha : Standard (.finite a)) :
    Canonical cmp a.toGraph := by
  obtain ⟨d, hd⟩ := (standard_finite_iff a).mp ha
  exact reach_preserves .nil fs (fun a => Canonical cmp a.toGraph)
    (fun _ h n => fs_canonical h n) hd (seed_canonical d)

theorem standard_rootClosed {a : Diagram} (ha : Standard (.finite a)) :
    RootClosed a.toGraph := canonical_rootClosed cmp (standard_canonical ha)

/-- A controller-local package is extensionally sufficient for this one
actual expansion. Its lower-row proof is obtained from smaller syntax depth. -/
theorem expand_lt_of_control_package {a : Diagram}
    (ha : Standard (.finite a)) (hn : a ≠ .nil)
    (hPackage : ∀ e, control cmp (a.toGraph.getLast?.getD []) = some e →
      ∀ b low, low ∈ rowPackage e.row b → cmp low e.row = .lt) (n : Nat) :
    cmp (fs a n) a = .lt := by
  rw [Omega3Comparison.cmp_eq_graphCompare, fs_toGraph]
  cases he : control cmp (a.toGraph.getLast?.getD []) with
  | none =>
    have hs : expand cmp rowPackage a.toGraph n = expand cmp rowPackage a.toGraph 0 := by
      simp [expand, he]
    rw [hs]
    exact GeneratedColumnDecrease.expand_zero_lt cmp Omega3Comparison.compareLaws rowPackage
      a.toGraph (toGraph_ne_nil hn)
  | some e =>
    let localPackage : Package Diagram := fun high b =>
      if high = e.row then rowPackage high b else []
    have hp : ∀ high b low, low ∈ localPackage high b → cmp low high = .lt := by
      intro high b low hl
      dsimp [localPackage] at hl
      split at hl
      · rename_i hh
        subst high
        exact hPackage e he b low hl
      · simp at hl
    have hs : expand cmp rowPackage a.toGraph n = expand cmp localPackage a.toGraph n := by
      apply expand_package_congr
      intro e' he' b
      have heq : e' = e := Option.some.inj (he'.symm.trans he)
      subst e'
      simp [localPackage]
    rw [hs]
    exact GeneratedColumnDecrease.expand_lt cmp Omega3Comparison.compareLaws localPackage hp
      (Omega3Validity.standard_valid ha) (standard_canonical ha)
      (toGraph_ne_nil hn) n

/-- Every actual standard nonzero diagram strictly decreases at every index.
The induction is on finite syntax depth, not on the order being proved. -/
theorem fs_lt {a : Diagram} (ha : Standard (.finite a)) (hn : a ≠ .nil) (n : Nat) :
    cmp (fs a n) a = .lt := by
  have go : ∀ d, ∀ a : Diagram, a.depth = d → Standard (.finite a) → a ≠ .nil →
      ∀ n, cmp (fs a n) a = .lt := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro a had ha hn n
      apply expand_lt_of_control_package ha hn ?_ n
      intro e he b low hl
      have hrow : Standard (.finite e.row) :=
        RowInvariant.last_rows (standard_rows ha) e (ExpansionValidity.control_mem cmp he)
      have hdepth : e.row.depth < d := had ▸ Diagram.control_row_depth_lt he
      unfold rowPackage at hl
      split at hl
      · simp at hl
      · rename_i hfinite
        have hne : e.row ≠ .nil := by
          intro hh
          simp [hh, Diagram.isFinite, Diagram.toGraph] at hfinite
        rcases List.mem_cons.mp hl with h | h
        · subst low
          exact nil_lt hne
        · obtain ⟨t, _, rfl⟩ := List.mem_map.mp h
          exact ih e.row.depth hdepth e.row rfl hrow hne t
  exact go a.depth a rfl ha hn n

theorem rowPackage_lt {row : Diagram} (hr : Standard (.finite row))
    {b : Nat} {low : Diagram} (hl : low ∈ rowPackage row b) : cmp low row = .lt := by
  unfold rowPackage at hl
  split at hl
  · simp at hl
  · rename_i hfinite
    have hn : row ≠ .nil := by
      intro h
      simp [h, Diagram.isFinite, Diagram.toGraph] at hfinite
    rcases List.mem_cons.mp hl with h | h
    · subst low
      exact nil_lt hn
    · obtain ⟨t, _, rfl⟩ := List.mem_map.mp h
      exact fs_lt hr hn t

theorem standard_step_lt {a b : Diagram} (ha : Standard (.finite a)) (h : Step b a) :
    cmp b a = .lt := by
  obtain ⟨hn, n, rfl⟩ := h
  exact fs_lt ha hn n

#print axioms standard_canonical
#print axioms fs_lt
#print axioms rowPackage_lt

end OrdinalFormal.Omega3ColumnDecrease
