import OrdinalFormal.ExpansionValidity
import OrdinalFormal.ColumnRepresentation

/-!
Actual finite-stage geometry of the executable expansion. In particular every
new edge is classified from the real normalized block, rather than assuming an
old/copy/seam decomposition as an interface hypothesis.
-/

namespace OrdinalFormal.ActualBlockGeometry
open Columns ExpansionValidity
set_option autoImplicit false
set_option maxHeartbeats 700000
universe u
variable {Row : Type u}

def stage (cmp : Row → Row → Ordering) (package : Package Row)
    (g : Graph Row) (e : Entry Row) (b : Nat) : Graph Row :=
  g.take (g.length - 1) ++ (List.range b).flatMap (block cmp package g e)

theorem stage_length (cmp : Row → Row → Ordering) (package : Package Row)
    (g : Graph Row) (e : Entry Row) (b : Nat) :
    (stage cmp package g e b).length = g.length - 1 + b * (g.length - 1 - e.parent) := by
  simp only [stage, List.length_append, List.length_take, blocks_length,
    Nat.min_eq_left (Nat.sub_le g.length 1)]

theorem stage_succ (cmp : Row → Row → Ordering) (package : Package Row)
    (g : Graph Row) (e : Entry Row) (b : Nat) :
    stage cmp package g e (b + 1) = stage cmp package g e b ++ block cmp package g e b := by
  simp [stage, List.range_succ, List.flatMap_append, List.append_assoc]

theorem expand_eq_stage (cmp : Row → Row → Ordering) (package : Package Row)
    (g : Graph Row) {e : Entry Row}
    (he : Columns.control cmp (g.getLast?.getD []) = some e) (n : Nat) :
    expand cmp package g n = stage cmp package g e n := by
  simp [expand, he, stage]

theorem stage_valid (cmp : Row → Row → Ordering) (package : Package Row)
    {g : Graph Row} (hg : Valid g) (e : Entry Row)
    (he : e.parent < g.length - 1) (b : Nat) : Valid (stage cmp package g e b) := by
  apply (validFrom_zero_iff _).mp
  apply validFrom_append _ _ _ ((validFrom_zero_iff _).mpr (valid_take hg _))
  simp only [Nat.zero_add, List.length_take, Nat.min_eq_left (Nat.sub_le g.length 1)]
  exact blocks_validFrom cmp package g e b hg he

def Weakened (a s : Entry Row) : Prop :=
  a.row = s.row ∧ a.parent = s.parent ∧ a.root ≤ s.root

/-- The first block index carries the seam; every other index is only a copy.
Normalization can lower roots but cannot invent a parent or row. -/
theorem block_entry_origin (cmp : Row → Row → Ordering) (package : Package Row)
    (g : Graph Row) (e : Entry Row) (b i : Nat)
    (hi : i < g.length - 1 - e.parent) {a : Entry Row}
    (ha : a ∈ (block cmp package g e b)[i]?.getD []) :
    (∃ s ∈ g[e.parent + i]?.getD [],
      Weakened a (moveEntry e.parent (g.length - 1 - e.parent) (b + 1) s)) ∨
    (i = 0 ∧ ∃ s ∈ ordinarySeam cmp (g.getLast?.getD []) e (g.length - 1 - e.parent) b ++
      generatedSeam package e (g.length - 1 - e.parent) b, Weakened a s) := by
  simp only [block, List.getElem?_map, List.getElem?_range, hi,
    Option.map_some, Option.getD_some] at ha
  obtain ⟨s, hs, hr, hp, hq⟩ := ColumnRepresentation.mem_normalizeColumn_source cmp ha
  rcases List.mem_append.mp hs with hs | hs
  · obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hs
    exact Or.inl ⟨old, hold, hr, hp, hq⟩
  · split at hs
    · rename_i hi0
      exact Or.inr ⟨hi0, s, hs, hr, hp, hq⟩
    · simp at hs

/-- Concrete global old/copy/seam classification for adding one more block.
The copy source and target child coordinates are included explicitly. -/
theorem stage_step_origin (cmp : Row → Row → Ordering) (package : Package Row)
    (g : Graph Row) (e : Entry Row) (b j : Nat) {a : Entry Row}
    (ha : a ∈ (stage cmp package g e (b + 1))[j]?.getD []) :
    (a ∈ (stage cmp package g e b)[j]?.getD []) ∨
    (∃ i, i < g.length - 1 - e.parent ∧
      j = g.length - 1 + b * (g.length - 1 - e.parent) + i ∧
      ((∃ s ∈ g[e.parent + i]?.getD [],
        Weakened a (moveEntry e.parent (g.length - 1 - e.parent) (b + 1) s)) ∨
       (i = 0 ∧ ∃ s ∈ ordinarySeam cmp (g.getLast?.getD []) e (g.length - 1 - e.parent) b ++
         generatedSeam package e (g.length - 1 - e.parent) b, Weakened a s))) := by
  rw [stage_succ, List.getElem?_append] at ha
  split at ha
  · exact Or.inl ha
  · rename_i hj
    have hi := ColumnRepresentation.index_lt_of_entry_mem ha
    rw [block_length, stage_length] at hi
    rw [stage_length] at ha hj
    refine Or.inr ⟨j - (g.length - 1 + b * (g.length - 1 - e.parent)), hi, ?_, ?_⟩
    · omega
    · exact block_entry_origin cmp package g e b _ hi ha

end OrdinalFormal.ActualBlockGeometry
