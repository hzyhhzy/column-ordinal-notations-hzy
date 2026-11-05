import LaverLowerBounds.CompletedCopy

set_option autoImplicit false

namespace LaverLowerBounds.ParentBMS

/-- Extend a cover by a live column whose parents are mapped exactly. Extra
target columns may be inserted immediately before that live column. -/
def Cover.appendMapped {s t : Matrix} (f : Cover s t) (last mappedLast : Column) (extra : Matrix)
    (hs : Leftward s) (hl : ∀ p ∈ last, p < s.length)
    (hmapped : mappedLast = last.map f.column) :
    Cover (s ++ [last]) (t ++ extra ++ [mappedLast]) where
  column i := if i < s.length then f.column i else t.length + extra.length
  bounded i hi := by
    simp only [List.length_append, List.length_singleton] at hi ⊢
    split
    · have := f.bounded i (by assumption)
      omega
    · omega
  strict i j hij hj := by
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hjo : j < s.length
    · rw [if_pos hjo, if_pos (by omega : i < s.length)]
      exact f.strict i j hij hjo
    · have hio : i < s.length := by omega
      rw [if_pos hio, if_neg hjo]
      have := f.bounded i hio
      omega
  edge q p i hp := by
    have hi := parent_column_lt hp
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hold : i < s.length
    · rw [parent_append_left hold] at hp
      have hpi : p < s.length := by
        exact Nat.lt_trans (hs q i p hp) hold
      rw [if_pos hold, if_pos hpi]
      exact (f.edge q p i hp).to_prefix_extension ⟨extra ++ [mappedLast], by simp [List.append_assoc]⟩
    · have he : i = s.length := by omega
      subst i
      rw [parent_last] at hp
      have hpi := hl p (List.mem_of_getElem? hp)
      rw [if_neg (Nat.lt_irrefl _), if_pos hpi]
      apply Ancestor.direct
      have he := parent_last (t ++ extra) mappedLast q
      simpa only [List.length_append, hmapped, List.getElem?_map, hp, Option.map_some] using he
  last _ := by simp

structure LiveCover (f : CopyFrame) (s : SproutState) where
  coverage : Cover f.stem s.base
  width_eq : f.width = s.block.length
  block_map : ∀ i, i < f.width → coverage.column (f.root + i) = s.front.length + i
  template_eq : s.template = f.last.map coverage.column

namespace LiveCover

variable {f : CopyFrame} {s : SproutState}

theorem root_map (h : LiveCover f s) : h.coverage.column f.root = s.front.length := by
  have hw : 0 < f.width := by have := f.root_lt; dsimp [CopyFrame.width]; omega
  simpa using h.block_map 0 hw

def extended (h : LiveCover f s) (ranks : List Nat) :
    Cover (f.stem ++ [f.last]) (s.full ranks ++ [s.template]) :=
  h.coverage.appendMapped f.last s.template (s.pending ranks)
    (leftward_prefix ⟨[f.last], rfl⟩ f.leftward) (fun _ hp => f.last_upper hp) h.template_eq

def targetFrame (s : SproutState) (ranks : List Nat)
    (hl : Leftward (s.full (0 :: ranks))) (hn : Nested (s.full (0 :: ranks))) : CopyFrame where
  stem := s.full ranks
  last := s.template
  root := s.front.length
  control := s.control
  root_lt := by
    have hp : s.block.length ≠ 0 := fun he => s.block_nonempty (List.eq_nil_of_length_eq_zero he)
    simp only [SproutState.full, SproutState.base, List.length_append]
    omega
  leftward := by simpa only [SproutState.full_cons, sprout, List.replicate_zero, List.append_nil] using hl
  nested := by simpa only [SproutState.full_cons, sprout, List.replicate_zero, List.append_nil] using hn

def aligned (h : LiveCover f s) (ranks : List Nat)
    (hl : Leftward (s.full (0 :: ranks))) (hn : Nested (s.full (0 :: ranks))) :
    AlignedCopy f (targetFrame s ranks hl hn) where
  cover := h.extended ranks
  row_eq := by
    change f.last.length - 1 = s.template.length - 1
    rw [h.template_eq, List.length_map]
  root_eq := by
    change s.front.length = (h.extended ranks).column f.root
    -- The explicit extension has the same column map below the old last.
    change s.front.length = if f.root < f.stem.length then h.coverage.column f.root else _
    rw [if_pos f.root_lt, h.root_map]

end LiveCover
end LaverLowerBounds.ParentBMS
