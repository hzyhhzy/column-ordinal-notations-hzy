import LaverLowerBounds.LiveCover

set_option autoImplicit false

namespace LaverLowerBounds.ParentBMS.LiveCover

variable {f : CopyFrame} {s : SproutState}

theorem target_width (ranks : List Nat) (hl : Leftward (s.full (0 :: ranks)))
    (hn : Nested (s.full (0 :: ranks))) :
    (targetFrame s ranks hl hn).width = s.distance ranks := by
  simp only [targetFrame, CopyFrame.width, SproutState.full, SproutState.base,
    SproutState.distance, List.length_append]
  omega

theorem target_out (ranks : List Nat) (hl : Leftward (s.full (0 :: ranks)))
    (hn : Nested (s.full (0 :: ranks))) :
    (targetFrame s ranks hl hn).out = (s.born ranks).full ranks := by
  have he := s.birth_step ranks
  change expandTail (s.full ranks) s.template 1 = _
  simpa only [SproutState.full_cons, sprout, List.replicate_zero, List.append_nil, expand_append] using he

theorem born_prefix (ranks : List Nat) (hl : Leftward (s.full (0 :: ranks)))
    (hn : Nested (s.full (0 :: ranks))) :
    (s.born ranks).base.IsPrefix (targetFrame s ranks hl hn).out := by
  rw [target_out]
  exact ⟨(s.born ranks).pending ranks, rfl⟩

theorem extended_old (h : LiveCover f s) (ranks : List Nat) {i : Nat} (hi : i < f.stem.length) :
    (h.extended ranks).column i = h.coverage.column i := by
  change (if i < f.stem.length then h.coverage.column i else _) = _
  rw [if_pos hi]

theorem copied_last (h : LiveCover f s) (ranks : List Nat)
    (hl : Leftward (s.full (0 :: ranks))) (hn : Nested (s.full (0 :: ranks))) :
    (h.aligned ranks hl hn).column (f.out.length - 1) = (s.born ranks).base.length - 1 := by
  let pair := h.aligned ranks hl hn
  have hx := f.root_lt
  have hlast : f.stem.length - 1 < f.stem.length := by omega
  have he : f.stem.length - 1 + f.width = f.out.length - 1 := by rw [f.out_length]; omega
  rw [← he, pair.column_new (by omega) hlast]
  change (h.extended ranks).column (f.stem.length - 1) +
    (targetFrame s ranks hl hn).width = _
  rw [h.extended_old ranks hlast, target_width]
  have hnonempty : f.stem ≠ [] := by intro hz; simp [hz] at hx
  rw [h.coverage.last hnonempty]
  have hp : s.block.length ≠ 0 := fun he => s.block_nonempty (List.eq_nil_of_length_eq_zero he)
  simp only [SproutState.born, SproutState.base, SproutState.full, SproutState.distance,
    List.length_append, bornBlock_length]
  omega

theorem copied_bounded (h : LiveCover f s) (ranks : List Nat)
    (hl : Leftward (s.full (0 :: ranks))) (hn : Nested (s.full (0 :: ranks)))
    {i : Nat} (hi : i < f.out.length) :
    (h.aligned ranks hl hn).column i < (s.born ranks).base.length := by
  let pair := h.aligned ranks hl hn
  have hp : s.block.length ≠ 0 := fun he => s.block_nonempty (List.eq_nil_of_length_eq_zero he)
  have hlen : 0 < (s.born ranks).base.length := by
    simp only [SproutState.born, SproutState.base, List.length_append, bornBlock_length]
    omega
  by_cases he : i = f.out.length - 1
  · rw [he, h.copied_last ranks hl hn]
    omega
  · have hh := pair.column_strict (by omega : i < f.out.length - 1) (by omega : f.out.length - 1 < f.out.length)
    have hm := h.copied_last ranks hl hn
    change pair.column (f.out.length - 1) = _ at hm
    change pair.column i < (s.born ranks).base.length
    omega

def birthCoverage (h : LiveCover f s) (ranks : List Nat)
    (hl : Leftward (s.full (0 :: ranks))) (hn : Nested (s.full (0 :: ranks))) :
    Cover f.next.stem (s.born ranks).base where
  column := (h.aligned ranks hl hn).column
  bounded _ hi := h.copied_bounded ranks hl hn hi
  strict _ _ hij hj := (h.aligned ranks hl hn).column_strict hij hj
  edge _ _ _ hp :=
    ((h.aligned ranks hl hn).edge hp).of_prefix (born_prefix ranks hl hn)
      (targetFrame s ranks hl hn).out_leftward
      (h.copied_bounded ranks hl hn (parent_column_lt hp))
  last _ := h.copied_last ranks hl hn

/-- Each actual root event advances the clean source by exactly one complete
copy. All gaps occupied by the pending forest are harmless to the cover. -/
def next (h : LiveCover f s) (ranks : List Nat)
    (hl : Leftward (s.full (0 :: ranks))) (hn : Nested (s.full (0 :: ranks))) :
    LiveCover f.next (s.born ranks) where
  coverage := h.birthCoverage ranks hl hn
  width_eq := by rw [f.next_width]; change f.width = (bornBlock _ _ _ _).length; rw [bornBlock_length]; exact h.width_eq
  block_map i hi := by
    let pair := h.aligned ranks hl hn
    rw [f.next_width] at hi
    change pair.column (f.stem.length + i) = (s.full ranks).length + i
    have hb : f.root + i < f.stem.length := by
      have := f.root_lt
      dsimp [CopyFrame.width] at hi
      omega
    have he : f.root + i + f.width = f.stem.length + i := by
      have := f.root_lt
      dsimp [CopyFrame.width]
      omega
    rw [← he, pair.column_new (by omega) hb]
    change (h.extended ranks).column (f.root + i) + (targetFrame s ranks hl hn).width = _
    rw [h.extended_old ranks hb, h.block_map i hi, target_width]
    simp only [SproutState.full, SproutState.base, SproutState.distance, List.length_append]
    omega
  template_eq := by
    change s.template.map (fun p => p + s.distance ranks) =
      (f.last.map f.move).map (h.aligned ranks hl hn).column
    rw [h.template_eq]
    simp only [List.map_map]
    apply List.map_congr_left
    intro p hp
    dsimp only [Function.comp_def]
    have hi := f.last_upper hp
    rw [(h.aligned ranks hl hn).column_move hi]
    change h.coverage.column p + s.distance ranks =
      (targetFrame s ranks hl hn).move ((h.extended ranks).column p)
    rw [h.extended_old ranks hi]
    have hlower : s.front.length ≤ h.coverage.column p := by
      apply s.lower
      rw [h.template_eq]
      exact List.mem_map.mpr ⟨p, hp, rfl⟩
    rw [(targetFrame s ranks hl hn).move_high hlower, target_width]

#print axioms next

end LaverLowerBounds.ParentBMS.LiveCover
