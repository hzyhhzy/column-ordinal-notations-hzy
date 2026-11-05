import LaverLowerBounds.DiagonalCover

set_option autoImplicit false

namespace LaverLowerBounds.ParentBMS

def loweringLast (h w : Nat) : Column := List.replicate h (w - 1) ++ [0]
def loweringTable (h w : Nat) : Matrix := diagonal (h + 1) w ++ [loweringLast h w]

theorem loweringLast_parent {h w q p : Nat} :
    (loweringLast h w)[q]? = some p ↔ (q < h ∧ p = w - 1) ∨ (q = h ∧ p = 0) := by
  by_cases hq : q < h
  · rw [loweringLast, List.getElem?_append_left (by simpa using hq), List.getElem?_replicate_of_lt hq]
    simp only [Option.some.injEq]
    constructor
    · intro he; exact Or.inl ⟨hq, he.symm⟩
    · rintro (⟨_, he⟩ | ⟨he, _⟩)
      · exact he.symm
      · omega
  · by_cases he : q = h
    · subst q
      simp [loweringLast, eq_comm]
    · have hb : (loweringLast h w).length ≤ q := by simp [loweringLast]; omega
      rw [List.getElem?_eq_none hb]
      simp [hq, he]

theorem lowering_shape {h w : Nat} (hw : 0 < w) : Shape (h + 1) 0 (loweringTable h w) := by
  apply shape_append (diagonal_shape (h + 1) w)
  intro i c hc
  have hi : i = 0 := by have := (List.getElem?_eq_some_iff.mp hc).1; simp at this; omega
  subst i
  simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
  rw [← hc]
  constructor
  · simp [loweringLast]
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · have he := List.eq_of_mem_replicate hp
      simp only [diagonal_length]
      omega
    · have he : p = 0 := by simpa using hp
      simp only [diagonal_length]
      omega

theorem lowering_nested {h w : Nat} (hw : 0 < w) : Nested (loweringTable h w) := by
  have hlast (r : Nat) : parent (loweringTable h w) r w = (loweringLast h w)[r]? := by
    simpa only [diagonal_length, loweringTable] using parent_last (diagonal (h + 1) w) (loweringLast h w) r
  intro q i p hp
  have hi := parent_column_lt hp
  change i < (diagonal (h + 1) w ++ [loweringLast h w]).length at hi
  simp only [List.length_append, List.length_singleton, diagonal_length] at hi
  by_cases hold : i < w
  · have he : parent (diagonal (h + 1) w) (q + 1) i = some p := by
      rw [loweringTable, parent_append_left (by simpa using hold : i < (diagonal (h + 1) w).length)] at hp
      exact hp
    exact (diagonal_nested (h + 1) w q i p he).to_prefix_extension ⟨[loweringLast h w], rfl⟩
  · have hilast : i = w := by omega
    subst i
    have he : (loweringLast h w)[q + 1]? = some p := by
      rw [hlast] at hp
      exact hp
    rcases loweringLast_parent.mp he with ⟨hqh, hparent⟩ | ⟨hqh, hparent⟩
    · apply Ancestor.direct
      rw [hlast]
      exact loweringLast_parent.mpr (Or.inl ⟨by omega, hparent⟩)
    · subst p
      have he : parent (loweringTable h w) q w = some (w - 1) := by
        rw [hlast]
        exact loweringLast_parent.mpr (Or.inl ⟨by omega, rfl⟩)
      by_cases hone : w = 1
      · simpa only [hone] using Ancestor.direct he
      · have ha := diagonal_ancestor (h := h + 1) (m := w) (q := q) (p := 0) (i := w - 1)
          (by omega) (by omega) (by omega)
        exact .step he (ha.to_prefix_extension ⟨[loweringLast h w], rfl⟩)

def loweringFrame (h w : Nat) (hw : 0 < w) : CopyFrame where
  stem := diagonal (h + 1) w
  last := loweringLast h w
  root := 0
  control := by simp [loweringLast]
  root_lt := by simpa using hw
  leftward := leftward_of_shape (lowering_shape hw)
  nested := lowering_nested hw

@[simp] theorem lowering_row (h w : Nat) (hw : 0 < w) : (loweringFrame h w hw).row = h := by
  simp [CopyFrame.row, loweringFrame, loweringLast]

@[simp] theorem lowering_width (h w : Nat) (hw : 0 < w) : (loweringFrame h w hw).width = w := by
  simp [CopyFrame.width, loweringFrame]

theorem lowering_out_parent {h w q i : Nat} (hw : 0 < w) (hq : q < h)
    (hpos : 0 < i) (hi : i < 2 * w) :
    parent (loweringFrame h w hw).out q i = some (i - 1) := by
  let f := loweringFrame h w hw
  by_cases hold : i < w
  · rw [f.parent_old (by simpa [f, loweringFrame] using hold)]
    exact diagonal_parent hold hpos (by omega)
  · by_cases hhead : i = w
    · subst i
      have he := f.parent_low_head (q := q) (by simpa [f] using hq)
      change parent f.out q w = some (w - 1)
      simpa only [f, loweringFrame, diagonal_length] using
        he.trans (loweringLast_parent.mpr (Or.inl ⟨hq, rfl⟩))
    · have hroot : f.root < i - w := by dsimp [f, loweringFrame]; omega
      have hib : i - w < f.stem.length := by simp only [f, loweringFrame, diagonal_length]; omega
      have he := f.parent_copied (q := q) hroot hib
      have hindex : i - w + f.width = i := by simp only [f, lowering_width]; omega
      rw [hindex] at he
      have hp : parent f.stem q (i - w) = some (i - w - 1) :=
        diagonal_parent (by omega) (by omega) (by omega)
      rw [hp, Option.map_some] at he
      have hm : f.move (i - w - 1) = i - 1 := by
        simp only [CopyFrame.move, f, loweringFrame, shift, Nat.not_lt_zero, ↓reduceIte]
        simp only [CopyFrame.width, diagonal_length, Nat.sub_zero]
        omega
      rwa [hm] at he

def lowering_cover (h w : Nat) (hw : 0 < w) :
    Cover (diagonal h (2 * w)) (loweringFrame h w hw).out where
  column := id
  bounded i hi := by
    rw [CopyFrame.out_length, lowering_width]
    simpa only [loweringFrame, diagonal_length, id_eq, Nat.two_mul] using hi
  strict _ _ hij _ := hij
  edge q p i hp := by
    obtain ⟨hi, hpos, hq, rfl⟩ := diagonal_parent_iff.mp hp
    exact .direct (lowering_out_parent hw hq hpos hi)
  last _ := by
    rw [CopyFrame.out_length, lowering_width]
    simp only [id_eq, loweringFrame, diagonal_length, Nat.two_mul]

/-- One row can be exchanged for nearly twice the width. The preparation
phase is supplied by the general cover simulation, not by a separate loop. -/
theorem row_width_trade {h w n : Nat} (hw : 0 < w)
    (ht : PrefixDescent.Stops (fun a => expand a 1) (diagonal (h + 1) (w + 1)) n) :
    ∃ k, PrefixDescent.Stops (fun a => expand a 1) (diagonal h (2 * w)) k ∧ k < n := by
  let f := loweringFrame h w hw
  let initial : Cover (loweringTable h w) (diagonal (h + 1) (w + 1)) :=
    diagonal_cover (lowering_shape hw) (by simp [loweringTable])
  obtain ⟨j, hj, hjn⟩ := initial.stops ht f.leftward f.nested
    (diagonal_leftward _ _) (diagonal_nested _ _)
  obtain ⟨j', hnext, hjeq⟩ := PrefixDescent.stops_next hj (by simp [loweringTable])
  have hnext' : PrefixDescent.Stops (fun a => expand a 1) f.out j' := by
    rw [loweringTable, expand_append] at hnext
    exact hnext
  obtain ⟨k, hk, hkj⟩ := (lowering_cover h w hw).stops hnext'
    (diagonal_leftward _ _) (diagonal_nested _ _) f.out_leftward f.out_nested
  exact ⟨k, hk, by omega⟩

#print axioms row_width_trade

end LaverLowerBounds.ParentBMS
