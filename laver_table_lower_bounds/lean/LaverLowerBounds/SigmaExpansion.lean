import LaverLowerBounds.RepeatedCopies

set_option autoImplicit false

namespace LaverLowerBounds.ParentBMS

def diagonalTag (offset : Nat) (s : Matrix) : Matrix :=
  s.mapIdx (fun i c => (offset + i) :: c.map Nat.succ)

theorem sigma_append (s t : Matrix) : sigma (s ++ t) = sigma s ++ diagonalTag s.length t := by
  simp [sigma, diagonalTag, List.mapIdx_append, Nat.add_comm]

theorem sigma_append_last (s : Matrix) (c : Column) :
    sigma (s ++ [c]) = sigma s ++ [s.length :: c.map Nat.succ] := by
  simp [sigma_append, diagonalTag]

theorem sigma_lookup {s : Matrix} {i : Nat} (hi : i < s.length) :
    (sigma s)[i + 1]?.getD [] = i :: (s[i]?.getD []).map Nat.succ := by
  simp [sigma, List.getElem?_eq_getElem hi]

namespace CopyFrame

def sigmaFrame (f : CopyFrame) : CopyFrame where
  stem := sigma f.stem
  last := f.stem.length :: f.last.map Nat.succ
  root := f.root + 1
  control := by
    simp [List.getLast?_cons, List.getLast?_map, f.control]
  root_lt := by rw [sigma_length]; have := f.root_lt; omega
  leftward := by
    rw [← sigma_append_last]
    exact sigma_leftward f.leftward
  nested := by
    rw [← sigma_append_last]
    exact sigma_nested f.leftward f.nested

theorem sigmaFrame_width (f : CopyFrame) : f.sigmaFrame.width = f.width := by
  simp only [sigmaFrame, width, sigma_length]
  omega

theorem sigmaFrame_row (f : CopyFrame) : f.sigmaFrame.row = f.row + 1 := by
  have hpos : 0 < f.last.length := by
    have hc := f.control
    cases he : f.last with
    | nil => simp [he] at hc
    | cons _ _ => simp
  simp only [sigmaFrame, row, List.length_cons, List.length_map]
  omega

theorem sigma_copy_one (f : CopyFrame) :
    copy f.sigmaFrame.stem f.sigmaFrame.last f.sigmaFrame.row f.sigmaFrame.root f.sigmaFrame.width 0 =
      diagonalTag f.stem.length (copy f.stem f.last f.row f.root f.width 0) := by
  rw [f.sigmaFrame_width, f.sigmaFrame_row]
  change copy (sigma f.stem) (f.stem.length :: f.last.map Nat.succ) (f.row + 1) (f.root + 1) f.width 0 = _
  apply List.ext_getElem?
  intro i
  by_cases hi : i < f.width
  · rw [copy_zero, List.getElem?_map, List.getElem?_range hi]
    simp only [diagonalTag, List.getElem?_mapIdx]
    rw [copy_zero, List.getElem?_map, List.getElem?_range hi]
    simp only [Option.map_some]
    by_cases hz : i = 0
    · rw [if_pos hz, if_pos hz, sigma_lookup f.root_lt]
      subst i
      simp only [List.take_succ_cons, ← List.map_take, List.drop_succ_cons, ← List.map_drop,
        List.cons_append, List.map_append, Nat.add_zero]
    · rw [if_neg hz, if_neg hz]
      have hib : f.root + i < f.stem.length := by
        have := f.root_lt
        dsimp [width] at hi
        omega
      have he : f.root + 1 + i = f.root + i + 1 := by omega
      rw [he, sigma_lookup hib]
      simp only [List.map_cons, List.map_map]
      have hroot : f.root + 1 ≤ f.root + i := by omega
      have hlow : shift (f.root + 1) f.width (f.root + i) = f.stem.length + i := by
        simp only [shift, if_neg (by omega : ¬ f.root + i < f.root + 1)]
        have := f.root_add_width
        omega
      rw [hlow]
      congr 1
      apply congrArg (List.cons (f.stem.length + i))
      apply congrArg (fun g => (f.stem[f.root + i]?.getD []).map g)
      funext p
      exact (succ_shift f.root f.width p).symm
  · rw [List.getElem?_eq_none (by rw [copy_length]; omega),
      List.getElem?_eq_none (by simp only [diagonalTag, List.length_mapIdx, copy_length]; omega)]

theorem sigma_out (f : CopyFrame) : f.sigmaFrame.out = sigma f.out := by
  rw [f.sigmaFrame.out_eq, f.sigma_copy_one, f.out_eq, sigma_append]
  rfl

theorem ext_fields {f g : CopyFrame} (hs : f.stem = g.stem) (hl : f.last = g.last) (hr : f.root = g.root) : f = g := by
  cases f
  cases g
  simp_all

theorem sigma_next (f : CopyFrame) : f.sigmaFrame.next = f.next.sigmaFrame := by
  apply ext_fields
  · exact f.sigma_out
  · change (f.stem.length :: f.last.map Nat.succ).map f.sigmaFrame.move =
      f.out.length :: (f.last.map f.move).map Nat.succ
    simp only [List.map_cons, List.map_map]
    have hhead : f.sigmaFrame.move f.stem.length = f.out.length := by
      rw [f.sigmaFrame.move_high (by change f.root + 1 ≤ f.stem.length; have := f.root_lt; omega), f.sigmaFrame_width,
        f.out_length]
    rw [hhead]
    congr 1
    apply congrArg (fun g => f.last.map g)
    funext p
    change shift (f.root + 1) f.sigmaFrame.width (Nat.succ p) = Nat.succ (shift f.root f.width p)
    rw [f.sigmaFrame_width]
    exact (succ_shift f.root f.width p).symm
  · change (sigma f.stem).length = f.stem.length + 1
    exact sigma_length _

theorem sigma_advance (f : CopyFrame) (n : Nat) :
    f.sigmaFrame.advance n = (f.advance n).sigmaFrame := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
      change f.sigmaFrame.next.advance n = (f.next.advance n).sigmaFrame
      rw [f.sigma_next, ih]

theorem sigma_expand (f : CopyFrame) (n : Nat) :
    expandTail f.sigmaFrame.stem f.sigmaFrame.last n = sigma (expandTail f.stem f.last n) := by
  rw [← f.sigmaFrame.advance_stem, f.sigma_advance, ← f.advance_stem]
  rfl

end CopyFrame

/-- Adding the diagonal row commutes exactly with every positive-last-column
expansion, including index zero. -/
theorem sigma_expand_nonzero {stem : Matrix} {last : Column} (hne : last ≠ [])
    (hl : Leftward (stem ++ [last])) (hn : Nested (stem ++ [last])) (n : Nat) :
    expand (sigma (stem ++ [last])) n = sigma (expand (stem ++ [last]) n) := by
  cases hc : last.getLast? with
  | none => exact False.elim (hne (List.getLast?_eq_none_iff.mp hc))
  | some root =>
      have hr : root < stem.length := hl (last.length - 1) stem.length root (by
        rw [parent_last, ← List.getLast?_eq_getElem?]; exact hc)
      let f : CopyFrame := ⟨stem, last, root, hc, hr, hl, hn⟩
      rw [sigma_append_last, expand_append, expand_append]
      exact f.sigma_expand n

#print axioms sigma_expand_nonzero

end LaverLowerBounds.ParentBMS
