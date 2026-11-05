import LaverLowerBounds.ParentPreparation

set_option autoImplicit false

namespace LaverLowerBounds.ParentBMS

structure CopyFrame where
  stem : Matrix
  last : Column
  root : Nat
  control : last.getLast? = some root
  root_lt : root < stem.length
  leftward : Leftward (stem ++ [last])
  nested : Nested (stem ++ [last])

namespace CopyFrame

def row (f : CopyFrame) := f.last.length - 1
def width (f : CopyFrame) := f.stem.length - f.root
def out (f : CopyFrame) := expandTail f.stem f.last 1
def move (f : CopyFrame) := shift f.root f.width

theorem out_eq (f : CopyFrame) :
    f.out = f.stem ++ copy f.stem f.last f.row f.root f.width 0 := expandTail_one_positive f.control

theorem out_length (f : CopyFrame) : f.out.length = f.stem.length + f.width := by
  rw [f.out_eq, List.length_append, copy_length]

theorem stem_prefix (f : CopyFrame) : f.stem.IsPrefix f.out := by rw [f.out_eq]; exact ⟨_, rfl⟩

theorem prepared_prefix (f : CopyFrame) : (prepare f.stem f.last f.row f.root).IsPrefix f.out :=
  prepare_prefix_one f.control f.root_lt

theorem move_low (f : CopyFrame) {i : Nat} (hi : i < f.root) : f.move i = i := by simp [move, shift, hi]
theorem move_high (f : CopyFrame) {i : Nat} (hi : f.root ≤ i) : f.move i = i + f.width := by
  simp [move, shift, show ¬ i < f.root by omega]
theorem move_root (f : CopyFrame) : f.move f.root = f.stem.length := by
  rw [f.move_high (Nat.le_refl _)]
  have := f.root_lt
  dsimp [width]
  omega

theorem parent_old (f : CopyFrame) {q i : Nat} (hi : i < f.stem.length) :
    parent f.out q i = parent f.stem q i := parent_prefix f.stem_prefix hi

theorem parent_low_head (f : CopyFrame) {q : Nat} (hq : q < f.row) :
    parent f.out q f.stem.length = f.last[q]? := by
  rw [parent_prefix f.prepared_prefix (by rw [prepare_length]; omega)]
  exact parent_prepare_low (Nat.sub_le _ _) hq

theorem parent_high_head (f : CopyFrame) {q : Nat} (hq : f.row ≤ q) :
    parent f.out q f.stem.length = parent f.stem q f.root := by
  rw [parent_prefix f.prepared_prefix (by rw [prepare_length]; omega)]
  exact parent_prepare_high (Nat.sub_le _ _) hq f.root_lt

theorem parent_copied (f : CopyFrame) {q i : Nat} (hroot : f.root < i) (hi : i < f.stem.length) :
    parent f.out q (i + f.width) = (parent f.stem q i).map f.move := by
  have hw := f.root_lt
  have hs : f.stem.length ≤ i + f.width := by dsimp [width]; omega
  have hl : i + f.width - f.stem.length < f.width := by dsimp [width]; omega
  have hn : i + f.width - f.stem.length ≠ 0 := by dsimp [width]; omega
  have he : f.root + (i + f.width - f.stem.length) = i := by dsimp [width]; omega
  have hc : f.out[i + f.width]? = some ((f.stem[i]?.getD []).map f.move) := by
    rw [f.out_eq, List.getElem?_append_right hs, copy_zero, List.getElem?_map,
      List.getElem?_range hl]
    simp only [Option.map_some, if_neg hn, he]
    rfl
  simp only [parent, hc, Option.bind_some, List.getElem?_map,
    List.getElem?_eq_getElem hi, Option.getD_some]

theorem low_ancestry (f : CopyFrame) {q p i : Nat} (hq : q < f.row)
    (ha : Ancestor (f.stem ++ [f.last]) q p i) : Ancestor f.out q p i :=
  (ancestry_prepare_low (Nat.sub_le _ _) hq ha).to_prefix_extension f.prepared_prefix

theorem root_ancestry (f : CopyFrame) {q p : Nat}
    (ha : Ancestor f.stem q p f.root) : Ancestor f.out q p f.stem.length := by
  by_cases hq : q < f.row
  · have control : parent (f.stem ++ [f.last]) f.row f.stem.length = some f.root := by
      rw [parent_last, row, ← List.getLast?_eq_getElem?]
      exact f.control
    have rootLast : Ancestor (f.stem ++ [f.last]) q f.root f.stem.length :=
      (Ancestor.direct control).lower f.nested (Nat.le_of_lt hq)
    exact f.low_ancestry hq ((ha.to_prefix_extension ⟨[f.last], rfl⟩).trans rootLast)
  · exact (ancestry_prepare_from_root (Nat.sub_le _ _) (by change f.row ≤ q; omega) f.root_lt ha).to_prefix_extension f.prepared_prefix

/-- The full shifted ancestor relation survives copying, even for paths
crossing the cut. The new head can add ancestors, so equality is unnecessary. -/
theorem lift_edge (f : CopyFrame) {q p i : Nat} (hp : parent f.stem q i = some p) :
    Ancestor f.out q (f.move p) (f.move i) := by
  have hi := parent_column_lt hp
  have hpi := f.leftward q i p (by rw [parent_append_left hi]; exact hp)
  by_cases hilow : i < f.root
  · rw [f.move_low hilow, f.move_low (by omega : p < f.root)]
    exact (Ancestor.direct hp).to_prefix_extension f.stem_prefix
  · by_cases he : i = f.root
    · subst i
      rw [f.move_root, f.move_low hpi]
      exact f.root_ancestry (.direct hp)
    · rw [f.move_high (by omega : f.root ≤ i)]
      apply Ancestor.direct
      rw [f.parent_copied (by omega) hi, hp]
      rfl

theorem lift_ancestry (f : CopyFrame) {q p i : Nat} (ha : Ancestor f.stem q p i) :
    Ancestor f.out q (f.move p) (f.move i) := ha.map_edges (fun _ _ he => f.lift_edge he)

theorem out_leftward (f : CopyFrame) : Leftward f.out := by
  intro q i p hp
  have hi := parent_column_lt hp
  rw [f.out_length] at hi
  by_cases hiold : i < f.stem.length
  · rw [f.parent_old hiold] at hp
    exact f.leftward q i p (by rw [parent_append_left hiold]; exact hp)
  · by_cases hhead : i = f.stem.length
    · subst i
      by_cases hq : q < f.row
      · rw [f.parent_low_head hq] at hp
        exact f.leftward q f.stem.length p (by rw [parent_last]; exact hp)
      · rw [f.parent_high_head (by omega)] at hp
        have he := f.leftward q f.root p (by rw [parent_append_left f.root_lt]; exact hp)
        have := f.root_lt
        omega
    · let old := i - f.width
      have oldRoot : f.root < old := by have := f.root_lt; dsimp [old, width] at *; omega
      have oldBound : old < f.stem.length := by dsimp [old, width] at *; omega
      have oldEq : old + f.width = i := by dsimp [old, width] at *; omega
      rw [← oldEq, f.parent_copied oldRoot oldBound] at hp
      cases he : parent f.stem q old with
      | none => simp only [he, Option.map_none] at hp; contradiction
      | some oldParent =>
          have mapped : f.move oldParent = p := by simpa only [he, Option.map_some, Option.some.injEq] using hp
          have hlt := f.leftward q old oldParent (by rw [parent_append_left oldBound]; exact he)
          rw [← mapped]
          dsimp [move, shift]
          split <;> omega

theorem out_nested (f : CopyFrame) : Nested f.out := by
  intro q i p hp
  have hi := parent_column_lt hp
  rw [f.out_length] at hi
  by_cases hiold : i < f.stem.length
  · rw [f.parent_old hiold] at hp
    have he : parent (f.stem ++ [f.last]) (q + 1) i = some p := by rw [parent_append_left hiold]; exact hp
    have ha := (f.nested q i p he).of_prefix ⟨[f.last], rfl⟩ f.leftward hiold
    exact ha.to_prefix_extension f.stem_prefix
  · by_cases hhead : i = f.stem.length
    · subst i
      have hcontrol : parent (f.stem ++ [f.last]) f.row f.stem.length = some f.root := by
        rw [parent_last, row, ← List.getLast?_eq_getElem?]
        exact f.control
      have hn := prepare_nested (Nat.sub_le f.last.length 1) f.root_lt hcontrol f.leftward f.nested
      have he : parent (prepare f.stem f.last f.row f.root) (q + 1) f.stem.length = some p := by
        rwa [parent_prefix f.prepared_prefix (by rw [prepare_length]; omega)] at hp
      exact (hn q f.stem.length p he).to_prefix_extension f.prepared_prefix
    · let old := i - f.width
      have oldRoot : f.root < old := by have := f.root_lt; dsimp [old, width] at *; omega
      have oldBound : old < f.stem.length := by dsimp [old, width] at *; omega
      have oldEq : old + f.width = i := by dsimp [old, width] at *; omega
      rw [← oldEq, f.parent_copied oldRoot oldBound] at hp
      cases he : parent f.stem (q + 1) old with
      | none => simp only [he, Option.map_none] at hp; contradiction
      | some oldParent =>
          have mapped : f.move oldParent = p := by simpa only [he, Option.map_some, Option.some.injEq] using hp
          have horiginal : parent (f.stem ++ [f.last]) (q + 1) old = some oldParent := by
            rw [parent_append_left oldBound]
            exact he
          have ha := (f.nested q old oldParent horiginal).of_prefix ⟨[f.last], rfl⟩ f.leftward oldBound
          have lifted := f.lift_ancestry ha
          rwa [mapped, f.move_high (Nat.le_of_lt oldRoot), oldEq] at lifted

#print axioms lift_ancestry
#print axioms out_leftward
#print axioms out_nested

end CopyFrame
end LaverLowerBounds.ParentBMS
