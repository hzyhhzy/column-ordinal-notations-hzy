import LaverLowerBounds.ParentCopyGraph
import LaverLowerBounds.GraphEmbedding

set_option autoImplicit false

namespace LaverLowerBounds.ParentBMS

structure AlignedCopy (s t : CopyFrame) where
  cover : Cover (s.stem ++ [s.last]) (t.stem ++ [t.last])
  row_eq : s.row = t.row
  root_eq : t.root = cover.column s.root

namespace AlignedCopy

variable {s t : CopyFrame}

def column (f : AlignedCopy s t) (i : Nat) :=
  if i < s.stem.length then f.cover.column i
  else f.cover.column (i - s.width) + t.width

theorem old_lt (f : AlignedCopy s t) {i : Nat} (hi : i < s.stem.length) :
    f.cover.column i < t.stem.length := by
  have hh := f.cover.strict i s.stem.length hi (by simp)
  rwa [f.cover.last_column] at hh

theorem column_old (f : AlignedCopy s t) {i : Nat} (hi : i < s.stem.length) :
    f.column i = f.cover.column i := if_pos hi

theorem column_new (f : AlignedCopy s t) {i : Nat} (hr : s.root ≤ i) (_hi : i < s.stem.length) :
    f.column (i + s.width) = f.cover.column i + t.width := by
  have hn : ¬ i + s.width < s.stem.length := by
    have := s.root_lt
    dsimp [CopyFrame.width] at *
    omega
  simp only [column, if_neg hn, Nat.add_sub_cancel]

theorem column_move (f : AlignedCopy s t) {i : Nat} (hi : i < s.stem.length) :
    f.column (s.move i) = t.move (f.cover.column i) := by
  by_cases hlo : i < s.root
  · have htlo : f.cover.column i < t.root := by
      rw [f.root_eq]
      exact f.cover.strict i s.root hlo (by have := s.root_lt; simp; omega)
    rw [s.move_low hlo, f.column_old hi, t.move_low htlo]
  · have hthi : t.root ≤ f.cover.column i := by
      rw [f.root_eq]
      by_cases he : i = s.root
      · simp only [he, Nat.le_refl]
      · exact Nat.le_of_lt (f.cover.strict s.root i (by omega) (by simp; omega))
    rw [s.move_high (by omega), f.column_new (by omega) hi, t.move_high hthi]

theorem column_head (f : AlignedCopy s t) : f.column s.stem.length = t.stem.length := by
  rw [← s.move_root, f.column_move s.root_lt, ← f.root_eq, t.move_root]

theorem new_lower (f : AlignedCopy s t) {i : Nat}
    (hi : s.stem.length ≤ i) (hib : i < s.out.length) :
    t.stem.length ≤ f.column i := by
  have hlen := s.out_length
  have hr := s.root_lt
  have ho : i - s.width < s.stem.length := by omega
  have hor : s.root ≤ i - s.width := by dsimp [CopyFrame.width] at *; omega
  have he : i - s.width + s.width = i := by dsimp [CopyFrame.width] at *; omega
  have hm : t.root ≤ f.cover.column (i - s.width) := by
    rw [f.root_eq]
    by_cases hsame : i - s.width = s.root
    · simp only [hsame, Nat.le_refl]
    · exact Nat.le_of_lt (f.cover.strict s.root (i - s.width) (by omega) (by simp; omega))
  have hc := f.column_new hor ho
  rw [he] at hc
  rw [hc]
  have htotal : t.root + t.width = t.stem.length := by
    have := t.root_lt
    dsimp [CopyFrame.width]
    omega
  omega

theorem column_bounded (f : AlignedCopy s t) {i : Nat} (hi : i < s.out.length) :
    f.column i < t.out.length := by
  rw [t.out_length]
  by_cases hold : i < s.stem.length
  · rw [f.column_old hold]
    have := f.old_lt hold
    omega
  · have hlen := s.out_length
    have hr := s.root_lt
    have ho : i - s.width < s.stem.length := by omega
    have hor : s.root ≤ i - s.width := by dsimp [CopyFrame.width] at *; omega
    have he : i - s.width + s.width = i := by dsimp [CopyFrame.width] at *; omega
    have hc := f.column_new hor ho
    rw [he] at hc
    rw [hc]
    have := f.old_lt ho
    omega

theorem column_strict (f : AlignedCopy s t) {i j : Nat}
    (hij : i < j) (hj : j < s.out.length) : f.column i < f.column j := by
  by_cases hjo : j < s.stem.length
  · rw [f.column_old (by omega : i < s.stem.length), f.column_old hjo]
    exact f.cover.strict i j hij (by simp; omega)
  · by_cases hio : i < s.stem.length
    · rw [f.column_old hio]
      have := f.old_lt hio
      have := f.new_lower (by omega) hj
      omega
    · have hlen := s.out_length
      have hr := s.root_lt
      have hip : i - s.width < j - s.width := by dsimp [CopyFrame.width] at *; omega
      have hjb : j - s.width < s.stem.length := by omega
      have hh := f.cover.strict (i - s.width) (j - s.width) hip (by simp; omega)
      simp only [column, if_neg hio, if_neg hjo]
      omega

theorem edge (f : AlignedCopy s t) {q p i : Nat} (hp : parent s.out q i = some p) :
    Ancestor t.out q (f.column p) (f.column i) := by
  have hi := parent_column_lt hp
  have hpi := s.out_leftward q i p hp
  by_cases hold : i < s.stem.length
  · rw [f.column_old hold, f.column_old (by omega : p < s.stem.length)]
    rw [s.parent_old hold] at hp
    have he : parent (s.stem ++ [s.last]) q i = some p := by rw [parent_append_left hold]; exact hp
    have ha := (f.cover.edge q p i he).of_prefix ⟨[t.last], rfl⟩ t.leftward (f.old_lt hold)
    exact ha.to_prefix_extension t.stem_prefix
  · by_cases hhead : i = s.stem.length
    · subst i
      rw [f.column_head, f.column_old hpi]
      by_cases hlow : q < s.row
      · rw [s.parent_low_head hlow] at hp
        have he : parent (s.stem ++ [s.last]) q s.stem.length = some p := by rw [parent_last]; exact hp
        have ha := f.cover.edge q p s.stem.length he
        rw [f.cover.last_column] at ha
        exact t.low_ancestry (by rwa [← f.row_eq]) ha
      · rw [s.parent_high_head (by omega)] at hp
        have he : parent (s.stem ++ [s.last]) q s.root = some p := by rw [parent_append_left s.root_lt]; exact hp
        have ha := (f.cover.edge q p s.root he).of_prefix ⟨[t.last], rfl⟩ t.leftward (f.old_lt s.root_lt)
        rw [← f.root_eq] at ha
        exact t.root_ancestry ha
    · let old := i - s.width
      have oldRoot : s.root < old := by have := s.root_lt; rw [s.out_length] at hi; dsimp [old, CopyFrame.width] at *; omega
      have oldBound : old < s.stem.length := by rw [s.out_length] at hi; dsimp [old] at *; omega
      have oldEq : old + s.width = i := by have := s.root_lt; dsimp [old, CopyFrame.width] at *; omega
      rw [← oldEq, s.parent_copied oldRoot oldBound] at hp
      cases he : parent s.stem q old with
      | none => simp only [he, Option.map_none] at hp; contradiction
      | some oldParent =>
          have mapped : s.move oldParent = p := by simpa only [he, Option.map_some, Option.some.injEq] using hp
          have horiginal : parent (s.stem ++ [s.last]) q old = some oldParent := by
            rw [parent_append_left oldBound]
            exact he
          have hpbound : oldParent < s.stem.length := Nat.lt_trans (s.leftward q old oldParent horiginal) oldBound
          have ha := (f.cover.edge q oldParent old horiginal).of_prefix ⟨[t.last], rfl⟩ t.leftward (f.old_lt oldBound)
          have hmove : s.move old = i := by rw [s.move_high (Nat.le_of_lt oldRoot)]; exact oldEq
          rw [← mapped, ← hmove, f.column_move hpbound, f.column_move oldBound]
          exact t.lift_ancestry ha

def embedding (f : AlignedCopy s t) : GraphEmbedding s.out t.out where
  column := f.column
  bounded _ hi := f.column_bounded hi
  strict _ _ hij hj := f.column_strict hij hj
  edge _ _ _ hp := f.edge hp

/-- Aligned fixed-[1] copies preserve ancestor coverage, after cropping the
target at the image of the final source column. -/
def copiedCover (f : AlignedCopy s t) : Cover s.out f.embedding.cropped :=
  f.embedding.toCover t.out_leftward

#print axioms copiedCover

end AlignedCopy
end LaverLowerBounds.ParentBMS
