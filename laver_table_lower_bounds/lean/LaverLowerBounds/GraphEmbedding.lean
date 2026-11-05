import LaverLowerBounds.CoverPreparation

set_option autoImplicit false

namespace LaverLowerBounds.ParentBMS

/-- An increasing ancestor embedding, without requiring the last columns to
agree. Cropping at its final image turns it into a cover. -/
structure GraphEmbedding (s t : Matrix) where
  column : Nat → Nat
  bounded : ∀ i, i < s.length → column i < t.length
  strict : ∀ i j, i < j → j < s.length → column i < column j
  edge : ∀ row p i, parent s row i = some p → Ancestor t row (column p) (column i)

def Cover.toEmbedding {s t : Matrix} (f : Cover s t) : GraphEmbedding s t where
  column := f.column
  bounded := f.bounded
  strict := f.strict
  edge := f.edge

theorem leftward_prefix {s t : Matrix} (hp : s.IsPrefix t) (ht : Leftward t) : Leftward s := by
  intro row i p he
  exact ht row i p (by rw [parent_prefix hp (parent_column_lt he)]; exact he)

namespace GraphEmbedding

variable {s t u : Matrix}

def restrict (f : GraphEmbedding s t) (hp : u.IsPrefix s) : GraphEmbedding u t where
  column := f.column
  bounded i hi := f.bounded i (Nat.lt_of_lt_of_le hi hp.length_le)
  strict i j hij hj := f.strict i j hij (Nat.lt_of_lt_of_le hj hp.length_le)
  edge row p i he := f.edge row p i (by rw [parent_prefix hp (parent_column_lt he)]; exact he)

def cut (f : GraphEmbedding s t) := if s = [] then 0 else f.column (s.length - 1) + 1
def cropped (f : GraphEmbedding s t) := t.take f.cut

theorem cut_le (f : GraphEmbedding s t) : f.cut ≤ t.length := by
  unfold cut
  split
  · omega
  · have hs : 0 < s.length := by cases s <;> simp_all
    have := f.bounded (s.length - 1) (by omega)
    omega

theorem image_lt_cut (f : GraphEmbedding s t) {i : Nat} (hi : i < s.length) :
    f.column i < f.cut := by
  have hs : s ≠ [] := by intro he; simp [he] at hi
  rw [cut, if_neg hs]
  by_cases he : i = s.length - 1
  · rw [he]; omega
  · have := f.strict i (s.length - 1) (by omega) (by omega)
    omega

theorem cropped_length (f : GraphEmbedding s t) : f.cropped.length = f.cut := by
  exact List.length_take_of_le f.cut_le

theorem cropped_prefix (f : GraphEmbedding s t) : f.cropped.IsPrefix t := List.take_prefix _ _

def toCover (f : GraphEmbedding s t) (ht : Leftward t) : Cover s f.cropped where
  column := f.column
  bounded i hi := by rw [f.cropped_length]; exact f.image_lt_cut hi
  strict := f.strict
  edge row p i he :=
    (f.edge row p i he).of_prefix f.cropped_prefix ht
      (by rw [f.cropped_length]; exact f.image_lt_cut (parent_column_lt he))
  last hs := by rw [f.cropped_length, cut, if_neg hs]; omega

end GraphEmbedding

namespace Cover

variable {s t u : Matrix}

/-- Restricting to a proper source prefix crops to a proper target prefix. -/
theorem restrict_cut_lt (f : Cover s t) (hp : u.IsPrefix s) (hne : u ≠ s) (hs : s ≠ []) :
    (f.toEmbedding.restrict hp).cut < t.length := by
  have slen : 0 < s.length := by cases s <;> simp_all
  have tlen : 0 < t.length := Nat.zero_lt_of_lt (f.bounded 0 slen)
  by_cases hu : u = []
  · simp only [GraphEmbedding.cut, hu, ↓reduceIte]
    exact tlen
  · have ulen : 0 < u.length := by cases u <;> simp_all
    have lens : u.length < s.length := by
      have hle := hp.length_le
      have hn : ¬ s.length ≤ u.length := by intro hh; exact hne (hp.eq_of_length_le hh)
      omega
    have hh := f.strict (u.length - 1) (s.length - 1) (by omega) (by omega)
    rw [f.last hs] at hh
    change (if u = [] then 0 else f.column (u.length - 1) + 1) < t.length
    rw [if_neg hu]
    omega

theorem restrict_cropped_stem (f : Cover s t) (hp : u.IsPrefix s) (hne : u ≠ s) (hs : s ≠ []) :
    (f.toEmbedding.restrict hp).cropped.IsPrefix t.dropLast := by
  apply PrefixDescent.proper_prefix_stem (f.toEmbedding.restrict hp).cropped_prefix
  intro he
  have hh := f.restrict_cut_lt hp hne hs
  rw [← (f.toEmbedding.restrict hp).cropped_length, he] at hh
  omega

end Cover

#print axioms GraphEmbedding.toCover
#print axioms Cover.restrict_cropped_stem

end LaverLowerBounds.ParentBMS
