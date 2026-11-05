import LaverLowerBounds.NumericParentBasics

set_option autoImplicit false

namespace LaverLowerBounds.NumericBMS
open YesMetaZFC.BMS
open ExpansionContext

theorem copy_position_shift {a : ValidArray} (c : ExpansionContext a)
    (n i : Nat) : ParentBMS.shift c.parentColumn (n * c.blockLength)
      (c.copyPosition 0 i) = c.copyPosition n i := by
  simp only [copyPosition_zero, ParentBMS.shift]
  rw [if_neg (by omega : ¬c.parentColumn + i < c.parentColumn)]
  simp only [copyPosition, copyStart]
  omega

theorem parent_internal_copy {a : ValidArray} (c : ExpansionContext a)
    (n r : Nat) {i : Nat} (hip : 0 < i) (hi : i < c.blockLength) :
    parent r (a.expand n).raw (c.copyPosition n i) =
      (parent r a.raw (c.parentColumn + i)).map
        (ParentBMS.shift c.parentColumn (n * c.blockLength)) := by
  have hstem : c.parentColumn + i < c.lastIndex := by
    have := c.parentColumn_lt_lastIndex
    unfold blockLength at hi
    omega
  have hzero : parent r (a.expand n).raw (c.copyPosition 0 i) =
      parent r a.raw (c.parentColumn + i) := by
    simpa using parent_expand_stem c n r hstem
  rw [← hzero]
  apply parent_map_of_ancestry _ (fun _ _ h => shift_mono _ _ h)
  · intro p hp
    by_cases hg : p < c.parentColumn
    · simpa [ParentBMS.shift, hg] using
        (show isAncestor (a.expand n).raw r p (c.copyPosition n i) = true by
          rw [← (c.lemma25_all n r).good_to_copy hg hi]; exact hp)
    · have hlt := isAncestor_lt hp
      have hpLocal : p - c.parentColumn < c.blockLength := by
        simp only [copyPosition_zero] at hlt
        omega
      have he : p = c.copyPosition 0 (p - c.parentColumn) := by
        simp only [copyPosition_zero]; omega
      rw [he, copy_position_shift]
      rw [← (c.lemma25_all n r).inside_copy hpLocal hi]
      rwa [← he]
  · intro q hq
    have hqa := direct_parent_isAncestor hq
    rcases (c.lemma25_all n r).parent_locality hip hi hq with hg | hc
    · refine ⟨q, ?_, by simp [ParentBMS.shift, hg]⟩
      rw [(c.lemma25_all n r).good_to_copy hg hi]
      exact hqa
    · obtain ⟨j, hj, he⟩ := c.inCopy_iff_exists_copyPosition.mp hc
      refine ⟨c.copyPosition 0 j, ?_, ?_⟩
      · rw [(c.lemma25_all n r).inside_copy hj hi]
        rwa [he] at hqa
      · rw [copy_position_shift]
        exact he.symm

theorem parent_first_high {a : ValidArray} (c : ExpansionContext a)
    (n : Nat) {r : Nat} (hr : c.maximalRow ≤ r) :
    parent r (a.expand n).raw (c.copyPosition n 0) =
      parent r a.raw c.parentColumn := by
  rw [← c.parent_first_copies_eq_of_maximalRow_le hr
    (fun q _ _ hg => (c.lemma25_all n q).good_to_copy hg c.blockLength_pos)]
  simpa using parent_expand_stem c n r c.parentColumn_lt_lastIndex

theorem parent_first_low {a : ValidArray} (c : ExpansionContext a)
    {n r : Nat} (hn : 0 < n) (hr : r < c.maximalRow) :
    parent r (a.expand n).raw (c.copyPosition n 0) =
      (parent r a.raw c.lastIndex).map
        (ParentBMS.shift c.parentColumn ((n - 1) * c.blockLength)) := by
  have hroot : isAncestor a.raw r c.parentColumn c.lastIndex = true :=
    isAncestor_of_lt_row hr (direct_parent_isAncestor c.parent_eq)
  cases hp : parent r a.raw c.lastIndex with
  | none =>
    have := isAncestor_eq_false_of_parent_none hp (ancestor := c.parentColumn)
    simp_all
  | some p =>
    have hple := ancestor_le_parent hp hroot
    have hplt := parent_some_lt hp
    have hlocal : p - c.parentColumn < c.blockLength := by
      unfold blockLength; omega
    have he : c.parentColumn + (p - c.parentColumn) = p := by omega
    have hpanc : isAncestor (a.expand n).raw r
        (c.copyPosition (n - 1) (p - c.parentColumn)) (c.copyPosition n 0) = true := by
      rw [← (c.lemma25_all n r).previous_to_next hn hr hlocal, he]
      exact direct_parent_isAncestor hp
    simp only [Option.map_some]
    have hshift : ParentBMS.shift c.parentColumn ((n - 1) * c.blockLength) p =
        c.copyPosition (n - 1) (p - c.parentColumn) := by
      simp only [ParentBMS.shift, if_neg (by omega : ¬p < c.parentColumn),
        copyPosition, copyStart]
      omega
    rw [hshift]
    apply parent_some_of_greatest_ancestor hpanc
    intro q hq
    by_cases hle : q ≤ c.copyPosition (n - 1) (p - c.parentColumn)
    · exact hle
    · have hqlt := isAncestor_lt hq
      have hn' : n = (n - 1) + 1 := by omega
      have hwidth : n * c.blockLength = (n - 1) * c.blockLength + c.blockLength := by
        calc
          n * c.blockLength = ((n - 1) + 1) * c.blockLength :=
            congrArg (fun k => k * c.blockLength) hn'
          _ = (n - 1) * c.blockLength + c.blockLength := by simp [Nat.add_mul]
      let start := c.parentColumn + (n - 1) * c.blockLength
      have hstart : start ≤ q := by
        simp only [copyPosition, copyStart] at hle
        dsimp [start]; omega
      have hj : q - start < c.blockLength := by
        simp only [copyPosition, copyStart] at hqlt
        dsimp [start]; omega
      have hqe : q = c.copyPosition (n - 1) (q - start) := by
        simp only [copyPosition, copyStart]; dsimp [start] at *; omega
      have hsource : isAncestor a.raw r (c.parentColumn + (q - start)) c.lastIndex = true := by
        rw [(c.lemma25_all n r).previous_to_next hn hr hj]
        rwa [← hqe]
      have := ancestor_le_parent hp hsource
      simp only [copyPosition, copyStart]
      dsimp [start] at *
      omega

/-- Exact parent rule for any positive copy, in any larger expansion. -/
theorem parent_copied {a : ValidArray} (c : ExpansionContext a)
    {n b i : Nat} (hb : 0 < b) (hbn : b ≤ n) (hi : i < c.blockLength) (r : Nat) :
    parent r (a.expand n).raw (c.copyPosition b i) =
      if i = 0 then
        if r < c.maximalRow then
          (parent r a.raw c.lastIndex).map
            (ParentBMS.shift c.parentColumn ((b - 1) * c.blockLength))
        else parent r a.raw c.parentColumn
      else (parent r a.raw (c.parentColumn + i)).map
        (ParentBMS.shift c.parentColumn (b * c.blockLength)) := by
  rw [← parent_expand_indices c hbn (c.copyPosition_lt_length (Nat.le_refl b) hi)]
  by_cases hi0 : i = 0
  · subst i
    simp only [↓reduceIte]
    by_cases hr : r < c.maximalRow
    · rw [if_pos hr]; exact parent_first_low c hb hr
    · rw [if_neg hr]; exact parent_first_high c b (by omega)
  · rw [if_neg hi0]
    exact parent_internal_copy c b r (by omega) hi

#print axioms parent_copied

end LaverLowerBounds.NumericBMS
