import ARD2Core
import OrdinalFormal.ExpansionValidity

/-! Finite geometry of the actual ARD2 expansion. All three stored coordinates
move together; both row and root remain at or before their child. -/

namespace OrdinalFormal.ARD2
open Columns
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 4096

theorem nat_compare_laws : GenericSortedColumns.CompareLaws (compare : Nat → Nat → Ordering) where
  eq_iff := fun _ _ => Nat.compare_eq_eq
  lt_trans := Comparison.nat_compare_lt_trans
  trichotomy := by
    intro a b
    by_cases hab : a < b
    · exact Or.inl (Nat.compare_eq_lt.mpr hab)
    · by_cases heq : a = b
      · exact Or.inr (Or.inl heq)
      · exact Or.inr (Or.inr (Nat.compare_eq_lt.mpr (by omega)))

@[simp] theorem expand_zero (g : Graph) : expand g 0 = g.take (g.length - 1) := by
  simp [expand]
  split <;> simp

@[simp] theorem expand_empty (n : Nat) : expand ([] : Graph) n = [] := by
  simp [expand, Columns.control]

theorem expand_prefix_succ (g : Graph) (n : Nat) :
    (expand g n).IsPrefix (expand g (n+1)) := by
  unfold expand
  split
  · exact ⟨[], by simp⟩
  · rename_i e he
    refine ⟨block g e n, ?_⟩
    simp [List.range_succ, List.flatMap_append, List.append_assoc]

theorem expand_prefix (g : Graph) {i j : Nat} (h : i ≤ j) :
    (expand g i).IsPrefix (expand g j) := by
  induction h with
  | refl => exact ⟨[], by simp⟩
  | @step j _ ih => exact ih.trans (expand_prefix_succ g j)

theorem valid_take {g : Graph} (hg : Valid g) (n : Nat) : Valid (g.take n) := by
  intro j a ha
  rw [List.getElem?_take] at ha
  split at ha
  · exact hg j a ha
  · simp at ha

theorem control_valid {g : Graph} (hg : Valid g) {e : Entry}
    (he : control compare (g.getLast?.getD []) = some e) :
    e.row ≤ g.length - 1 ∧ e.root ≤ g.length - 1 ∧ e.parent < g.length - 1 := by
  have hm := ExpansionValidity.control_mem compare he
  rw [List.getLast?_eq_getElem?] at hm
  exact hg _ e hm

@[simp] theorem block_length (g : Graph) (e : Entry) (b : Nat) :
    (block g e b).length = g.length - 1 - e.parent := by simp [block]

theorem blocks_length (g : Graph) (e : Entry) (n : Nat) :
    ((List.range n).flatMap (block g e)).length = n * (g.length - 1 - e.parent) := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, List.flatMap_append, ih, Nat.add_mul]

theorem stage_length (g : Graph) (e : Entry) (b : Nat) :
    (stage g e b).length = width g e b := by
  simp only [stage, List.length_append, List.length_take, blocks_length, width,
    Nat.min_eq_left (Nat.sub_le g.length 1)]

theorem stage_succ (g : Graph) (e : Entry) (b : Nat) :
    stage g e (b+1) = stage g e b ++ block g e b := by
  simp [stage, List.range_succ, List.flatMap_append, List.append_assoc]

theorem expand_eq_stage (g : Graph) {e : Entry}
    (he : control compare (g.getLast?.getD []) = some e) (n : Nat) :
    expand g n = stage g e n := by simp [expand, he, stage]

theorem cut_lt {g : Graph} {e : Entry} (he : e.parent < g.length - 1) (b : Nat) :
    cut g e b < width g e b := by unfold cut width; omega

theorem shift_lt {g : Graph} {e : Entry} {i : Nat}
    (hi : i < g.length - 1) (b : Nat) : shift g e b i < width g e b :=
  ExpansionValidity.move_lt_shift _ _ _ hi

theorem shift_cut (g : Graph) (e : Entry) (b : Nat) : shift g e b e.parent = cut g e b := by
  simp [shift, cut, move]

theorem shift_le {g : Graph} {e : Entry} {i : Nat}
    (hi : i ≤ g.length - 1) (b : Nat) : shift g e b i ≤ width g e b := by
  have hm := ExpansionValidity.move_le e.parent (g.length-1-e.parent) b i
  unfold shift width
  omega

theorem shift_last {g : Graph} {e : Entry} (he : e.parent < g.length-1) (b : Nat) :
    shift g e b (g.length-1) = width g e b := by
  simp [shift, width, move, Nat.not_lt.mpr (Nat.le_of_lt he)]

theorem generated_bound {g : Graph} {e : Entry} (he : e.parent < g.length-1) (b : Nat) :
    e.parent + (b+1)*(g.length-1-e.parent) = width g e b := by
  unfold width
  simp only [Nat.add_mul, Nat.one_mul]
  omega

theorem width_succ {g : Graph} {e : Entry} (he : e.parent < g.length - 1) (b : Nat) :
    width g e (b+1) = width g e b + (width g e b - cut g e b) := by
  unfold width cut
  simp only [Nat.add_mul, Nat.one_mul]
  omega

theorem shift_succ {g : Graph} {e : Entry} (he : e.parent < g.length - 1) (b i : Nat) :
    ReflectionTransport.moveColumn (width g e b) (cut g e b) (shift g e b i) =
      shift g e (b+1) i :=
  ColumnRepresentation.move_succ _ _ _ _ (Nat.le_of_lt he)

def Weakened (a s : Entry) : Prop :=
  a.row = s.row ∧ a.parent = s.parent ∧ a.root ≤ s.root

theorem block_entry_origin (g : Graph) (e : Entry) (b i : Nat)
    (hi : i < g.length - 1 - e.parent) {a : Entry}
    (ha : a ∈ (block g e b)[i]?.getD []) :
    (∃ s ∈ g[e.parent+i]?.getD [], Weakened a (moveEntry e.parent (g.length-1-e.parent) (b+1) s)) ∨
    (i = 0 ∧ ∃ s ∈ seam g e b, Weakened a s) := by
  simp only [block, List.getElem?_map, List.getElem?_range, hi, Option.map_some, Option.getD_some] at ha
  obtain ⟨s, hs, hr, hp, hq⟩ := ColumnRepresentation.mem_normalizeColumn_source compare ha
  rcases List.mem_append.mp hs with hs | hs
  · obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hs
    exact Or.inl ⟨old, hold, hr, hp, hq⟩
  · split at hs
    · exact Or.inr ⟨by assumption, s, hs, hr, hp, hq⟩
    · simp at hs

theorem stage_step_origin (g : Graph) (e : Entry) (b j : Nat) {a : Entry}
    (ha : a ∈ (stage g e (b+1))[j]?.getD []) :
    (a ∈ (stage g e b)[j]?.getD []) ∨
    (∃ i, i < g.length - 1 - e.parent ∧ j = width g e b + i ∧
      ((∃ s ∈ g[e.parent+i]?.getD [], Weakened a (moveEntry e.parent (g.length-1-e.parent) (b+1) s)) ∨
       (i=0 ∧ ∃ s ∈ seam g e b, Weakened a s))) := by
  rw [stage_succ, List.getElem?_append] at ha
  split at ha
  · exact Or.inl ha
  · rename_i hj
    have hi := ColumnRepresentation.index_lt_of_entry_mem ha
    rw [block_length, stage_length] at hi
    rw [stage_length] at ha hj
    refine Or.inr ⟨j-width g e b, hi, by omega, ?_⟩
    exact block_entry_origin g e b _ hi ha

theorem seam_valid {g : Graph} (hg : Valid g) (e : Entry)
    (he : e.parent < g.length-1) (hk : e.row ≤ g.length-1) (b : Nat) :
    ∀ a ∈ seam g e b, NeedValid (width g e b) a := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · simp only [ordinarySeam, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range] at ha
    obtain ⟨s, hs, q, ⟨hq, _⟩, rfl⟩ := ha
    rw [List.getLast?_eq_getElem?] at hs
    have hv := hg _ s hs
    have hr := shift_le (g := g) (e := e) hv.2.1 b
    unfold shift at hr
    change move e.parent (g.length-1-e.parent) b s.row ≤ width g e b ∧
      q ≤ width g e b ∧
      move e.parent (g.length-1-e.parent) b s.parent < width g e b
    exact ⟨shift_le hv.1 b, Nat.le_trans (by omega) hr, shift_lt hv.2.2 b⟩
  · simp only [generatedSeam, List.mem_flatMap, List.mem_map, List.mem_range] at ha
    obtain ⟨row, hrow, q, hq, rfl⟩ := ha
    have hcut := cut_lt he b
    have hrowbound := shift_le (g := g) (e := e) hk b
    unfold shift at hrowbound
    have hm := shift_cut g e b
    change move e.parent (g.length-1-e.parent) b e.parent = cut g e b at hm
    change row ≤ width g e b ∧ q ≤ width g e b ∧
      move e.parent (g.length-1-e.parent) b e.parent < width g e b
    rw [generated_bound he b] at hq
    rw [hm]
    exact ⟨by omega, by omega, hcut⟩

theorem block_valid {g : Graph} (hg : Valid g) (e : Entry)
    (he : e.parent < g.length-1) (hk : e.row ≤ g.length-1) (b i : Nat)
    (hi : i < g.length-1-e.parent) :
    ∀ a ∈ (block g e b)[i]?.getD [], NeedValid (width g e b+i) a := by
  intro a ha
  rcases block_entry_origin g e b i hi ha with ⟨s, hs, hr, hp, hq⟩ | ⟨hi0, s, hs, hr, hp, hq⟩
  · have hv := hg (e.parent+i) s hs
    have hrow := ExpansionValidity.move_le e.parent (g.length-1-e.parent) (b+1) s.row
    have hroot := ExpansionValidity.move_le e.parent (g.length-1-e.parent) (b+1) s.root
    have hparent := ExpansionValidity.move_lt_shift e.parent (g.length-1-e.parent) (b+1) hv.2.2
    simp only [moveEntry] at hr hp hq
    simp only [Nat.add_mul, Nat.one_mul] at hrow hparent hroot
    unfold NeedValid width
    rw [hr, hp]
    exact ⟨by omega, by omega, by omega⟩
  · subst i
    have hv := seam_valid hg e he hk b s hs
    unfold NeedValid at hv ⊢
    rw [hr, hp]
    exact ⟨by omega, Nat.le_trans hq hv.2.1, by omega⟩

theorem stage_valid {g : Graph} (hg : Valid g) (e : Entry)
    (he : e.parent < g.length-1) (hk : e.row ≤ g.length-1) (b : Nat) : Valid (stage g e b) := by
  induction b with
  | zero => simpa [stage] using valid_take hg (g.length-1)
  | succ b ih =>
    intro j a ha
    rcases stage_step_origin g e b j ha with hold | ⟨i, hi, hj, _⟩
    · exact ih j a hold
    · have hmem : a ∈ (block g e b)[i]?.getD [] := by
        rw [stage_succ, List.getElem?_append] at ha
        simp only [stage_length] at ha
        rw [if_neg (by omega)] at ha
        have hsub : j - width g e b = i := by omega
        rwa [hsub] at ha
      simpa [NeedValid, hj] using block_valid hg e he hk b i hi a hmem

theorem expand_valid {g : Graph} (hg : Valid g) (n : Nat) : Valid (expand g n) := by
  cases he : control compare (g.getLast?.getD []) with
  | none => simpa [expand, he] using valid_take hg (g.length-1)
  | some e =>
    rw [expand_eq_stage g he]
    have hv := control_valid hg he
    exact stage_valid hg e hv.2.2 hv.1 n

theorem expand_canonical {g : Graph} (hg : Canonical g) (n : Nat) : Canonical (expand g n) := by
  intro c hc
  unfold expand at hc
  split at hc
  · exact hg c (List.mem_of_mem_take hc)
  · rcases List.mem_append.mp hc with hc | hc
    · exact hg c (List.mem_of_mem_take hc)
    · obtain ⟨b, _, hb⟩ := List.mem_flatMap.mp hc
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hb
      exact GenericSortedColumns.normalized_column_canonical compare nat_compare_laws _

@[simp] theorem seed_length (n : Nat) : (seed n).length = n := by simp [seed]

theorem seed_valid (n : Nat) : Valid (seed n) := by
  intro j a ha
  by_cases hj : j < n
  · simp only [seed, List.getElem?_map, List.getElem?_range, hj, Option.map_some, Option.getD_some] at ha
    split at ha
    · simp at ha
    · rename_i hzero
      obtain ⟨s, hs, hr, hp, hq⟩ := ColumnRepresentation.mem_normalizeColumn_source compare ha
      simp only [List.mem_singleton] at hs
      subst s
      simp only at hr hp hq
      exact ⟨by omega, by omega, by omega⟩
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hj)] at ha
    simp at ha

theorem seed_canonical (n : Nat) : Canonical (seed n) := by
  intro c hc
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
  split
  · exact ⟨List.Pairwise.nil, by simp⟩
  · exact GenericSortedColumns.normalized_column_canonical compare nat_compare_laws _

theorem seed_succ_take (n : Nat) : (seed (n+1)).take n = seed n := by
  simp [seed, List.range_succ, List.map_append]

theorem seed_succ_zero (n : Nat) : expand (seed (n+1)) 0 = seed n := by
  rw [expand_zero, seed_length]
  simpa using seed_succ_take n

#print axioms stage_step_origin
#print axioms stage_valid
#print axioms expand_valid
#print axioms expand_canonical
#print axioms seed_valid
#print axioms seed_succ_zero

end OrdinalFormal.ARD2
