import ARD2Structure
import OrdinalFormal.BlockFiniteUnion

/-!
Exact edge membership for the block implementation. The intended final
specification is the finite union of all shifted internal edges and seams,
including downward root closure. These are combinatorial equivalences, with
no accessibility, ordinal interpretation or well-ordering hypotheses.
-/

namespace OrdinalFormal.ARD2.FiniteUnion
open Columns ExpansionValidity
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 4096

theorem normalize_mem_iff (c : Column) (a : Entry) :
    a ∈ normalizeColumn compare c ↔ ∃ s ∈ c, Weakened a s := by
  constructor
  · exact ColumnRepresentation.mem_normalizeColumn_source compare
  · rintro ⟨s, hs, hr, hp, hq⟩
    apply (GenericSortedColumns.mem_dedupSorted_iff compare nat_compare_laws _ _).mpr
    apply (ColumnRepresentation.mem_sortDescending compare _ _).mpr
    apply List.mem_flatMap.mpr
    refine ⟨s, hs, List.mem_map.mpr ⟨a.root, List.mem_range.mpr (by omega), ?_⟩⟩
    cases a
    cases s
    simp_all

theorem block_entry_iff (g : Graph)
    (e : Entry) (b i : Nat) (hi : i < g.length - 1 - e.parent) (a : Entry) :
    a ∈ (block g e b)[i]?.getD [] ↔
    (∃ s ∈ g[e.parent + i]?.getD [],
      Weakened a (moveEntry e.parent (g.length - 1 - e.parent) (b + 1) s)) ∨
    (i = 0 ∧ ∃ s ∈ ordinarySeam (g.getLast?.getD []) e (g.length - 1 - e.parent) b ++
      generatedSeam e (g.length - 1 - e.parent) b, Weakened a s) := by
  simp only [block, List.getElem?_map, List.getElem?_range, hi,
    Option.map_some, Option.getD_some]
  rw [normalize_mem_iff]
  constructor
  · rintro ⟨s, hs, hw⟩
    rcases List.mem_append.mp hs with hs | hs
    · obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hs
      exact Or.inl ⟨old, hold, hw⟩
    · split at hs
      · exact Or.inr ⟨by assumption, s, hs, hw⟩
      · simp at hs
  · intro h
    rcases h with ⟨s, hs, hw⟩ | ⟨hi0, s, hs, hw⟩
    · exact ⟨_, List.mem_append_left _ (List.mem_map.mpr ⟨s, hs, rfl⟩), hw⟩
    · exact ⟨s, List.mem_append_right _ (by simpa [hi0, seam] using hs), hw⟩


/-- Membership in a concatenation of equal-width blocks, with global child
coordinates retained in the conclusion. -/
theorem stage_entry_iff (g : Graph)
    (e : Entry) (n j : Nat) (a : Entry) :
    a ∈ (stage g e n)[j]?.getD [] ↔
      (j < g.length - 1 ∧ a ∈ g[j]?.getD []) ∨
      ∃ b, b < n ∧ ∃ i, i < g.length - 1 - e.parent ∧
        j = g.length - 1 + b * (g.length - 1 - e.parent) + i ∧
        a ∈ (block g e b)[i]?.getD [] := by
  induction n with
  | zero =>
    simp only [stage, List.range_zero, List.flatMap_nil, List.append_nil,
      List.getElem?_take]
    split
    · simp_all
    · have hj : ¬j < g.length - 1 := by omega
      simp [hj]
  | succ n ih =>
    rw [stage_succ, List.getElem?_append]
    split
    · rename_i hj
      rw [ih]
      constructor
      · intro h
        rcases h with h | ⟨b, hb, i, hi, he, hm⟩
        · exact Or.inl h
        · exact Or.inr ⟨b, by omega, i, hi, he, hm⟩
      · intro h
        rcases h with h | ⟨b, hb, i, hi, he, hm⟩
        · exact Or.inl h
        · have hbn : b < n := by
            rw [stage_length] at hj
            unfold width at hj
            by_cases hn : b < n
            · exact hn
            · have : b = n := by omega
              subst b
              omega
          exact Or.inr ⟨b, hbn, i, hi, he, hm⟩
    · rename_i hj
      rw [stage_length] at hj ⊢
      unfold width at hj ⊢
      constructor
      · intro hm
        have hi := ColumnRepresentation.index_lt_of_entry_mem hm
        rw [block_length] at hi
        exact Or.inr ⟨n, by omega, j - (g.length - 1 + n * (g.length - 1 - e.parent)),
          hi, by omega, hm⟩
      · intro h
        rcases h with ⟨hj0, _⟩ | ⟨b, hb, i, hi, he, hm⟩
        · omega
        · have hbn : b = n := by
            by_cases hn : b = n
            · exact hn
            · have hb' : b + 1 ≤ n := by omega
              have hm' := Nat.mul_le_mul_right (g.length - 1 - e.parent) hb'
              rw [Nat.add_mul, Nat.one_mul] at hm'
              omega
          subst b
          have he' : j - (g.length - 1 + n * (g.length - 1 - e.parent)) = i := by omega
          simpa [he'] using hm

theorem weakened_mem {g : Graph} (hc : RootClosed g) {j : Nat}
    {a s : Entry} (hs : s ∈ g[j]?.getD []) (hw : Weakened a s) :
    a ∈ g[j]?.getD [] := by
  cases hj : g[j]? with
  | none => simp [hj] at hs
  | some c =>
    simp only [hj, Option.getD_some] at hs ⊢
    have h := hc c (List.mem_of_getElem? hj) s hs a.root hw.2.2
    have he : {s with root := a.root} = a := by
      cases a
      cases s
      simp_all [Weakened]
    simpa [he] using h

@[simp] theorem move_zero (cut len i : Nat) : move cut len 0 i = i := by
  simp [move]

@[simp] theorem moveEntry_zero (cut len : Nat) (a : Entry) :
    moveEntry cut len 0 a = a := by
  cases a
  simp [moveEntry]

theorem moveEntry_before {g : Graph} (hg : Valid g) {i cut : Nat}
    {s : Entry} (hs : s ∈ g[i]?.getD []) (hi : i < cut) (len b : Nat) :
    moveEntry cut len b s = s := by
  obtain ⟨hrow, hroot, hparent⟩ := hg i s hs
  have hk : s.row < cut := by omega
  have hp : s.parent < cut := by omega
  have hq : s.root < cut := by omega
  cases s
  simp_all [moveEntry, move]

/-- The mathematical finite union, stated independently of block iteration:
all shifted internal edges for b <= n, plus seams for b < n, then root closure.
ARD2 moves the anchor as well as parent and root. -/
def FiniteUnionEdge (g : Graph)
    (e : Entry) (n j : Nat) (a : Entry) : Prop :=
  (∃ b, b ≤ n ∧ ∃ i, i < g.length - 1 ∧ ∃ s ∈ g[i]?.getD [],
    j = move e.parent (g.length - 1 - e.parent) b i ∧
    Weakened a (moveEntry e.parent (g.length - 1 - e.parent) b s)) ∨
  (∃ b, b < n ∧ j = g.length - 1 + b * (g.length - 1 - e.parent) ∧
    ∃ s ∈ ordinarySeam (g.getLast?.getD []) e (g.length - 1 - e.parent) b ++
      generatedSeam e (g.length - 1 - e.parent) b, Weakened a s)

theorem stage_finiteUnion_iff {g : Graph}
    (hg : Valid g) (hc : RootClosed g) (e : Entry)
    (he : e.parent < g.length - 1) (n j : Nat) (a : Entry) :
    a ∈ (stage g e n)[j]?.getD [] ↔
      FiniteUnionEdge g e n j a := by
  rw [stage_entry_iff]
  constructor
  · intro h
    rcases h with ⟨hj, hm⟩ | ⟨b, hb, i, hi, hji, hm⟩
    · exact Or.inl ⟨0, by omega, j, hj, a, hm, by simp,
        by simp [Weakened]⟩
    · rcases (block_entry_iff g e b i hi a).mp hm with
        ⟨s, hs, hw⟩ | ⟨hi0, s, hs, hw⟩
      · apply Or.inl
        refine ⟨b + 1, by omega, e.parent + i, by omega, s, hs, ?_, hw⟩
        have hn : ¬ e.parent + i < e.parent := by omega
        simp only [move, hn, ↓reduceIte, Nat.add_mul, Nat.one_mul]
        omega
      · subst i
        exact Or.inr ⟨b, hb, by simpa using hji, s, hs, hw⟩
  · intro h
    rcases h with ⟨b, hb, i, hi, s, hs, hji, hw⟩ | ⟨b, hb, hji, s, hs, hw⟩
    · by_cases hb0 : b = 0
      · subst b
        simp only [move_zero, moveEntry_zero] at hji hw
        subst j
        exact Or.inl ⟨hi, weakened_mem hc hs hw⟩
      · by_cases hic : i < e.parent
        · have hmove := moveEntry_before hg hs hic (g.length - 1 - e.parent) b
          rw [hmove] at hw
          have hj : j = i := by simpa [move, hic] using hji
          rw [hj]
          exact Or.inl ⟨hi, weakened_mem hc hs hw⟩
        · have hb1 : b - 1 + 1 = b := by omega
          have hii : e.parent + (i - e.parent) = i := by omega
          have hilt : i - e.parent < g.length - 1 - e.parent := by omega
          apply Or.inr
          refine ⟨b - 1, by omega, i - e.parent, hilt, ?_, ?_⟩
          · simp only [move, hic, ↓reduceIte] at hji
            have hm : b * (g.length - 1 - e.parent) =
                (b - 1) * (g.length - 1 - e.parent) + (g.length - 1 - e.parent) := by
              calc
                b * (g.length - 1 - e.parent) =
                    (b - 1 + 1) * (g.length - 1 - e.parent) := congrArg (fun z => z * _) hb1.symm
                _ = _ := by simp only [Nat.add_mul, Nat.one_mul]
            rw [hm] at hji
            omega
          · apply (block_entry_iff g e (b - 1) _ hilt a).mpr
            exact Or.inl ⟨s, by simpa [hii] using hs, by simpa [hb1] using hw⟩
    · have hlen : 0 < g.length - 1 - e.parent := by omega
      exact Or.inr ⟨b, hb, 0, hlen, by simpa using hji,
        (block_entry_iff g e b 0 hlen a).mpr
          (Or.inr ⟨rfl, s, hs, hw⟩)⟩

theorem ordinarySeam_mem_iff (last : Column) (e : Entry)
    (len b : Nat) (a : Entry) :
    a ∈ ordinarySeam last e len b ↔
      ∃ s ∈ last, a.row = move e.parent len b s.row ∧ a.parent = move e.parent len b s.parent ∧
        a.root ≤ move e.parent len b s.root ∧
        (s.row < e.row ∨
          (s.row = e.row ∧ a.root < move e.parent len b e.root)) := by
  simp only [ordinarySeam, List.mem_flatMap, List.mem_map, List.mem_filter,
    List.mem_range, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨s, hs, q, ⟨hq, hguard⟩, heq⟩
    subst a
    exact ⟨s, hs, rfl, rfl, Nat.le_of_lt_succ hq, hguard⟩
  · rintro ⟨s, hs, hr, hp, hq, hguard⟩
    refine ⟨s, hs, a.root, ⟨by omega, hguard⟩, ?_⟩
    cases a
    cases s
    simp_all

theorem ordinarySeam_weakening (last : Column) (e : Entry)
    (len b : Nat) (a : Entry) :
    (∃ s ∈ ordinarySeam last e len b, Weakened a s) ↔
      a ∈ ordinarySeam last e len b := by
  constructor
  · rintro ⟨s, hs, hw⟩
    obtain ⟨old, hold, hr, hp, hq, hguard⟩ := (ordinarySeam_mem_iff last e len b s).mp hs
    apply (ordinarySeam_mem_iff last e len b a).mpr
    refine ⟨old, hold, hw.1.trans hr, hw.2.1.trans hp, by have := hw.2.2; omega, ?_⟩
    rcases hguard with h | ⟨h, hroot⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, by have := hw.2.2; omega⟩
  · intro ha
    exact ⟨a, ha, rfl, rfl, Nat.le_refl _⟩

theorem generatedSeam_mem_iff (e : Entry) (len b : Nat) (a : Entry) :
    a ∈ generatedSeam e len b ↔
      a.row < move e.parent len b e.row ∧
      a.parent = move e.parent len b e.parent ∧ a.root ≤ e.parent + (b+1)*len := by
  simp only [generatedSeam, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, hk, q, hq, he⟩
    subst a
    exact ⟨hk, rfl, Nat.le_of_lt_succ hq⟩
  · rintro ⟨hk, hp, hq⟩
    exact ⟨a.row, hk, a.root, by omega, by cases a; simp_all⟩

theorem generatedSeam_weakening (e : Entry) (len b : Nat) (a : Entry) :
    (∃ s ∈ generatedSeam e len b, Weakened a s) ↔ a ∈ generatedSeam e len b := by
  constructor
  · rintro ⟨s, hs, hr, hp, hq⟩
    obtain ⟨hsk, hsp, hsq⟩ := (generatedSeam_mem_iff e len b s).mp hs
    exact (generatedSeam_mem_iff e len b a).mpr
      ⟨by rwa [hr], hp.trans hsp, Nat.le_trans hq hsq⟩
  · intro ha
    exact ⟨a, ha, rfl, rfl, Nat.le_refl _⟩

theorem seam_weakening_iff (last : Column) (e : Entry) (len b : Nat) (a : Entry) :
    (∃ s ∈ ordinarySeam last e len b ++ generatedSeam e len b, Weakened a s) ↔
      a ∈ ordinarySeam last e len b ∨ a ∈ generatedSeam e len b := by
  simp only [List.mem_append, or_and_right, exists_or,
    ordinarySeam_weakening, generatedSeam_weakening]

/-- A literal numerical edge specification: no block, seam, expand, or
normalization function appears in this definition. -/
def PaperEdge (g : Graph) (e : Entry) (n j : Nat) (a : Entry) : Prop :=
  (∃ b, b ≤ n ∧ ∃ i, i < g.length - 1 ∧ ∃ s ∈ g[i]?.getD [],
    j = move e.parent (g.length-1-e.parent) b i ∧
    a.row = move e.parent (g.length-1-e.parent) b s.row ∧
    a.parent = move e.parent (g.length-1-e.parent) b s.parent ∧
    a.root ≤ move e.parent (g.length-1-e.parent) b s.root) ∨
  (∃ b, b < n ∧ j = g.length-1 + b*(g.length-1-e.parent) ∧
    ((∃ s ∈ g[g.length-1]?.getD [],
      a.row = move e.parent (g.length-1-e.parent) b s.row ∧
      a.parent = move e.parent (g.length-1-e.parent) b s.parent ∧
      a.root ≤ move e.parent (g.length-1-e.parent) b s.root ∧
      (s.row < e.row ∨ (s.row = e.row ∧ a.root < move e.parent (g.length-1-e.parent) b e.root))) ∨
     (a.row < move e.parent (g.length-1-e.parent) b e.row ∧
      a.parent = move e.parent (g.length-1-e.parent) b e.parent ∧
      a.root ≤ width g e b)))

theorem finiteUnion_paper_iff (g : Graph) (e : Entry)
    (he : e.parent < g.length-1) (n j : Nat) (a : Entry) :
    FiniteUnionEdge g e n j a ↔ PaperEdge g e n j a := by
  unfold FiniteUnionEdge PaperEdge
  simp only [seam_weakening_iff]
  simp only [ordinarySeam_mem_iff, generatedSeam_mem_iff,
    Weakened, moveEntry, List.getLast?_eq_getElem?, generated_bound (g := g) (e := e) he]

theorem expand_paper_iff {g : Graph} (hg : Valid g) (hc : RootClosed g)
    {e : Entry} (he : control compare (g.getLast?.getD []) = some e)
    (n j : Nat) (a : Entry) :
    a ∈ (expand g n)[j]?.getD [] ↔ PaperEdge g e n j a := by
  rw [expand_eq_stage g he]
  exact (stage_finiteUnion_iff hg hc e (control_valid hg he).2.2 n j a).trans
    (finiteUnion_paper_iff g e (control_valid hg he).2.2 n j a)

#print axioms moveEntry_before
#print axioms normalize_mem_iff
#print axioms block_entry_iff
#print axioms stage_entry_iff
#print axioms stage_finiteUnion_iff
#print axioms ordinarySeam_weakening
#print axioms finiteUnion_paper_iff
#print axioms expand_paper_iff

end OrdinalFormal.ARD2.FiniteUnion
