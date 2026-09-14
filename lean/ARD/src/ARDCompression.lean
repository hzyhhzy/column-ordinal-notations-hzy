import ARDStructure
import OrdinalFormal.RPDFiniteUnion

/-! Exact comparison and controller bridge from compressed maximum-root lists
to the complete-root representation used by ARDCore. A compressed column is
strictly descending in (parent,row), so each group occurs at most once. -/

namespace OrdinalFormal.ARD.Compression
open Columns
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 4096

/-- One stored maximum denotes every root from that maximum down to zero. -/
def roots (a : Entry) : Column :=
  a :: ((List.range a.root).reverse.map fun q => {a with root := q})

def fullRoots (c : Column) : Column := c.flatMap roots

/-- Descending group keys encode both ordering and uniqueness of groups. -/
def Compressed (c : Column) : Prop := c.Pairwise fun a b =>
  b.parent < a.parent ∨ (b.parent = a.parent ∧ b.row < a.row)

def UniqueGroups (c : Column) : Prop :=
  c.Pairwise fun a b => ¬ (a.parent = b.parent ∧ a.row = b.row)

/-- The group-order invariant is exactly the usual descending column order
together with having one maximum-root entry per (row,parent) group. -/
theorem compressed_iff_sorted_unique (c : Column) :
    Compressed c ↔ GenericSortedColumns.Sorted compare c ∧ UniqueGroups c := by
  constructor
  · intro hc
    constructor
    · apply hc.imp
      intro a b hab
      apply (GenericSortedColumns.lt_iff compare nat_compare_laws b a).mpr
      rcases hab with hp | ⟨hp, hr⟩
      · exact Or.inl hp
      · exact Or.inr ⟨hp, Or.inl (Nat.compare_eq_lt.mpr hr)⟩
    · apply hc.imp
      intro a b hab
      omega
  · rintro ⟨hs, hu⟩
    apply (hs.and hu).imp
    intro a b ⟨hab, hne⟩
    have h := (GenericSortedColumns.lt_iff compare nat_compare_laws b a).mp hab
    simp only [Nat.compare_eq_lt] at h
    omega

theorem mem_roots_iff (a s : Entry) :
    a ∈ roots s ↔ a.row = s.row ∧ a.parent = s.parent ∧ a.root ≤ s.root := by
  constructor
  · intro ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨rfl, rfl, Nat.le_refl _⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
      have hq' : q < s.root := List.mem_range.mp (List.mem_reverse.mp hq)
      exact ⟨rfl, rfl, Nat.le_of_lt hq'⟩
  · rintro ⟨hr, hp, hq⟩
    by_cases he : a.root = s.root
    · have has : a = s := by cases a; cases s; simp_all
      exact List.mem_cons.mpr (Or.inl has)
    · apply List.mem_cons.mpr ∘ Or.inr
      apply List.mem_map.mpr
      refine ⟨a.root, List.mem_reverse.mpr (List.mem_range.mpr (by omega)), ?_⟩
      cases a; cases s; simp_all

theorem mem_fullRoots_iff (a : Entry) (c : Column) :
    a ∈ fullRoots c ↔ ∃ s ∈ c,
      a.row = s.row ∧ a.parent = s.parent ∧ a.root ≤ s.root := by
  simp only [fullRoots, List.mem_flatMap, mem_roots_iff]

theorem mem_normalize_iff (a : Entry) (c : Column) :
    a ∈ normalizeColumn compare c ↔ ∃ s ∈ c,
      a.row = s.row ∧ a.parent = s.parent ∧ a.root ≤ s.root := by
  constructor
  · exact fun ha => ColumnRepresentation.mem_normalizeColumn_source compare ha
  · rintro ⟨s, hs, hr, hp, hq⟩
    apply (GenericSortedColumns.mem_dedupSorted_iff compare nat_compare_laws _ _).mpr
    apply (ColumnRepresentation.mem_sortDescending compare _ _).mpr
    apply List.mem_flatMap.mpr
    refine ⟨s, hs, List.mem_map.mpr ⟨a.root, List.mem_range.mpr (by omega), ?_⟩⟩
    cases a; cases s; simp_all

theorem range_pairwise_lt (n : Nat) : (List.range n).Pairwise (· < ·) := by
  induction n with
  | zero => exact .nil
  | succ n ih =>
    rw [List.range_succ, List.pairwise_append]
    refine ⟨ih, by simp, ?_⟩
    intro a ha b hb
    have hb' : b = n := List.mem_singleton.mp hb
    subst b
    exact List.mem_range.mp ha

theorem roots_sorted (s : Entry) : GenericSortedColumns.Sorted compare (roots s) := by
  apply List.pairwise_cons.mpr
  constructor
  · intro a ha
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
    apply (GenericSortedColumns.lt_iff compare nat_compare_laws _ _).mpr
    exact Or.inr ⟨rfl, Or.inr ⟨rfl, List.mem_range.mp (List.mem_reverse.mp hq)⟩⟩
  · rw [List.pairwise_map, List.pairwise_reverse]
    apply (range_pairwise_lt s.root).imp
    intro q r hqr
    apply (GenericSortedColumns.lt_iff compare nat_compare_laws _ _).mpr
    exact Or.inr ⟨rfl, Or.inr ⟨rfl, hqr⟩⟩

theorem fullRoots_sorted {c : Column} (hc : Compressed c) :
    GenericSortedColumns.Sorted compare (fullRoots c) := by
  apply List.pairwise_flatMap.mpr
  refine ⟨fun s _ => roots_sorted s, ?_⟩
  apply hc.imp
  intro s t hst a ha b hb
  obtain ⟨har, hap, _⟩ := (mem_roots_iff a s).mp ha
  obtain ⟨hbr, hbp, _⟩ := (mem_roots_iff b t).mp hb
  apply (GenericSortedColumns.lt_iff compare nat_compare_laws b a).mpr
  rcases hst with hp | ⟨hp, hr⟩
  · exact Or.inl (by omega)
  · exact Or.inr ⟨by omega, Or.inl (Nat.compare_eq_lt.mpr (by omega))⟩

/-- The literal sorted full-root list, not merely equality of edge sets. -/
theorem normalize_eq_fullRoots {c : Column} (hc : Compressed c) :
    normalizeColumn compare c = fullRoots c := by
  apply RPDFiniteUnion.sorted_ext
    (GenericSortedColumns.normalize_sorted compare nat_compare_laws c) (fullRoots_sorted hc)
  intro a
  exact (mem_normalize_iff a c).trans (mem_fullRoots_iff a c).symm

theorem entryCompare_self (a : Entry) : entryCompare compare a a = .eq :=
  (Comparison.entryCompare_eq_iff compare nat_compare_laws.eq_iff a a).mpr rfl

/-- Replacing each entry by a fixed nonempty block headed by that entry
preserves the three-way lexicographic comparison, even before normalization. -/
theorem fullRoots_compare (c d : Column) :
    listCompare (entryCompare compare) (fullRoots c) (fullRoots d) =
      listCompare (entryCompare compare) c d := by
  induction c generalizing d with
  | nil => cases d <;> simp [fullRoots, roots, listCompare]
  | cons a as ih =>
    cases d with
    | nil => simp [fullRoots, roots, listCompare]
    | cons b bs =>
      by_cases hab : a = b
      · subst b
        simp only [fullRoots, List.flatMap_cons]
        rw [RPDDecrease.listCompare_append_left _ entryCompare_self]
        simpa only [listCompare, entryCompare_self, thenCompare, fullRoots] using ih bs
      · have hne : entryCompare compare a b ≠ .eq := by
          intro h
          exact hab ((Comparison.entryCompare_eq_iff compare nat_compare_laws.eq_iff a b).mp h)
        simp only [fullRoots, List.flatMap_cons, roots, List.cons_append, listCompare]
        cases hcmp : entryCompare compare a b <;> simp_all [thenCompare]

/-- Python/NER maximum-root and Lean full-root comparisons agree exactly. -/
theorem normalize_compare {c d : Column} (hc : Compressed c) (hd : Compressed d) :
    listCompare (entryCompare compare) (normalizeColumn compare c) (normalizeColumn compare d) =
      listCompare (entryCompare compare) c d := by
  rw [normalize_eq_fullRoots hc, normalize_eq_fullRoots hd, fullRoots_compare]

def CompressedGraph (g : Graph) : Prop := ∀ c ∈ g, Compressed c

theorem normalize_graphCompare {g h : Graph} (hg : CompressedGraph g) (hh : CompressedGraph h) :
    graphCompare compare (normalize compare g) (normalize compare h) = graphCompare compare g h := by
  induction g generalizing h with
  | nil => cases h <;> rfl
  | cons c cs ih =>
    cases h with
    | nil => rfl
    | cons d ds =>
      change thenCompare (listCompare (entryCompare compare) (normalizeColumn compare c)
        (normalizeColumn compare d)) (fun _ => graphCompare compare (normalize compare cs)
          (normalize compare ds)) = _
      rw [normalize_compare (hg c List.mem_cons_self) (hh d List.mem_cons_self)]
      rw [ih (fun a ha => hg a (List.mem_cons_of_mem c ha))
        (fun a ha => hh a (List.mem_cons_of_mem d ha))]
      rfl

/-- Filling lower roots never changes the row/root/parent maximum controller.
This holds for every input list, without sortedness or group uniqueness. -/
theorem control_normalize (c : Column) :
    control compare (normalizeColumn compare c) = control compare c := by
  cases hc : control compare c with
  | none =>
    cases c with
    | nil => simp [normalizeColumn, sortDescending, dedupSorted, Columns.control]
    | cons a as => simp [Columns.control] at hc
  | some e =>
    apply (RPDFiniteUnion.control_eq_paper _ e).mpr
    refine ⟨?_, ?_⟩
    · apply (mem_normalize_iff e c).mpr
      exact ⟨e, ExpansionValidity.control_mem compare hc, rfl, rfl, Nat.le_refl _⟩
    · intro a ha
      obtain ⟨s, hs, hr, hp, hq⟩ := (mem_normalize_iff a c).mp ha
      have hb := RPDDecrease.control_bound hc s hs
      unfold RPDDecrease.ControlBound at hb
      rcases hb with ⟨hrow, hroot, hparent⟩
      refine ⟨by omega, ?_, ?_⟩
      · intro heq
        have hh := hroot (by omega)
        omega
      · intro heq hreq
        have hh := hroot (by omega)
        have ht := hparent (by omega) (by omega)
        omega

#print axioms normalize_eq_fullRoots
#print axioms compressed_iff_sorted_unique
#print axioms normalize_compare
#print axioms normalize_graphCompare
#print axioms control_normalize

end OrdinalFormal.ARD.Compression
