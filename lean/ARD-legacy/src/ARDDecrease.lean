import ARDStructure
import OrdinalFormal.GeneratedColumnDecrease

/-! Strict column comparison decrease of the actual dynamic-row ARD expansion.
The controller uses (row,root,parent); columns use (parent,row,root).
No accessibility or ordinal interpretation is assumed in this finite theorem. -/

namespace OrdinalFormal.ARD
open Columns
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 4096

theorem columnCompare_self (c : Column) :
    listCompare (entryCompare compare) c c = .eq :=
  GeneratedColumnDecrease.columnCompare_self compare nat_compare_laws c

theorem expand_zero_lt (g : Graph) (hg : g ≠ []) : CompareLt (expand g 0) g := by
  unfold CompareLt
  rw [expand_zero, ← List.dropLast_eq_take]
  exact RPDDecrease.listCompare_dropLast_lt _ columnCompare_self g hg

def firstColumn (g : Graph) (e : Entry) : Column :=
  normalizeColumn compare
    ((g[e.parent]?.getD []).map (moveEntry e.parent (g.length-1-e.parent) 1) ++ seam g e 0)

theorem block_zero_first {g : Graph} {e : Entry}
    (he : e.parent < g.length-1) :
    ∃ tail, block g e 0 = firstColumn g e :: tail := by
  have hlen : 0 < g.length-1-e.parent := by omega
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hlen)
  unfold block firstColumn
  simp only [hm, List.range_succ_eq_map, List.map_cons, Nat.add_zero, Nat.zero_add, ite_true]
  exact ⟨_, rfl⟩

theorem expand_positive_first {g : Graph} (hg : Valid g) {e : Entry}
    (he : control compare (g.getLast?.getD []) = some e) (n : Nat) :
    ∃ tail, expand g (n+1) = g.dropLast ++ firstColumn g e :: tail := by
  obtain ⟨tail, ht⟩ := block_zero_first (control_valid hg he).2.2
  unfold expand
  rw [he, List.range_succ_eq_map]
  simp only [List.flatMap_cons, ht, List.cons_append, ← List.dropLast_eq_take]
  exact ⟨_, rfl⟩

theorem nonempty_of_control {g : Graph} {e : Entry}
    (he : control compare (g.getLast?.getD []) = some e) : g ≠ [] := by
  intro h
  subst g
  simp [Columns.control] at he

theorem expand_positive_lt_iff {g : Graph} (hg : Valid g) {e : Entry}
    (he : control compare (g.getLast?.getD []) = some e) (n : Nat) :
    CompareLt (expand g (n+1)) g ↔
      listCompare (entryCompare compare) (firstColumn g e) (g.getLast?.getD []) = .lt := by
  obtain ⟨tail, ht⟩ := expand_positive_first hg he n
  have hn := nonempty_of_control he
  have hlast : g.getLast?.getD [] = g.getLast hn := by simp [List.getLast?_eq_some_getLast hn]
  rw [ht, hlast]
  have hc := RPDDecrease.listCompare_append_left _ columnCompare_self g.dropLast
    (firstColumn g e :: tail) [g.getLast hn]
  rw [List.dropLast_concat_getLast hn] at hc
  unfold CompareLt graphCompare
  rw [hc]
  simp only [listCompare, Comparison.thenCompare_lt_iff]
  cases tail <;> simp [listCompare]

theorem move_source_cut_eq {g : Graph} (hg : Valid g) (c len b : Nat)
    {a : Entry} (ha : a ∈ g[c]?.getD []) : moveEntry c len b a = a := by
  have hv := hg c a ha
  have hr : a.root < c := by omega
  cases a
  simp_all [moveEntry, move]

theorem firstColumn_source_unmoved {g : Graph} (hg : Valid g) (e : Entry) :
    firstColumn g e = normalizeColumn compare (g[e.parent]?.getD [] ++ seam g e 0) := by
  unfold firstColumn
  have h := List.map_congr_left (fun a ha => move_source_cut_eq hg e.parent
    (g.length-1-e.parent) 1 (a := a) ha)
  simp only [List.map_id_fun', id_eq] at h
  rw [h]

theorem firstSeam_entry {g : Graph} (hclosed : RootClosed g)
    (hn : g ≠ []) (e : Entry) (len : Nat) {a : Entry}
    (ha : a ∈ ordinarySeam (g.getLast?.getD []) e len 0) :
    a ∈ g.getLast?.getD [] ∧
      (a.row < e.row ∨ (a.row = e.row ∧ a.root < e.root)) := by
  obtain ⟨s, hs, hm⟩ := List.mem_flatMap.mp ha
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
  have hfilter := (List.mem_filter.mp hq).2
  have hrange := List.mem_range.mp (List.mem_filter.mp hq).1
  simp only [RPDDecrease.move_zero, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq, decide_eq_true_eq] at hfilter hrange ⊢
  refine ⟨?_, hfilter⟩
  have hlast : g.getLast?.getD [] = g.getLast hn := by simp [List.getLast?_eq_some_getLast hn]
  rw [hlast] at hs ⊢
  exact hclosed _ (List.getLast_mem hn) s hs q (by omega)

/-- The new first column contains only old atoms, atoms with lower parent,
or atoms at the control parent whose row is strictly below the control row. -/
theorem firstColumn_entry {g : Graph} (hg : Valid g) (hclosed : RootClosed g)
    (hn : g ≠ []) (e : Entry) {a : Entry} (ha : a ∈ firstColumn g e) :
    a.parent < e.parent ∨
      (a ∈ g.getLast?.getD [] ∧
        (a.row < e.row ∨ (a.row = e.row ∧ a.root < e.root))) ∨
      (a.parent = e.parent ∧ a.row < e.row) := by
  rw [firstColumn_source_unmoved hg e] at ha
  obtain ⟨s, hs, hr, hp, hq⟩ := ColumnRepresentation.mem_normalizeColumn_source compare ha
  rcases List.mem_append.mp hs with hs | hs
  · exact Or.inl (hp ▸ (hg e.parent s hs).2.2)
  · rcases List.mem_append.mp hs with hs | hs
    · have hs' := firstSeam_entry hclosed hn e _ hs
      apply Or.inr ∘ Or.inl
      have hlast : g.getLast?.getD [] = g.getLast hn := by simp [List.getLast?_eq_some_getLast hn]
      have hsmem := hs'.1
      rw [hlast] at hsmem
      have hamem := hclosed _ (List.getLast_mem hn) s hsmem a.root hq
      have hae : {s with root := a.root} = a := by cases a; cases s; simp_all
      refine ⟨?_, ?_⟩
      · rw [hlast, ← hae]
        exact hamem
      · rcases hs'.2 with hl | ⟨heq, hlt⟩
        · exact Or.inl (hr ▸ hl)
        · exact Or.inr ⟨hr.trans heq, Nat.lt_of_le_of_lt hq hlt⟩
    · obtain ⟨low, hlow, hm⟩ := List.mem_flatMap.mp hs
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp hm
      apply Or.inr ∘ Or.inr
      refine ⟨?_, ?_⟩
      · simpa only [RPDDecrease.move_zero] using hp
      · rw [hr]
        simpa only [RPDDecrease.move_zero, List.mem_range] using hlow

theorem controller_not_firstColumn {g : Graph} (hg : Valid g)
    (hclosed : RootClosed g) (hn : g ≠ []) (e : Entry) : e ∉ firstColumn g e := by
  intro he
  have h := firstColumn_entry hg hclosed hn e he
  rcases h with hp | ⟨_, hr | ⟨_, hq⟩⟩ | ⟨_, hr⟩ <;> omega

theorem firstColumn_new_below_control {g : Graph} (hg : Valid g)
    (hclosed : RootClosed g) (hn : g ≠ []) {e a : Entry}
    (ha : a ∈ firstColumn g e) (hnew : a ∉ g.getLast?.getD []) :
    entryCompare compare a e = .lt := by
  have h := firstColumn_entry hg hclosed hn e ha
  apply (Comparison.entryCompare_lt_iff compare nat_compare_laws.eq_iff a e).mpr
  rcases h with hp | ⟨hmem, _⟩ | ⟨hp, hr⟩
  · exact Or.inl hp
  · exact False.elim (hnew hmem)
  · exact Or.inr ⟨hp, Or.inl (Nat.compare_eq_lt.mpr hr)⟩

theorem firstColumn_lt {g : Graph} (hg : Valid g) (hcan : Canonical g)
    {e : Entry} (he : control compare (g.getLast?.getD []) = some e) :
    listCompare (entryCompare compare) (firstColumn g e) (g.getLast?.getD []) = .lt := by
  have hn := nonempty_of_control he
  have hl : g.getLast?.getD [] ∈ g := by
    rw [List.getLast?_eq_some_getLast hn]
    exact List.getLast_mem hn
  apply GenericSortedColumns.compare_lt_of_deleted_pivot compare nat_compare_laws
    (GenericSortedColumns.normalize_sorted compare nat_compare_laws _) (hcan _ hl).1 e
    (ExpansionValidity.control_mem compare he)
    (controller_not_firstColumn hg (GenericSortedColumns.canonical_rootClosed compare hcan) hn e)
  intro z hz hnew
  exact firstColumn_new_below_control hg
    (GenericSortedColumns.canonical_rootClosed compare hcan) hn hz hnew

/-- Every actual ARD expansion strictly lowers the column comparator.
The only hypotheses are finite validity, canonical presentation and nonemptiness. -/
theorem expand_lt {g : Graph} (hg : Valid g) (hcan : Canonical g) (hn : g ≠ [])
    (n : Nat) : CompareLt (expand g n) g := by
  cases he : control compare (g.getLast?.getD []) with
  | none =>
    have hfs : expand g n = expand g 0 := by simp [expand, he]
    rw [hfs]
    exact expand_zero_lt g hn
  | some e =>
    cases n with
    | zero => exact expand_zero_lt g hn
    | succ n => exact (expand_positive_lt_iff hg he n).mpr (firstColumn_lt hg hcan he)

#print axioms move_source_cut_eq
#print axioms firstColumn_entry
#print axioms firstColumn_lt
#print axioms expand_lt

end OrdinalFormal.ARD
