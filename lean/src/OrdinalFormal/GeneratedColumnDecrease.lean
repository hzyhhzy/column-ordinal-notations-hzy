import OrdinalFormal.GenericSortedColumns
import OrdinalFormal.RPDDecrease

/-!
# Strict column-order decrease of actual generated-row expansion

Generalized from the local RPD decrease and deleted-pivot proofs. No semantic
representation, accessibility, control-maximality, or first-column-decrease
assumption is used. The package contributes only genuinely lower rows.
-/

namespace OrdinalFormal.GeneratedColumnDecrease

open Columns GenericSortedColumns
set_option autoImplicit false
set_option maxHeartbeats 700000
universe u
variable {Row : Type u}
variable (cmp : Row → Row → Ordering) (laws : CompareLaws cmp)
variable (package : Package Row)

include laws in
theorem columnCompare_self (c : Column Row) :
    listCompare (entryCompare cmp) c c = .eq :=
  (Comparison.listCompare_eq_iff _ (Comparison.entryCompare_eq_iff cmp laws.eq_iff) c c).mpr rfl

include laws in
theorem expand_zero_lt (g : Graph Row) (hg : g ≠ []) :
    graphCompare cmp (expand cmp package g 0) g = .lt := by
  rw [expand_zero, ← List.dropLast_eq_take]
  exact RPDDecrease.listCompare_dropLast_lt _ (columnCompare_self cmp laws) g hg

def firstColumn (g : Graph Row) (e : Entry Row) : Column Row :=
  let len := g.length - 1 - e.parent
  normalizeColumn cmp
    ((g[e.parent]?.getD []).map (moveEntry e.parent len 1) ++
      (ordinarySeam cmp (g.getLast?.getD []) e len 0 ++ generatedSeam package e len 0))

theorem block_zero_first {g : Graph Row} {e : Entry Row}
    (he : e.parent < g.length - 1) :
    ∃ tail, block cmp package g e 0 = firstColumn cmp package g e :: tail := by
  have hlen : 0 < g.length - 1 - e.parent := by omega
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hlen)
  unfold block firstColumn
  simp only [hm, List.range_succ_eq_map, List.map_cons, Nat.add_zero, Nat.zero_add, ite_true]
  exact ⟨_, rfl⟩

theorem expand_positive_first {g : Graph Row} (hg : Valid g) {e : Entry Row}
    (he : Columns.control cmp (g.getLast?.getD []) = some e) (n : Nat) :
    ∃ tail, expand cmp package g (n + 1) = g.dropLast ++ firstColumn cmp package g e :: tail := by
  obtain ⟨tail, ht⟩ := block_zero_first cmp package (ExpansionValidity.control_valid cmp hg he).2
  unfold expand
  rw [he, List.range_succ_eq_map]
  simp only [List.flatMap_cons, ht, List.cons_append, ← List.dropLast_eq_take]
  exact ⟨_, rfl⟩

theorem nonempty_of_control {g : Graph Row} {e : Entry Row}
    (he : Columns.control cmp (g.getLast?.getD []) = some e) : g ≠ [] := by
  intro h
  subst g
  simp [Columns.control] at he

include laws in
theorem expand_positive_lt_iff {g : Graph Row} (hg : Valid g) {e : Entry Row}
    (he : Columns.control cmp (g.getLast?.getD []) = some e) (n : Nat) :
    graphCompare cmp (expand cmp package g (n + 1)) g = .lt ↔
      listCompare (entryCompare cmp) (firstColumn cmp package g e) (g.getLast?.getD []) = .lt := by
  obtain ⟨tail, ht⟩ := expand_positive_first cmp package hg he n
  have hn := nonempty_of_control cmp he
  have hlast : g.getLast?.getD [] = g.getLast hn := by simp [List.getLast?_eq_some_getLast hn]
  rw [ht, hlast]
  have hc := RPDDecrease.listCompare_append_left _ (columnCompare_self cmp laws) g.dropLast
    (firstColumn cmp package g e :: tail) [g.getLast hn]
  rw [List.dropLast_concat_getLast hn] at hc
  unfold graphCompare
  rw [hc]
  simp only [listCompare, Comparison.thenCompare_lt_iff]
  cases tail <;> simp [listCompare]

theorem move_source_cut_eq {g : Graph Row} (hg : Valid g) (cut len b : Nat)
    {a : Entry Row} (ha : a ∈ g[cut]?.getD []) : moveEntry cut len b a = a := by
  have hv := hg cut a ha
  have hr : a.root < cut := by omega
  cases a
  simp_all [moveEntry, move]

theorem firstColumn_source_unmoved {g : Graph Row} (hg : Valid g) (e : Entry Row) :
    firstColumn cmp package g e = normalizeColumn cmp
      ((g[e.parent]?.getD []) ++
        (ordinarySeam cmp (g.getLast?.getD []) e (g.length - 1 - e.parent) 0 ++
          generatedSeam package e (g.length - 1 - e.parent) 0)) := by
  unfold firstColumn
  dsimp only
  have h := List.map_congr_left (fun a ha => move_source_cut_eq hg e.parent
    (g.length - 1 - e.parent) 1 (a := a) ha)
  simp only [List.map_id_fun', id_eq] at h
  rw [h]

include laws in
theorem firstSeam_entry {g : Graph Row} (hclosed : RootClosed g)
    (hn : g ≠ []) (e : Entry Row) (len : Nat) {a : Entry Row}
    (ha : a ∈ ordinarySeam cmp (g.getLast?.getD []) e len 0) :
    a ∈ g.getLast?.getD [] ∧
      (cmp a.row e.row = .lt ∨ (a.row = e.row ∧ a.root < e.root)) := by
  obtain ⟨s, hs, hm⟩ := List.mem_flatMap.mp ha
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
  have hfilter := (List.mem_filter.mp hq).2
  have hrange := List.mem_range.mp (List.mem_filter.mp hq).1
  simp only [RPDDecrease.move_zero, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq, laws.eq_iff] at hfilter hrange ⊢
  refine ⟨?_, hfilter⟩
  have hlast : g.getLast?.getD [] = g.getLast hn := by simp [List.getLast?_eq_some_getLast hn]
  rw [hlast] at hs ⊢
  exact hclosed _ (List.getLast_mem hn) s hs q (by omega)

variable (hPackage : ∀ high b low, low ∈ package high b → cmp low high = .lt)
include laws hPackage

/-- The three real origins after normalization: source left of the cut,
ordinary old seam, or generated row at the cut with strictly lower row. -/
theorem firstColumn_entry {g : Graph Row} (hg : Valid g) (hclosed : RootClosed g)
    (hn : g ≠ []) (e : Entry Row) {a : Entry Row}
    (ha : a ∈ firstColumn cmp package g e) :
    a.parent < e.parent ∨
      (a ∈ g.getLast?.getD [] ∧
        (cmp a.row e.row = .lt ∨ (a.row = e.row ∧ a.root < e.root))) ∨
      (a.parent = e.parent ∧ cmp a.row e.row = .lt) := by
  rw [firstColumn_source_unmoved cmp package hg e] at ha
  obtain ⟨s, hs, hr, hp, hq⟩ := ColumnRepresentation.mem_normalizeColumn_source cmp ha
  rcases List.mem_append.mp hs with hs | hs
  · exact Or.inl (hp ▸ (hg e.parent s hs).2)
  · rcases List.mem_append.mp hs with hs | hs
    · have hs' := firstSeam_entry cmp laws hclosed hn e _ hs
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
        exact hPackage e.row 0 low hlow

theorem controller_not_firstColumn {g : Graph Row} (hg : Valid g)
    (hclosed : RootClosed g) (hn : g ≠ []) (e : Entry Row) :
    e ∉ firstColumn cmp package g e := by
  intro he
  have h := firstColumn_entry cmp laws package hPackage hg hclosed hn e he
  have hself : cmp e.row e.row = .eq := (laws.eq_iff _ _).mpr rfl
  rcases h with hp | ⟨_, hr | ⟨_, hq⟩⟩ | ⟨_, hr⟩
  · omega
  · rw [hself] at hr
    contradiction
  · omega
  · rw [hself] at hr
    contradiction

theorem firstColumn_new_below_control {g : Graph Row} (hg : Valid g)
    (hclosed : RootClosed g) (hn : g ≠ []) {e a : Entry Row}
    (ha : a ∈ firstColumn cmp package g e) (hnew : a ∉ g.getLast?.getD []) :
    entryCompare cmp a e = .lt := by
  have h := firstColumn_entry cmp laws package hPackage hg hclosed hn e ha
  apply (Comparison.entryCompare_lt_iff cmp laws.eq_iff a e).mpr
  rcases h with hp | ⟨hmem, _⟩ | ⟨hp, hr⟩
  · exact Or.inl hp
  · exact False.elim (hnew hmem)
  · exact Or.inr ⟨hp, Or.inl hr⟩

theorem firstColumn_lt {g : Graph Row} (hg : Valid g) (hcan : Canonical cmp g)
    {e : Entry Row} (he : Columns.control cmp (g.getLast?.getD []) = some e) :
    listCompare (entryCompare cmp) (firstColumn cmp package g e) (g.getLast?.getD []) = .lt := by
  have hn := nonempty_of_control cmp he
  have hl : g.getLast?.getD [] ∈ g := by
    rw [List.getLast?_eq_some_getLast hn]
    exact List.getLast_mem hn
  apply compare_lt_of_deleted_pivot cmp laws (normalize_sorted cmp laws _) (hcan _ hl).1 e
    (ExpansionValidity.control_mem cmp he)
    (controller_not_firstColumn cmp laws package hPackage hg (canonical_rootClosed cmp hcan) hn e)
  intro z hz hnew
  exact firstColumn_new_below_control cmp laws package hPackage hg
    (canonical_rootClosed cmp hcan) hn hz hnew

/-- Full strict comparison decrease of the actual expansion, for all indices.
No well-foundedness or semantic representation premise occurs. -/
theorem expand_lt {g : Graph Row} (hg : Valid g) (hcan : Canonical cmp g) (hn : g ≠ [])
    (n : Nat) : graphCompare cmp (expand cmp package g n) g = .lt := by
  cases he : Columns.control cmp (g.getLast?.getD []) with
  | none =>
    have hfs : expand cmp package g n = expand cmp package g 0 := by simp [expand, he]
    rw [hfs]
    exact expand_zero_lt cmp laws package g hn
  | some e =>
    cases n with
    | zero => exact expand_zero_lt cmp laws package g hn
    | succ n =>
      exact (expand_positive_lt_iff cmp laws package hg he n).mpr
        (firstColumn_lt cmp laws package hPackage hg hcan he)

#check expand_lt
#print axioms firstColumn_entry
#print axioms expand_lt

end OrdinalFormal.GeneratedColumnDecrease
