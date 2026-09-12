import OrdinalFormal.RPD
import OrdinalFormal.Comparison
import OrdinalFormal.ExpansionValidity
import OrdinalFormal.ColumnRepresentation

/-!
# Concrete one-step comparison: proved reductions and remaining obligation

Deletion strictly decreases every nonempty raw graph. For positive indices the
actual expansion is reduced exactly to comparing its first appended column with
the old last column. This reduction is NOT a proof that that column is smaller;
the latter needs the genuine canonical-domain/controller/seam invariant.
-/

namespace OrdinalFormal.RPDDecrease

set_option autoImplicit false
set_option maxHeartbeats 600000

universe u
open Columns
variable {α : Type u}

theorem listCompare_append_left (cmp : α → α → Ordering)
    (hSelf : ∀ a, cmp a a = .eq) (pre a b : List α) :
    listCompare cmp (pre ++ a) (pre ++ b) = listCompare cmp a b := by
  induction pre with
  | nil => rfl
  | cons p ps ih => simp only [List.cons_append, listCompare, hSelf, thenCompare, ih]

theorem listCompare_dropLast_lt (cmp : α → α → Ordering)
    (hSelf : ∀ a, cmp a a = .eq) (as : List α) (ha : as ≠ []) :
    listCompare cmp as.dropLast as = .lt := by
  have h := listCompare_append_left cmp hSelf as.dropLast [] [as.getLast ha]
  rw [List.append_nil, List.dropLast_concat_getLast ha] at h
  exact h

theorem columnCompare_self (c : Column Nat) :
    listCompare (entryCompare compare) c c = .eq :=
  (Comparison.listCompare_eq_iff _
    (Comparison.entryCompare_eq_iff compare (fun _ _ => Nat.compare_eq_eq)) c c).mpr rfl

theorem rpd_fs_zero_lt (g : RPD.Diagram) (hg : g ≠ []) :
    RPD.cmp (RPD.fs g 0) g = .lt := by
  rw [RPD.fs_zero, ← List.dropLast_eq_take]
  exact listCompare_dropLast_lt _ columnCompare_self g hg

/-- The literal first new column of the first block. There are no generated
rows in RPD. Source movement is retained here so this definition is exact even
before geometric validity has been used. -/
def firstColumn (g : RPD.Diagram) (e : Entry Nat) : Column Nat :=
  let len := g.length - 1 - e.parent
  normalizeColumn compare
    ((g[e.parent]?.getD []).map (moveEntry e.parent len 1) ++
      ordinarySeam compare (g.getLast?.getD []) e len 0)

theorem block_zero_first {g : RPD.Diagram} {e : Entry Nat}
    (he : e.parent < g.length - 1) :
    ∃ tail, block compare (fun _ _ => []) g e 0 = firstColumn g e :: tail := by
  have hlen : 0 < g.length - 1 - e.parent := by omega
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hlen)
  unfold block firstColumn
  simp only [hm, List.range_succ_eq_map, List.map_cons, Nat.add_zero, Nat.zero_add,
    ite_true, generatedSeam, List.flatMap_nil, List.append_nil]
  exact ⟨_, rfl⟩

theorem fs_positive_first {g : RPD.Diagram} (hg : Valid g) {e : Entry Nat}
    (he : Columns.control compare (g.getLast?.getD []) = some e) (n : Nat) :
    ∃ tail, RPD.fs g (n + 1) = g.dropLast ++ firstColumn g e :: tail := by
  obtain ⟨tail, ht⟩ := block_zero_first (ExpansionValidity.control_valid compare hg he).2
  unfold RPD.fs expand
  rw [he, List.range_succ_eq_map]
  simp only [List.flatMap_cons, ht, List.cons_append, ← List.dropLast_eq_take]
  exact ⟨_, rfl⟩

theorem nonempty_of_control {g : RPD.Diagram} {e : Entry Nat}
    (he : Columns.control compare (g.getLast?.getD []) = some e) : g ≠ [] := by
  intro h
  subst g
  simp [Columns.control] at he

/-- Exact positive-index reduction. No claim that its RHS already holds. -/
theorem rpd_fs_positive_lt_iff {g : RPD.Diagram} (hg : Valid g) {e : Entry Nat}
    (he : Columns.control compare (g.getLast?.getD []) = some e) (n : Nat) :
    RPD.cmp (RPD.fs g (n + 1)) g = .lt ↔
      listCompare (entryCompare compare) (firstColumn g e) (g.getLast?.getD []) = .lt := by
  obtain ⟨tail, ht⟩ := fs_positive_first hg he n
  have hn := nonempty_of_control he
  have hlast : g.getLast?.getD [] = g.getLast hn := by simp [List.getLast?_eq_some_getLast hn]
  rw [ht, hlast]
  change graphCompare compare (g.dropLast ++ firstColumn g e :: tail) g = .lt ↔ _
  have hc := listCompare_append_left _ columnCompare_self g.dropLast
    (firstColumn g e :: tail) [g.getLast hn]
  rw [List.dropLast_concat_getLast hn] at hc
  unfold graphCompare
  rw [hc]
  simp only [listCompare, Comparison.thenCompare_lt_iff]
  cases tail <;> simp [listCompare]

@[simp] theorem move_zero (cut len i : Nat) : move cut len 0 i = i := by
  simp [move]

theorem move_source_cut_eq {g : RPD.Diagram} (hg : Valid g) (cut len b : Nat)
    {a : Entry Nat} (ha : a ∈ g[cut]?.getD []) : moveEntry cut len b a = a := by
  have hv := hg cut a ha
  have hr : a.root < cut := by omega
  cases a
  simp_all [moveEntry, move]

theorem firstColumn_source_unmoved {g : RPD.Diagram} (hg : Valid g) (e : Entry Nat) :
    firstColumn g e = normalizeColumn compare
      ((g[e.parent]?.getD []) ++
        ordinarySeam compare (g.getLast?.getD []) e (g.length - 1 - e.parent) 0) := by
  unfold firstColumn
  dsimp only
  have h := List.map_congr_left (fun a ha => move_source_cut_eq hg e.parent
    (g.length - 1 - e.parent) 1 (a := a) ha)
  simp only [List.map_id_fun', id_eq] at h
  rw [h]

/-- In the first seam, every entry is an old entry (using root closure),
and it has a strictly smaller controller-row/root pair. -/
theorem firstSeam_entry {g : RPD.Diagram} (hclosed : RootClosed g)
    (hn : g ≠ []) (e : Entry Nat) (len : Nat) {a : Entry Nat}
    (ha : a ∈ ordinarySeam compare (g.getLast?.getD []) e len 0) :
    a ∈ g.getLast?.getD [] ∧
      (a.row < e.row ∨ (a.row = e.row ∧ a.root < e.root)) := by
  obtain ⟨s, hs, hm⟩ := List.mem_flatMap.mp ha
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
  have hfilter := (List.mem_filter.mp hq).2
  have hrange := List.mem_range.mp (List.mem_filter.mp hq).1
  simp only [move_zero, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq, Nat.compare_eq_lt, Nat.compare_eq_eq] at hfilter hrange ⊢
  refine ⟨?_, hfilter⟩
  have hlast : g.getLast?.getD [] = g.getLast hn := by simp [List.getLast?_eq_some_getLast hn]
  rw [hlast] at hs ⊢
  exact hclosed _ (List.getLast_mem hn) s hs q (by omega)

/-- Every normalized entry either lies strictly to the left of the control
parent, or is a retained old entry with lower controller row/root.
This explicitly handles the mismatch between control priority and column order. -/
theorem firstColumn_entry {g : RPD.Diagram} (hg : Valid g) (hclosed : RootClosed g)
    (hn : g ≠ []) (e : Entry Nat) {a : Entry Nat} (ha : a ∈ firstColumn g e) :
    a.parent < e.parent ∨
      (a ∈ g.getLast?.getD [] ∧
        (a.row < e.row ∨ (a.row = e.row ∧ a.root < e.root))) := by
  rw [firstColumn_source_unmoved hg e] at ha
  obtain ⟨s, hs, hr, hp, hq⟩ := ColumnRepresentation.mem_normalizeColumn_source compare ha
  rcases List.mem_append.mp hs with hs | hs
  · exact Or.inl (hp ▸ (hg e.parent s hs).2)
  · have hs' := firstSeam_entry hclosed hn e _ hs
    apply Or.inr
    have hlast : g.getLast?.getD [] = g.getLast hn := by simp [List.getLast?_eq_some_getLast hn]
    have hsmem := hs'.1
    rw [hlast] at hsmem
    have hamem := hclosed _ (List.getLast_mem hn) s hsmem a.root hq
    have hae : {s with root := a.root} = a := by
      cases a
      cases s
      simp_all
    refine ⟨?_, ?_⟩
    · rw [hlast, ← hae]
      exact hamem
    · rcases hs'.2 with hl | ⟨heq, hlt⟩
      · exact Or.inl (hr ▸ hl)
      · exact Or.inr ⟨hr.trans heq, Nat.lt_of_le_of_lt hq hlt⟩

theorem controller_not_firstColumn {g : RPD.Diagram} (hg : Valid g)
    (hclosed : RootClosed g) (e : Entry Nat) : e ∉ firstColumn g e := by
  intro he
  have hn : g ≠ [] := by
    intro hnil
    subst g
    simp [firstColumn, ordinarySeam, normalizeColumn, sortDescending, dedupSorted] at he
  have h := firstColumn_entry hg hclosed hn e he
  rcases h with hp | ⟨_, hr | ⟨_, hq⟩⟩ <;> omega

theorem mem_dedupSorted_iff (c : Column Nat) (e : Entry Nat) :
    e ∈ dedupSorted compare c ↔ e ∈ c := by
  induction c with
  | nil => rfl
  | cons a as ih =>
      cases hd : dedupSorted compare as with
      | nil =>
          simp only [dedupSorted, hd, List.mem_cons, List.not_mem_nil, or_false]
          have hn : ¬e ∈ as := by simpa [hd] using ih.symm
          simp [hn]
      | cons b bs =>
          simp only [dedupSorted, hd]
          split
          · rename_i hab
            have hab' : a = b :=
              (Comparison.entryCompare_eq_iff compare (fun _ _ => Nat.compare_eq_eq) a b).mp
                (beq_iff_eq.mp hab)
            subst a
            have hi : e ∈ b :: bs ↔ e ∈ as := by simpa [hd] using ih
            simp only [List.mem_cons] at hi ⊢
            rw [← hi]
            simp
          · simp only [List.mem_cons, ← hd, ih]

theorem mem_normalizeColumn_of_mem {c : Column Nat} {e : Entry Nat}
    (he : e ∈ c) : e ∈ normalizeColumn compare c := by
  apply (mem_dedupSorted_iff _ e).mpr
  apply (ColumnRepresentation.mem_sortDescending compare e _).mpr
  apply List.mem_flatMap.mpr
  refine ⟨e, he, List.mem_map.mpr ⟨e.root, List.mem_range.mpr (Nat.lt_succ_self _), ?_⟩⟩
  cases e
  rfl

theorem firstSeam_retains {g : RPD.Diagram} (e : Entry Nat) (len : Nat)
    {a : Entry Nat} (ha : a ∈ g.getLast?.getD [])
    (hguard : a.row < e.row ∨ (a.row = e.row ∧ a.root < e.root)) :
    a ∈ ordinarySeam compare (g.getLast?.getD []) e len 0 := by
  apply List.mem_flatMap.mpr
  refine ⟨a, ha, List.mem_map.mpr ⟨a.root, ?_, ?_⟩⟩
  · apply List.mem_filter.mpr
    constructor
    · simp only [move_zero]
      exact List.mem_range.mpr (Nat.lt_succ_self _)
    · simpa only [move_zero, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq, Nat.compare_eq_lt, Nat.compare_eq_eq] using hguard
  · simp only [move_zero]

theorem firstColumn_retains {g : RPD.Diagram} (hg : Valid g) (e : Entry Nat)
    {a : Entry Nat} (ha : a ∈ g.getLast?.getD [])
    (hguard : a.row < e.row ∨ (a.row = e.row ∧ a.root < e.root)) :
    a ∈ firstColumn g e := by
  rw [firstColumn_source_unmoved hg e]
  exact mem_normalizeColumn_of_mem (List.mem_append.mpr (Or.inr (firstSeam_retains e _ ha hguard)))

def ControlBound (e a : Entry Nat) : Prop :=
  a.row ≤ e.row ∧ (a.row = e.row → a.root ≤ e.root) ∧
    (a.row = e.row → a.root = e.root → a.parent ≤ e.parent)

theorem controlCompare_lt_iff (a b : Entry Nat) :
    controlCompare compare a b = .lt ↔
      a.row < b.row ∨ (a.row = b.row ∧
        (a.root < b.root ∨ (a.root = b.root ∧ a.parent < b.parent))) := by
  simp only [controlCompare, Comparison.thenCompare_lt_iff, Nat.compare_eq_lt,
    Nat.compare_eq_eq]

theorem controlBound_of_lt {a b : Entry Nat} (h : controlCompare compare a b = .lt) :
    ControlBound b a := by
  have h' := (controlCompare_lt_iff a b).mp h
  unfold ControlBound
  omega

theorem controlBound_of_not_lt {a b : Entry Nat} (h : controlCompare compare a b ≠ .lt) :
    ControlBound a b := by
  have h' : ¬(a.row < b.row ∨ (a.row = b.row ∧
      (a.root < b.root ∨ (a.root = b.root ∧ a.parent < b.parent)))) :=
    fun hlt => h ((controlCompare_lt_iff a b).mpr hlt)
  unfold ControlBound
  omega

theorem controlBound_refl (a : Entry Nat) : ControlBound a a := by
  simp [ControlBound]

theorem controlBound_trans {a b c : Entry Nat}
    (hab : ControlBound a b) (hbc : ControlBound b c) : ControlBound a c := by
  unfold ControlBound at *
  omega

theorem controlFold_bound (c : Column Nat) (a : Entry Nat) :
    ∀ x ∈ a :: c,
      ControlBound (c.foldl (fun a b => if controlCompare compare a b == .lt then b else a) a) x := by
  induction c generalizing a with
  | nil =>
      intro x hx
      have hxa := List.mem_singleton.mp hx
      subst x
      exact controlBound_refl a
  | cons b bs ih =>
      simp only [List.foldl_cons]
      split
      · rename_i hab
        intro x hx
        rcases List.mem_cons.mp hx with hx | hx
        · subst x
          exact controlBound_trans (ih b b List.mem_cons_self)
            (controlBound_of_lt (beq_iff_eq.mp hab))
        · exact ih b x hx
      · rename_i hab
        intro x hx
        rcases List.mem_cons.mp hx with hx | hx
        · subst x
          exact ih a a List.mem_cons_self
        · rcases List.mem_cons.mp hx with hx | hx
          · subst x
            exact controlBound_trans (ih a a List.mem_cons_self)
              (controlBound_of_not_lt (fun h => hab (beq_iff_eq.mpr h)))
          · exact ih a x (List.mem_cons_of_mem a hx)

theorem control_bound {c : Column Nat} {e : Entry Nat}
    (he : Columns.control compare c = some e) : ∀ a ∈ c, ControlBound e a := by
  cases c with
  | nil => simp [Columns.control] at he
  | cons a as =>
      simp only [Columns.control, Option.some.injEq] at he
      rw [← he]
      exact controlFold_bound as a

/-- Every old entry above the deleted controller in parent-first column order
is retained, despite controller selection using row-first priority. -/
theorem firstColumn_retains_above_control {g : RPD.Diagram} (hg : Valid g)
    {e a : Entry Nat} (he : Columns.control compare (g.getLast?.getD []) = some e)
    (ha : a ∈ g.getLast?.getD []) (hlt : entryCompare compare e a = .lt) :
    a ∈ firstColumn g e := by
  have hb := control_bound he a ha
  have ho := (Comparison.entryCompare_lt_iff compare (fun _ _ => Nat.compare_eq_eq) e a).mp hlt
  simp only [Nat.compare_eq_lt] at ho
  apply firstColumn_retains hg e ha
  unfold ControlBound at hb
  omega

theorem firstColumn_new_below_control {g : RPD.Diagram} (hg : Valid g)
    (hclosed : RootClosed g) (hn : g ≠ []) {e a : Entry Nat}
    (ha : a ∈ firstColumn g e) (hnew : a ∉ g.getLast?.getD []) :
    entryCompare compare a e = .lt := by
  have h := firstColumn_entry hg hclosed hn e ha
  apply (Comparison.entryCompare_lt_iff compare (fun _ _ => Nat.compare_eq_eq) a e).mpr
  rcases h with h | ⟨h, _⟩
  · exact Or.inl h
  · exact False.elim (hnew h)

#print axioms rpd_fs_zero_lt
#print axioms rpd_fs_positive_lt_iff
#print axioms controller_not_firstColumn
#print axioms firstColumn_retains
#print axioms firstColumn_retains_above_control

end OrdinalFormal.RPDDecrease
