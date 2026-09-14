import OrdinalFormal.Comparison
import OrdinalFormal.ColumnRepresentation

/-!
Canonical finite columns, generalized from the local RPDSortedColumns module: normalization produces strictly descending,
root-closed columns. These are finite order lemmas, not well-order assumptions.
-/

namespace OrdinalFormal.GenericSortedColumns
open Columns
set_option autoImplicit false
set_option maxHeartbeats 700000

universe u
variable {Row : Type u}

structure CompareLaws (cmp : Row → Row → Ordering) : Prop where
  eq_iff : ∀ a b, cmp a b = .eq ↔ a = b
  lt_trans : ∀ {a b c}, cmp a b = .lt → cmp b c = .lt → cmp a c = .lt
  trichotomy : ∀ a b, cmp a b = .lt ∨ a = b ∨ cmp b a = .lt

variable (cmp : Row → Row → Ordering)

def Lt (a b : Entry Row) : Prop := entryCompare cmp a b = .lt
def Le (a b : Entry Row) : Prop := a = b ∨ Lt cmp a b
def Sorted (c : Column Row) : Prop := c.Pairwise (fun a b => Lt cmp b a)
def WeakSorted (c : Column Row) : Prop := c.Pairwise (fun a b => Le cmp b a)

variable (laws : CompareLaws cmp)
include laws

theorem lt_iff (a b : Entry Row) : Lt cmp a b ↔
    a.parent < b.parent ∨ (a.parent = b.parent ∧
      (cmp a.row b.row = .lt ∨ (a.row = b.row ∧ a.root < b.root))) :=
  Comparison.entryCompare_lt_iff cmp laws.eq_iff a b

theorem lt_irrefl (a : Entry Row) : ¬ Lt cmp a a := by
  have h := (Comparison.entryCompare_eq_iff cmp laws.eq_iff a a).mpr rfl
  intro hlt
  change entryCompare cmp a a = .lt at hlt
  rw [h] at hlt
  contradiction

theorem lt_trans {a b c : Entry Row} (hab : Lt cmp a b) (hbc : Lt cmp b c) : Lt cmp a c :=
  Comparison.entryCompare_lt_trans cmp laws.eq_iff laws.lt_trans hab hbc

theorem lt_asymm {a b : Entry Row} (hab : Lt cmp a b) : ¬ Lt cmp b a :=
  fun hba => lt_irrefl cmp laws a (lt_trans cmp laws hab hba)

theorem trichotomy (a b : Entry Row) : Lt cmp a b ∨ a = b ∨ Lt cmp b a := by
  by_cases hp : a.parent < b.parent
  · exact Or.inl ((lt_iff cmp laws a b).mpr (Or.inl hp))
  by_cases hp' : b.parent < a.parent
  · exact Or.inr (Or.inr ((lt_iff cmp laws b a).mpr (Or.inl hp')))
  have he : a.parent = b.parent := by omega
  rcases laws.trichotomy a.row b.row with hr | hr | hr
  · exact Or.inl ((lt_iff cmp laws a b).mpr (Or.inr ⟨he, Or.inl hr⟩))
  · by_cases hq : a.root < b.root
    · exact Or.inl ((lt_iff cmp laws a b).mpr (Or.inr ⟨he, Or.inr ⟨hr, hq⟩⟩))
    by_cases hq' : b.root < a.root
    · exact Or.inr (Or.inr ((lt_iff cmp laws b a).mpr (Or.inr ⟨he.symm, Or.inr ⟨hr.symm, hq'⟩⟩)))
    apply Or.inr ∘ Or.inl
    have hqeq : a.root = b.root := by omega
    cases a
    cases b
    simp_all
  · exact Or.inr (Or.inr ((lt_iff cmp laws b a).mpr (Or.inr ⟨he.symm, Or.inl hr⟩)))

theorem le_of_not_lt {a b : Entry Row} (h : ¬ Lt cmp b a) : Le cmp a b := by
  rcases trichotomy cmp laws a b with hl | he | hl
  · exact Or.inr hl
  · exact Or.inl he
  · exact False.elim (h hl)

theorem le_trans {a b c : Entry Row} (hab : Le cmp a b) (hbc : Le cmp b c) : Le cmp a c := by
  rcases hab with rfl | hab
  · exact hbc
  rcases hbc with rfl | hbc
  · exact Or.inr hab
  · exact Or.inr (lt_trans cmp laws hab hbc)

theorem lt_of_lt_of_le {a b c : Entry Row} (hab : Lt cmp a b) (hbc : Le cmp b c) : Lt cmp a c := by
  rcases hbc with rfl | hbc
  · exact hab
  · exact lt_trans cmp laws hab hbc

theorem insert_weakSorted (a : Entry Row) {c : Column Row} (hc : WeakSorted cmp c) :
    WeakSorted cmp (insertDescending cmp a c) := by
  induction c with
  | nil => simp [insertDescending, WeakSorted]
  | cons b bs ih =>
    obtain ⟨hb, hbs⟩ := List.pairwise_cons.mp hc
    simp only [insertDescending]
    split
    · rename_i hab
      have hba : Le cmp b a := le_of_not_lt cmp laws (by simpa [Lt] using hab)
      apply List.pairwise_cons.mpr
      refine ⟨?_, hc⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hba
      · exact le_trans cmp laws (hb z hz) hba
    · rename_i hab
      have hab' : Lt cmp a b := by simpa [Lt] using hab
      apply List.pairwise_cons.mpr
      refine ⟨?_, ih hbs⟩
      intro z hz
      rcases (ColumnRepresentation.mem_insertDescending cmp z a bs).mp hz with rfl | hz
      · exact Or.inr hab'
      · exact hb z hz

theorem sort_weakSorted (c : Column Row) : WeakSorted cmp (sortDescending cmp c) := by
  induction c with
  | nil => exact .nil
  | cons a as ih => exact insert_weakSorted cmp laws a ih

theorem dedup_sorted {c : Column Row} (hc : WeakSorted cmp c) : Sorted cmp (dedupSorted cmp c) := by
  induction c with
  | nil => exact .nil
  | cons a as ih =>
    obtain ⟨ha, has⟩ := List.pairwise_cons.mp hc
    have hs := ih has
    cases hr : dedupSorted cmp as with
    | nil => simp [dedupSorted, hr, Sorted]
    | cons b bs =>
      have hrest : Sorted cmp (b :: bs) := by simpa [hr] using hs
      have hmem : ∀ z ∈ b :: bs, z ∈ as := by
        intro z hz
        exact ColumnRepresentation.mem_dedupSorted_subset cmp (by simpa [hr] using hz)
      simp only [dedupSorted, hr]
      split
      · exact hrest
      · rename_i hne
        have hab : a ≠ b := by
          intro he
          apply hne
          apply beq_iff_eq.mpr
          exact (Comparison.entryCompare_eq_iff cmp laws.eq_iff a b).mpr he
        have hba : Lt cmp b a := by
          rcases ha b (hmem b List.mem_cons_self) with he | hl
          · exact False.elim (hab he.symm)
          · exact hl
        apply List.pairwise_cons.mpr
        refine ⟨?_, hrest⟩
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hba
        · exact lt_trans cmp laws ((List.pairwise_cons.mp hrest).1 z hz) hba

theorem normalize_sorted (c : Column Row) : Sorted cmp (normalizeColumn cmp c) :=
  dedup_sorted cmp laws (sort_weakSorted cmp laws _)

theorem mem_dedupSorted_iff (c : Column Row) (e : Entry Row) :
    e ∈ dedupSorted cmp c ↔ e ∈ c := by
  induction c with
  | nil => rfl
  | cons a as ih =>
      cases hd : dedupSorted cmp as with
      | nil =>
          simp only [dedupSorted, hd, List.mem_cons, List.not_mem_nil, or_false]
          have hn : ¬e ∈ as := by simpa [hd] using ih.symm
          simp [hn]
      | cons b bs =>
          simp only [dedupSorted, hd]
          split
          · rename_i hab
            have hab' : a = b := (Comparison.entryCompare_eq_iff cmp laws.eq_iff a b).mp
              (beq_iff_eq.mp hab)
            subst a
            have hi : e ∈ b :: bs ↔ e ∈ as := by simpa [hd] using ih
            simp only [List.mem_cons] at hi ⊢
            rw [← hi]
            simp
          · simp only [List.mem_cons, ← hd, ih]

theorem normalize_rootClosed (c : Column Row) :
    ∀ e ∈ normalizeColumn cmp c, ∀ q, q ≤ e.root →
      {e with root := q} ∈ normalizeColumn cmp c := by
  intro e he q hq
  obtain ⟨s, hs, hr, hp, hroot⟩ :=
    ColumnRepresentation.mem_normalizeColumn_source cmp he
  apply (mem_dedupSorted_iff cmp laws _ _).mpr
  apply (ColumnRepresentation.mem_sortDescending cmp _ _).mpr
  apply List.mem_flatMap.mpr
  refine ⟨s, hs, List.mem_map.mpr ⟨q, List.mem_range.mpr (by omega), ?_⟩⟩
  cases e
  cases s
  simp_all

/-- Removing a pivot and adding only entries below it strictly decreases a
strictly sorted finite column. Other old entries may also be removed. -/
theorem compare_lt_of_deleted_pivot {a b : Column Row} (ha : Sorted cmp a) (hb : Sorted cmp b)
    (e : Entry Row) (he : e ∈ b) (hne : e ∉ a)
    (hnew : ∀ z ∈ a, z ∉ b → Lt cmp z e) :
    listCompare (entryCompare cmp) a b = .lt := by
  induction b generalizing a with
  | nil => simp at he
  | cons y ys ih =>
    cases a with
    | nil => rfl
    | cons x xs =>
      obtain ⟨hx, hxs⟩ := List.pairwise_cons.mp ha
      obtain ⟨hy, hys⟩ := List.pairwise_cons.mp hb
      rcases trichotomy cmp laws x y with hxy | hxy | hyx
      · change entryCompare cmp x y = .lt at hxy
        simp only [listCompare, hxy, thenCompare]
      · subst x
        have hey : e ≠ y := fun h => hne (List.mem_cons.mpr (Or.inl h))
        have heys : e ∈ ys := (List.mem_cons.mp he).resolve_left hey
        have henxs : e ∉ xs := fun h => hne (List.mem_cons_of_mem y h)
        have hnew' : ∀ z ∈ xs, z ∉ ys → Lt cmp z e := by
          intro z hz hzy
          apply hnew z (List.mem_cons_of_mem y hz)
          intro h
          rcases List.mem_cons.mp h with heq | h
          · have hzlt := hx z hz
            rw [heq] at hzlt
            exact lt_irrefl cmp laws y hzlt
          · exact hzy h
        have hi := ih hxs hys heys henxs hnew'
        have hself := (Comparison.entryCompare_eq_iff cmp laws.eq_iff y y).mpr rfl
        simpa only [listCompare, hself, thenCompare] using hi
      · have hnot : x ∉ y :: ys := by
          intro h
          rcases List.mem_cons.mp h with heq | h
          · rw [heq] at hyx
            exact lt_irrefl cmp laws y hyx
          · exact lt_asymm cmp laws hyx (hy x h)
        have hxe := hnew x List.mem_cons_self hnot
        have hey : Le cmp e y := by
          rcases List.mem_cons.mp he with h | h
          · exact Or.inl h
          · exact Or.inr (hy e h)
        exact False.elim (lt_asymm cmp laws hyx (lt_of_lt_of_le cmp laws hxe hey))


def Canonical (g : Graph Row) : Prop :=
  ∀ c ∈ g, Sorted cmp c ∧ ∀ e ∈ c, ∀ q, q ≤ e.root → {e with root := q} ∈ c

omit laws in
theorem canonical_rootClosed {g : Graph Row} (hg : Canonical cmp g) : RootClosed g :=
  fun c hc => (hg c hc).2

theorem normalized_column_canonical (c : Column Row) :
    Sorted cmp (normalizeColumn cmp c) ∧
      ∀ e ∈ normalizeColumn cmp c, ∀ q, q ≤ e.root →
        {e with root := q} ∈ normalizeColumn cmp c :=
  ⟨normalize_sorted cmp laws c, normalize_rootClosed cmp laws c⟩

theorem expand_canonical (package : Package Row) {g : Graph Row}
    (hg : Canonical cmp g) (n : Nat) : Canonical cmp (expand cmp package g n) := by
  intro c hc
  unfold expand at hc
  split at hc
  · exact hg c (List.mem_of_mem_take hc)
  · rcases List.mem_append.mp hc with hc | hc
    · exact hg c (List.mem_of_mem_take hc)
    · obtain ⟨b, _, hb⟩ := List.mem_flatMap.mp hc
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hb
      exact normalized_column_canonical cmp laws _

#print axioms compare_lt_of_deleted_pivot
#print axioms expand_canonical
end OrdinalFormal.GenericSortedColumns
