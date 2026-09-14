import OrdinalFormal.RPDDecrease
import OrdinalFormal.StandardValidity

/-!
Canonical finite columns of RPD: normalization produces strictly descending,
root-closed columns. These are finite order lemmas, not well-order assumptions.
-/

namespace OrdinalFormal.RPDSortedColumns
open Columns
set_option autoImplicit false
set_option maxHeartbeats 700000

abbrev E := Entry Nat
def Lt (a b : E) : Prop := entryCompare compare a b = .lt
def Le (a b : E) : Prop := a = b ∨ Lt a b
def Sorted (c : Column Nat) : Prop := c.Pairwise (fun a b => Lt b a)
def WeakSorted (c : Column Nat) : Prop := c.Pairwise (fun a b => Le b a)

theorem lt_iff (a b : E) : Lt a b ↔
    a.parent < b.parent ∨ (a.parent = b.parent ∧
      (a.row < b.row ∨ (a.row = b.row ∧ a.root < b.root))) := by
  simp [Lt, Comparison.entryCompare_lt_iff compare (fun _ _ => Nat.compare_eq_eq),
    Nat.compare_eq_lt]

theorem lt_irrefl (a : E) : ¬ Lt a a := by simp [lt_iff]

theorem lt_trans {a b c : E} (hab : Lt a b) (hbc : Lt b c) : Lt a c :=
  Comparison.entryCompare_lt_trans compare (fun _ _ => Nat.compare_eq_eq)
    Comparison.nat_compare_lt_trans hab hbc

theorem lt_asymm {a b : E} (hab : Lt a b) : ¬ Lt b a :=
  fun hba => lt_irrefl a (lt_trans hab hba)

theorem trichotomy (a b : E) : Lt a b ∨ a = b ∨ Lt b a := by
  by_cases h : a = b
  · exact Or.inr (Or.inl h)
  have hn : a.parent ≠ b.parent ∨ a.row ≠ b.row ∨ a.root ≠ b.root := by
    cases a
    cases b
    simp_all
    omega
  rw [lt_iff, lt_iff]
  omega

theorem le_of_not_lt {a b : E} (h : ¬ Lt b a) : Le a b := by
  rcases trichotomy a b with hl | he | hl
  · exact Or.inr hl
  · exact Or.inl he
  · exact False.elim (h hl)

theorem le_trans {a b c : E} (hab : Le a b) (hbc : Le b c) : Le a c := by
  rcases hab with rfl | hab
  · exact hbc
  rcases hbc with rfl | hbc
  · exact Or.inr hab
  · exact Or.inr (lt_trans hab hbc)

theorem lt_of_lt_of_le {a b c : E} (hab : Lt a b) (hbc : Le b c) : Lt a c := by
  rcases hbc with rfl | hbc
  · exact hab
  · exact lt_trans hab hbc

theorem insert_weakSorted (a : E) {c : Column Nat} (hc : WeakSorted c) :
    WeakSorted (insertDescending compare a c) := by
  induction c with
  | nil => simp [insertDescending, WeakSorted]
  | cons b bs ih =>
    obtain ⟨hb, hbs⟩ := List.pairwise_cons.mp hc
    simp only [insertDescending]
    split
    · rename_i hab
      have hba : Le b a := le_of_not_lt (by simpa [Lt] using hab)
      apply List.pairwise_cons.mpr
      refine ⟨?_, hc⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hba
      · exact le_trans (hb z hz) hba
    · rename_i hab
      have hab' : Lt a b := by simpa [Lt] using hab
      apply List.pairwise_cons.mpr
      refine ⟨?_, ih hbs⟩
      intro z hz
      rcases (ColumnRepresentation.mem_insertDescending compare z a bs).mp hz with rfl | hz
      · exact Or.inr hab'
      · exact hb z hz

theorem sort_weakSorted (c : Column Nat) : WeakSorted (sortDescending compare c) := by
  induction c with
  | nil => exact .nil
  | cons a as ih => exact insert_weakSorted a ih

theorem dedup_sorted {c : Column Nat} (hc : WeakSorted c) : Sorted (dedupSorted compare c) := by
  induction c with
  | nil => exact .nil
  | cons a as ih =>
    obtain ⟨ha, has⟩ := List.pairwise_cons.mp hc
    have hs := ih has
    cases hr : dedupSorted compare as with
    | nil => simp [dedupSorted, hr, Sorted]
    | cons b bs =>
      have hrest : Sorted (b :: bs) := by simpa [hr] using hs
      have hmem : ∀ z ∈ b :: bs, z ∈ as := by
        intro z hz
        exact ColumnRepresentation.mem_dedupSorted_subset compare (by simpa [hr] using hz)
      simp only [dedupSorted, hr]
      split
      · exact hrest
      · rename_i hne
        have hab : a ≠ b := by
          intro he
          apply hne
          apply beq_iff_eq.mpr
          exact (Comparison.entryCompare_eq_iff compare (fun _ _ => Nat.compare_eq_eq) a b).mpr he
        have hba : Lt b a := by
          rcases ha b (hmem b List.mem_cons_self) with he | hl
          · exact False.elim (hab he.symm)
          · exact hl
        apply List.pairwise_cons.mpr
        refine ⟨?_, hrest⟩
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hba
        · exact lt_trans ((List.pairwise_cons.mp hrest).1 z hz) hba

theorem normalize_sorted (c : Column Nat) : Sorted (normalizeColumn compare c) :=
  dedup_sorted (sort_weakSorted _)

theorem normalize_rootClosed (c : Column Nat) :
    ∀ e ∈ normalizeColumn compare c, ∀ q, q ≤ e.root →
      {e with root := q} ∈ normalizeColumn compare c := by
  intro e he q hq
  obtain ⟨s, hs, hr, hp, hroot⟩ :=
    ColumnRepresentation.mem_normalizeColumn_source compare he
  apply (RPDDecrease.mem_dedupSorted_iff _ _).mpr
  apply (ColumnRepresentation.mem_sortDescending compare _ _).mpr
  apply List.mem_flatMap.mpr
  refine ⟨s, hs, List.mem_map.mpr ⟨q, List.mem_range.mpr (by omega), ?_⟩⟩
  cases e
  cases s
  simp_all

/-- Removing a pivot and adding only entries below it strictly decreases a
strictly sorted finite column. Other old entries may also be removed. -/
theorem compare_lt_of_deleted_pivot {a b : Column Nat} (ha : Sorted a) (hb : Sorted b)
    (e : E) (he : e ∈ b) (hne : e ∉ a)
    (hnew : ∀ z ∈ a, z ∉ b → Lt z e) :
    listCompare (entryCompare compare) a b = .lt := by
  induction b generalizing a with
  | nil => simp at he
  | cons y ys ih =>
    cases a with
    | nil => rfl
    | cons x xs =>
      obtain ⟨hx, hxs⟩ := List.pairwise_cons.mp ha
      obtain ⟨hy, hys⟩ := List.pairwise_cons.mp hb
      rcases trichotomy x y with hxy | hxy | hyx
      · change entryCompare compare x y = .lt at hxy
        simp only [listCompare, hxy, thenCompare]
      · subst x
        have hey : e ≠ y := fun h => hne (List.mem_cons.mpr (Or.inl h))
        have heys : e ∈ ys := (List.mem_cons.mp he).resolve_left hey
        have henxs : e ∉ xs := fun h => hne (List.mem_cons_of_mem y h)
        have hnew' : ∀ z ∈ xs, z ∉ ys → Lt z e := by
          intro z hz hzy
          apply hnew z (List.mem_cons_of_mem y hz)
          intro h
          rcases List.mem_cons.mp h with heq | h
          · have hzlt := hx z hz
            rw [heq] at hzlt
            exact lt_irrefl y hzlt
          · exact hzy h
        have hi := ih hxs hys heys henxs hnew'
        have hself := (Comparison.entryCompare_eq_iff compare
          (fun _ _ => Nat.compare_eq_eq) y y).mpr rfl
        simpa only [listCompare, hself, thenCompare] using hi
      · have hnot : x ∉ y :: ys := by
          intro h
          rcases List.mem_cons.mp h with heq | h
          · rw [heq] at hyx
            exact lt_irrefl y hyx
          · exact lt_asymm hyx (hy x h)
        have hxe := hnew x List.mem_cons_self hnot
        have hey : Le e y := by
          rcases List.mem_cons.mp he with h | h
          · exact Or.inl h
          · exact Or.inr (hy e h)
        exact False.elim (lt_asymm hyx (lt_of_lt_of_le hxe hey))

def Canonical (g : RPD.Diagram) : Prop :=
  ∀ c ∈ g, Sorted c ∧ ∀ e ∈ c, ∀ q, q ≤ e.root → {e with root := q} ∈ c

theorem canonical_rootClosed {g : RPD.Diagram} (hg : Canonical g) : RootClosed g :=
  fun c hc => (hg c hc).2

theorem normalized_column_canonical (c : Column Nat) :
    Sorted (normalizeColumn compare c) ∧
      ∀ e ∈ normalizeColumn compare c, ∀ q, q ≤ e.root →
        {e with root := q} ∈ normalizeColumn compare c :=
  ⟨normalize_sorted c, normalize_rootClosed c⟩

theorem seed_canonical (n : Nat) : Canonical (RPD.seed n) := by
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact ⟨.nil, by simp⟩
  have hc' := List.mem_singleton.mp hc
  subst c
  exact normalized_column_canonical _

theorem fs_canonical {g : RPD.Diagram} (hg : Canonical g) (n : Nat) :
    Canonical (RPD.fs g n) := by
  intro c hc
  unfold RPD.fs expand at hc
  split at hc
  · exact hg c (List.mem_of_mem_take hc)
  · rcases List.mem_append.mp hc with hc | hc
    · exact hg c (List.mem_of_mem_take hc)
    · obtain ⟨b, _, hb⟩ := List.mem_flatMap.mp hc
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hb
      exact normalized_column_canonical _

theorem standard_canonical {g : RPD.Diagram} (hg : RPD.Standard (.finite g)) :
    Canonical g := by
  obtain ⟨n, hn⟩ := (RPD.standard_finite_iff g).mp hg
  exact reach_preserves [] RPD.fs Canonical (fun _ h k => fs_canonical h k)
    hn (seed_canonical n)

theorem firstColumn_lt {g : RPD.Diagram} (hg : Valid g) (hcan : Canonical g)
    {e : E} (he : Columns.control compare (g.getLast?.getD []) = some e) :
    listCompare (entryCompare compare) (RPDDecrease.firstColumn g e)
      (g.getLast?.getD []) = .lt := by
  have hn := RPDDecrease.nonempty_of_control he
  have hl : g.getLast?.getD [] ∈ g := by
    rw [List.getLast?_eq_some_getLast hn]
    exact List.getLast_mem hn
  apply compare_lt_of_deleted_pivot (normalize_sorted _) (hcan _ hl).1 e
    (ExpansionValidity.control_mem compare he)
    (RPDDecrease.controller_not_firstColumn hg (canonical_rootClosed hcan) e)
  intro z hz hnew
  exact RPDDecrease.firstColumn_new_below_control hg (canonical_rootClosed hcan) hn hz hnew

/-- Genuine one-step strict comparison for every geometrically valid,
canonical RPD graph. No accessibility or well-order premise. -/
theorem fs_lt {g : RPD.Diagram} (hg : Valid g) (hcan : Canonical g) (hn : g ≠ [])
    (n : Nat) : RPD.cmp (RPD.fs g n) g = .lt := by
  cases he : Columns.control compare (g.getLast?.getD []) with
  | none =>
    have hfs : RPD.fs g n = RPD.fs g 0 := by simp [RPD.fs, expand, he]
    rw [hfs]
    exact RPDDecrease.rpd_fs_zero_lt g hn
  | some e =>
    cases n with
    | zero => exact RPDDecrease.rpd_fs_zero_lt g hn
    | succ n =>
      exact (RPDDecrease.rpd_fs_positive_lt_iff hg he n).mpr (firstColumn_lt hg hcan he)

theorem standard_fs_lt {g : RPD.Diagram} (hg : RPD.Standard (.finite g))
    (hn : g ≠ []) (n : Nat) : RPD.cmp (RPD.fs g n) g = .lt :=
  fs_lt (StandardValidity.rpd_standard_valid hg) (standard_canonical hg) hn n

theorem standard_step_lt {a b : RPD.Diagram} (hb : RPD.Standard (.finite b))
    (hstep : RPD.Step a b) : RPD.cmp a b = .lt := by
  obtain ⟨hn, n, rfl⟩ := hstep
  exact standard_fs_lt hb hn n

end OrdinalFormal.RPDSortedColumns
