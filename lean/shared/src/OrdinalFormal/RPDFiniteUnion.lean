import OrdinalFormal.BlockFiniteUnion
import OrdinalFormal.RPDSortedColumns

/-!
The literal finite-union rule in RPD-良序证明.md, section 1, versus the
current executable RPD. The independent specification below uses quantifiers
over copies of internal edges and the numerical seam inequalities. It does
not call block, stage, expand, ordinarySeam or normalizeColumn.
-/

namespace OrdinalFormal.RPDFiniteUnion
open Columns ActualBlockGeometry BlockFiniteUnion
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 4096

def PaperEdge (g : RPD.Diagram) (e : Entry Nat) (n j : Nat) (a : Entry Nat) : Prop :=
  (∃ b, b ≤ n ∧ ∃ i, i < g.length - 1 ∧ ∃ s ∈ g[i]?.getD [],
    j = move e.parent (g.length - 1 - e.parent) b i ∧
    a.row = s.row ∧
    a.parent = move e.parent (g.length - 1 - e.parent) b s.parent ∧
    a.root ≤ move e.parent (g.length - 1 - e.parent) b s.root) ∨
  (∃ b, b < n ∧ j = g.length - 1 + b * (g.length - 1 - e.parent) ∧
    ∃ s ∈ g[g.length - 1]?.getD [],
      a.row = s.row ∧
      a.parent = move e.parent (g.length - 1 - e.parent) b s.parent ∧
      a.root ≤ move e.parent (g.length - 1 - e.parent) b s.root ∧
      (s.row < e.row ∨ (s.row = e.row ∧ a.root < move e.parent (g.length - 1 - e.parent) b e.root)))

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

theorem finiteUnion_paper_iff (g : RPD.Diagram) (e : Entry Nat)
    (n j : Nat) (a : Entry Nat) :
    FiniteUnionEdge compare (fun _ _ => []) g e n j a ↔ PaperEdge g e n j a := by
  unfold FiniteUnionEdge PaperEdge
  simp only [generatedSeam, List.flatMap_nil, List.append_nil]
  simp only [ordinarySeam_weakening]
  simp only [ordinarySeam_mem_iff,
    List.getLast?_eq_getElem?, Nat.compare_eq_lt, Nat.compare_eq_eq,
    Weakened, moveEntry]

/-- Exact edge set, not a one-way over-approximation and not a finite test. -/
theorem fs_paper_iff {g : RPD.Diagram} (hg : Valid g) (hc : RootClosed g)
    {e : Entry Nat} (he : control compare (g.getLast?.getD []) = some e)
    (n j : Nat) (a : Entry Nat) :
    a ∈ (RPD.fs g n)[j]?.getD [] ↔ PaperEdge g e n j a := by
  change a ∈ (expand compare (fun _ _ => []) g n)[j]?.getD [] ↔ _
  rw [expand_eq_stage _ _ g he]
  exact (stage_finiteUnion_iff compare nat_compare_laws _ hg hc e
    (ExpansionValidity.control_valid compare hg he).2 n j a).trans
      (finiteUnion_paper_iff g e n j a)

theorem fs_paper_length {g : RPD.Diagram}
    {e : Entry Nat} (he : control compare (g.getLast?.getD []) = some e) (n : Nat) :
    (RPD.fs g n).length = g.length - 1 + n * (g.length - 1 - e.parent) := by
  unfold RPD.fs
  rw [expand_eq_stage _ _ g he]
  exact stage_length _ _ _ _ _

/-- Every actual standard input meets the geometric and closure hypotheses.
The comparison is not assumed well-founded here. -/
theorem standard_fs_paper {g : RPD.Diagram} (hg : RPD.Standard (.finite g))
    {e : Entry Nat} (he : control compare (g.getLast?.getD []) = some e) (n : Nat) :
    (RPD.fs g n).length = g.length - 1 + n * (g.length - 1 - e.parent) ∧
    ∀ j a, a ∈ (RPD.fs g n)[j]?.getD [] ↔ PaperEdge g e n j a :=
  ⟨fs_paper_length he n, fs_paper_iff (StandardValidity.rpd_standard_valid hg)
    (RPDSortedColumns.canonical_rootClosed (RPDSortedColumns.standard_canonical hg)) he n⟩

theorem fs_no_control {g : RPD.Diagram}
    (he : control compare (g.getLast?.getD []) = none) (n : Nat) :
    RPD.fs g n = g.take (g.length - 1) := by
  simp [RPD.fs, expand, he]

def PaperController (c : Column Nat) (e : Entry Nat) : Prop :=
  e ∈ c ∧ ∀ a ∈ c,
    a.row ≤ e.row ∧ (a.row = e.row → a.root ≤ e.root) ∧
      (a.row = e.row → a.root = e.root → a.parent ≤ e.parent)

theorem control_eq_paper (c : Column Nat) (e : Entry Nat) :
    control compare c = some e ↔ PaperController c e := by
  constructor
  · intro h
    exact ⟨ExpansionValidity.control_mem compare h, RPDDecrease.control_bound h⟩
  · rintro ⟨he, hmax⟩
    cases hc : control compare c with
    | none =>
      cases c with
      | nil => simp at he
      | cons a as => simp [Columns.control] at hc
    | some chosen =>
      have hce := RPDDecrease.control_bound hc e he
      have hec := hmax chosen (ExpansionValidity.control_mem compare hc)
      have hr : chosen.row = e.row := by have := hce.1; have := hec.1; omega
      have hq : chosen.root = e.root := by
        have := hce.2.1 hr.symm
        have := hec.2.1 hr
        omega
      have hp : chosen.parent = e.parent := by
        have := hce.2.2 hr.symm hq.symm
        have := hec.2.2 hr hq
        omega
      have hEq : chosen = e := by cases chosen; cases e; simp_all
      exact congrArg some hEq

theorem sorted_ext {c d : Column Nat}
    (hc : RPDSortedColumns.Sorted c) (hd : RPDSortedColumns.Sorted d)
    (hmem : ∀ a, a ∈ c ↔ a ∈ d) : c = d := by
  induction c generalizing d with
  | nil =>
    cases d with
    | nil => rfl
    | cons b bs => have h := (hmem b).mpr List.mem_cons_self; simp at h
  | cons a as ih =>
    cases d with
    | nil => have h := (hmem a).mp List.mem_cons_self; simp at h
    | cons b bs =>
      obtain ⟨ha, has⟩ := List.pairwise_cons.mp hc
      obtain ⟨hb, hbs⟩ := List.pairwise_cons.mp hd
      have hab : a = b := by
        rcases RPDSortedColumns.trichotomy a b with h | h | h
        · have hm := (hmem b).mpr List.mem_cons_self
          rcases List.mem_cons.mp hm with he | hm
          · rw [he] at h
            exact False.elim (RPDSortedColumns.lt_irrefl _ h)
          · exact False.elim (RPDSortedColumns.lt_asymm h (ha b hm))
        · exact h
        · have hm := (hmem a).mp List.mem_cons_self
          rcases List.mem_cons.mp hm with he | hm
          · rw [he] at h
            exact False.elim (RPDSortedColumns.lt_irrefl _ h)
          · exact False.elim (RPDSortedColumns.lt_asymm h (hb a hm))
      subst b
      have hna : a ∉ as := fun hm => RPDSortedColumns.lt_irrefl a (ha a hm)
      have hnb : a ∉ bs := fun hm => RPDSortedColumns.lt_irrefl a (hb a hm)
      have ht : as = bs := ih has hbs (by
        intro z
        by_cases hz : z = a
        · simp [hz, hna, hnb]
        · simpa [List.mem_cons, hz] using hmem z)
      exact congrArg (List.cons a) ht

/-- The finite-union specification determines the complete sorted column
list, including empty columns; edge equality alone would lose those. -/
def PaperResult (g : RPD.Diagram) (e : Entry Nat) (n : Nat) (h : RPD.Diagram) : Prop :=
  h.length = g.length - 1 + n * (g.length - 1 - e.parent) ∧
  (∀ j a, a ∈ h[j]?.getD [] ↔ PaperEdge g e n j a) ∧
  ∀ c ∈ h, RPDSortedColumns.Sorted c

theorem paperResult_unique {g : RPD.Diagram} {e : Entry Nat} {n : Nat}
    {h k : RPD.Diagram} (hh : PaperResult g e n h) (hk : PaperResult g e n k) : h = k := by
  apply List.ext_getElem (hh.1.trans hk.1.symm)
  intro j hj hj'
  apply sorted_ext (hh.2.2 _ (List.getElem_mem hj)) (hk.2.2 _ (List.getElem_mem hj'))
  intro a
  simpa only [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj', Option.getD_some] using
    (hh.2.1 j a).trans (hk.2.1 j a).symm

theorem standard_fs_paperResult {g : RPD.Diagram} (hg : RPD.Standard (.finite g))
    {e : Entry Nat} (he : PaperController (g.getLast?.getD []) e) (n : Nat) :
    PaperResult g e n (RPD.fs g n) := by
  have h := standard_fs_paper hg ((control_eq_paper _ e).mpr he) n
  exact ⟨h.1, h.2, fun c hc =>
    (RPDSortedColumns.standard_canonical (RPD.Standard.child hg n) c hc).1⟩

/-- Literal equality to any graph satisfying the independent mathematical
rule, on every reachable standard input and every natural index. -/
theorem standard_fs_eq_paper {g : RPD.Diagram} (hg : RPD.Standard (.finite g))
    {e : Entry Nat} (he : PaperController (g.getLast?.getD []) e)
    {n : Nat} {h : RPD.Diagram} (hh : PaperResult g e n h) : RPD.fs g n = h :=
  paperResult_unique (standard_fs_paperResult hg he n) hh

#check standard_fs_paper
#check standard_fs_eq_paper
#print axioms finiteUnion_paper_iff
#print axioms fs_paper_iff
#print axioms standard_fs_paper
#print axioms fs_no_control
#print axioms control_eq_paper
#print axioms paperResult_unique
#print axioms standard_fs_paperResult
#print axioms standard_fs_eq_paper

end OrdinalFormal.RPDFiniteUnion
