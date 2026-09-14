import ARDFiniteUnion
import ARDOrderReduction
import OrdinalFormal.RPDFiniteUnion

/-! Exact agreement with an independently specified finite-union rule.
Only neutral Nat-entry maximum and sorted-list extensionality lemmas are reused
from RPDFiniteUnion, not an RPD semantic or well-ordering assertion. -/

namespace OrdinalFormal.ARD.Fidelity
open Columns FiniteUnion
set_option autoImplicit false

def PaperController (c : Column) (e : Entry) : Prop :=
  e ∈ c ∧ ∀ a ∈ c,
    a.row ≤ e.row ∧ (a.row = e.row → a.root ≤ e.root) ∧
      (a.row = e.row → a.root = e.root → a.parent ≤ e.parent)

theorem control_eq_paper (c : Column) (e : Entry) :
    control compare c = some e ↔ PaperController c e :=
  RPDFiniteUnion.control_eq_paper c e

def PaperResult (g : Graph) (e : Entry) (n : Nat) (h : Graph) : Prop :=
  h.length = g.length-1 + n*(g.length-1-e.parent) ∧
  (∀ j a, a ∈ h[j]?.getD [] ↔ PaperEdge g e n j a) ∧
  ∀ c ∈ h, GenericSortedColumns.Sorted compare c

theorem paperResult_unique {g : Graph} {e : Entry} {n : Nat}
    {h k : Graph} (hh : PaperResult g e n h) (hk : PaperResult g e n k) : h = k := by
  apply List.ext_getElem (hh.1.trans hk.1.symm)
  intro j hj hj'
  apply RPDFiniteUnion.sorted_ext
    (hh.2.2 _ (List.getElem_mem hj)) (hk.2.2 _ (List.getElem_mem hj'))
  intro a
  simpa only [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj', Option.getD_some] using
    (hh.2.1 j a).trans (hk.2.1 j a).symm

theorem standard_expand_paperResult {g : Graph} (hg : Standard (.finite g))
    {e : Entry} (he : PaperController (g.getLast?.getD []) e) (n : Nat) :
    PaperResult g e n (expand g n) := by
  have hctrl := (control_eq_paper _ e).mpr he
  refine ⟨?_, ?_, ?_⟩
  · rw [expand_eq_stage g hctrl, stage_length]
    rfl
  · exact expand_paper_iff (standard_valid hg)
      (GenericSortedColumns.canonical_rootClosed compare (standard_canonical hg)) hctrl n
  · exact fun c hc => (expand_canonical (standard_canonical hg) n c hc).1

theorem standard_expand_eq_paper {g : Graph} (hg : Standard (.finite g))
    {e : Entry} (he : PaperController (g.getLast?.getD []) e)
    {n : Nat} {h : Graph} (hh : PaperResult g e n h) : expand g n = h :=
  paperResult_unique (standard_expand_paperResult hg he n) hh

def PaperFs (g : Graph) (n : Nat) (h : Graph) : Prop :=
  if n = 0 ∨ g.getLast?.getD [] = [] then h = g.take (g.length - 1)
  else ∃ e, PaperController (g.getLast?.getD []) e ∧ PaperResult g e n h

theorem control_none_iff (c : Column) : control compare c = none ↔ c = [] := by
  cases c <;> simp [Columns.control]

theorem expand_no_control {g : Graph}
    (he : control compare (g.getLast?.getD []) = none) (n : Nat) :
    expand g n = g.take (g.length-1) := by simp [expand, he]

theorem standard_fs_satisfies_paper {g : Graph}
    (hg : Standard (.finite g)) (n : Nat) : PaperFs g n (expand g n) := by
  unfold PaperFs
  split
  · rename_i h
    rcases h with h | h
    · subst n
      exact expand_zero g
    · exact expand_no_control ((control_none_iff _).mpr h) n
  · rename_i hn
    cases he : control compare (g.getLast?.getD []) with
    | none => exact False.elim (hn (Or.inr ((control_none_iff _).mp he)))
    | some e =>
      have hc := (control_eq_paper _ e).mp he
      exact ⟨e, hc, standard_expand_paperResult hg hc n⟩

theorem paper_fs_eq {g : Graph} (hg : Standard (.finite g))
    {n : Nat} {h : Graph} (hh : PaperFs g n h) : expand g n = h := by
  unfold PaperFs at hh
  split at hh
  · rename_i hcase
    rcases hcase with hn | hempty
    · subst n
      exact (expand_zero g).trans hh.symm
    · exact (expand_no_control ((control_none_iff _).mpr hempty) n).trans hh.symm
  · obtain ⟨e, he, hspec⟩ := hh
    exact standard_expand_eq_paper hg he hspec

theorem standard_paper_fs_iff {g : Graph} (hg : Standard (.finite g))
    (n : Nat) (h : Graph) : PaperFs g n h ↔ expand g n = h := by
  constructor
  · exact paper_fs_eq hg
  · intro heq
    rw [← heq]
    exact standard_fs_satisfies_paper hg n

def PaperTermFs : Term → Nat → Term → Prop
  | .top, n, .finite g => g = seed n
  | .finite g, n, .finite h => PaperFs g n h
  | _, _, .top => False

theorem standard_term_fs_satisfies_paper {a : Term}
    (ha : Standard a) (n : Nat) : PaperTermFs a n (a.fs n) := by
  cases a with
  | top => rfl
  | finite g => exact standard_fs_satisfies_paper ha n

theorem paper_term_fs_eq {a b : Term} (ha : Standard a)
    {n : Nat} (h : PaperTermFs a n b) : a.fs n = b := by
  cases a with
  | top =>
    cases b with
    | top => exact False.elim h
    | finite g => exact congrArg Term.finite h.symm
  | finite g =>
    cases b with
    | top => exact False.elim h
    | finite k => exact congrArg Term.finite (paper_fs_eq ha h)

inductive PaperStandard : Term → Prop
  | top : PaperStandard .top
  | child {a b : Term} (ha : PaperStandard a) (n : Nat)
      (h : PaperTermFs a n b) : PaperStandard b

theorem paper_standard_to_standard {a : Term} (ha : PaperStandard a) : Standard a := by
  induction ha with
  | top => exact .top
  | child _ n h ih =>
    rw [← paper_term_fs_eq ih h]
    exact Standard.child ih n

theorem standard_to_paper_standard {a : Term} (ha : Standard a) : PaperStandard a := by
  induction ha with
  | top => exact .top
  | child h n ih => exact .child ih n (standard_term_fs_satisfies_paper h n)

theorem paper_standard_iff (a : Term) : PaperStandard a ↔ Standard a :=
  ⟨paper_standard_to_standard, standard_to_paper_standard⟩

#print axioms control_eq_paper
#print axioms paperResult_unique
#print axioms standard_expand_eq_paper
#print axioms standard_paper_fs_iff
#print axioms paper_term_fs_eq
#print axioms paper_standard_iff

end OrdinalFormal.ARD.Fidelity
