import OrdinalFormal.RPDFiniteUnion

/-!
The paper's finite-union expansion defines the same reachable domain as the
executable block rule. The seed and the top constructor are unchanged.
This is mathematical rule fidelity, not a semantics of the JavaScript runtime.
-/

namespace OrdinalFormal.RPDDefinitionFidelity
open Columns RPDFiniteUnion
set_option autoImplicit false
set_option maxHeartbeats 700000

def PaperFs (g : RPD.Diagram) (n : Nat) (h : RPD.Diagram) : Prop :=
  if n = 0 ∨ g.getLast?.getD [] = [] then h = g.take (g.length - 1)
  else ∃ e, PaperController (g.getLast?.getD []) e ∧ PaperResult g e n h

theorem control_none_iff (c : Column Nat) : control compare c = none ↔ c = [] := by
  cases c <;> simp [Columns.control]

theorem standard_fs_satisfies_paper {g : RPD.Diagram}
    (hg : RPD.Standard (.finite g)) (n : Nat) : PaperFs g n (RPD.fs g n) := by
  unfold PaperFs
  split
  · rename_i h
    rcases h with h | h
    · subst n
      exact RPD.fs_zero g
    · exact fs_no_control ((control_none_iff _).mpr h) n
  · rename_i hn
    cases he : control compare (g.getLast?.getD []) with
    | none => exact False.elim (hn (Or.inr ((control_none_iff _).mp he)))
    | some e =>
      have hc := (control_eq_paper _ e).mp he
      exact ⟨e, hc, standard_fs_paperResult hg hc n⟩

theorem paper_fs_eq {g : RPD.Diagram} (hg : RPD.Standard (.finite g))
    {n : Nat} {h : RPD.Diagram} (hh : PaperFs g n h) : RPD.fs g n = h := by
  unfold PaperFs at hh
  split at hh
  · rename_i hcase
    rcases hcase with hn | hempty
    · subst n
      exact (RPD.fs_zero g).trans hh.symm
    · exact (fs_no_control ((control_none_iff _).mpr hempty) n).trans hh.symm
  · obtain ⟨e, he, hspec⟩ := hh
    exact standard_fs_eq_paper hg he hspec

theorem standard_paper_fs_iff {g : RPD.Diagram} (hg : RPD.Standard (.finite g))
    (n : Nat) (h : RPD.Diagram) : PaperFs g n h ↔ RPD.fs g n = h := by
  constructor
  · exact paper_fs_eq hg
  · intro heq
    rw [← heq]
    exact standard_fs_satisfies_paper hg n

def PaperTermFs : RPD.Term → Nat → RPD.Term → Prop
  | .top, n, .finite g => g = RPD.seed n
  | .finite g, n, .finite h => PaperFs g n h
  | _, _, .top => False

theorem standard_term_fs_satisfies_paper {a : RPD.Term}
    (ha : RPD.Standard a) (n : Nat) : PaperTermFs a n (a.fs n) := by
  cases a with
  | top => rfl
  | finite g => exact standard_fs_satisfies_paper ha n

theorem paper_term_fs_eq {a b : RPD.Term} (ha : RPD.Standard a)
    {n : Nat} (h : PaperTermFs a n b) : a.fs n = b := by
  cases a with
  | top =>
    cases b with
    | top => exact False.elim h
    | finite g => exact congrArg RPD.Term.finite h.symm
  | finite g =>
    cases b with
    | top => exact False.elim h
    | finite k => exact congrArg RPD.Term.finite (paper_fs_eq ha h)

inductive PaperStandard : RPD.Term → Prop
  | top : PaperStandard .top
  | child {a b : RPD.Term} (ha : PaperStandard a) (n : Nat)
      (h : PaperTermFs a n b) : PaperStandard b

theorem paper_standard_to_standard {a : RPD.Term} (ha : PaperStandard a) : RPD.Standard a := by
  induction ha with
  | top => exact .top
  | child _ n h ih =>
    rw [← paper_term_fs_eq ih h]
    exact RPD.Standard.child ih n

theorem standard_to_paper_standard {a : RPD.Term} (ha : RPD.Standard a) : PaperStandard a := by
  induction ha with
  | top => exact .top
  | child h n ih => exact .child ih n (standard_term_fs_satisfies_paper h n)

theorem paper_standard_iff (a : RPD.Term) : PaperStandard a ↔ RPD.Standard a :=
  ⟨paper_standard_to_standard, standard_to_paper_standard⟩

#check standard_paper_fs_iff
#check paper_standard_iff
#print axioms standard_paper_fs_iff
#print axioms paper_term_fs_eq
#print axioms paper_standard_iff

end OrdinalFormal.RPDDefinitionFidelity
