import ARDSkylineCore
import ARDPrefixOrder
import OrdinalFormal.Comparison

/-! The actual finite terms, external top, and reachable standard domain.
No semantic accessibility is built into the definition of a standard term. -/

namespace OrdinalFormal.ARDSkyline
set_option autoImplicit false

abbrev Step : Graph → Graph → Prop := FSStep [] expand

inductive Term where
  | finite (g : Graph)
  | top
  deriving Repr, DecidableEq

def Term.fs : Term → Nat → Term
  | .finite g, n => .finite (expand g n)
  | .top, n => .finite (seed n)

inductive Standard : Term → Prop
  | top : Standard .top
  | child {a : Term} (ha : Standard a) (n : Nat) : Standard (a.fs n)

private theorem core_empty (n : Nat) : expand [] n = [] := by
  simp [expand, Columns.control]

theorem standard_seed (n : Nat) : Standard (.finite (seed n)) :=
  .child .top n

theorem standard_closed {g h : Graph}
    (hg : Standard (.finite g)) (hstep : Step h g) : Standard (.finite h) := by
  obtain ⟨_, n, rfl⟩ := hstep
  exact .child hg n

theorem standard_of_reach {g h : Graph} (hg : Standard (.finite g))
    (hreach : Reach Step g h) : Standard (.finite h) := by
  induction hreach with
  | refl => exact hg
  | cons h _ ih => exact ih (standard_closed hg h)

theorem standard_finite_iff (g : Graph) :
    Standard (.finite g) ↔ SeedDomain (Step := Step) seed g := by
  constructor
  · intro hg
    have aux : ∀ {a : Term}, Standard a →
        match a with
        | .top => True
        | .finite h => SeedDomain (Step := Step) seed h := by
      intro a ha
      induction ha with
      | top => trivial
      | @child a ha n ih =>
        cases a with
        | top => exact ⟨n, .refl _⟩
        | finite h =>
          change SeedDomain (Step := Step) seed (expand h n)
          by_cases he : h = []
          · subst h
            simpa only [core_empty] using ih
          · obtain ⟨m, hm⟩ := ih
            exact ⟨m, hm.trans (.single ⟨he, n, rfl⟩)⟩
    exact aux hg
  · rintro ⟨n, hn⟩
    exact standard_of_reach (standard_seed n) hn

theorem standard_invariant (P : Graph → Prop)
    (seedIn : ∀ n, P (seed n))
    (closed : ∀ {g h}, P g → Step h g → P h)
    {g : Graph} (hg : Standard (.finite g)) : P g := by
  obtain ⟨n, hn⟩ := (standard_finite_iff g).mp hg
  have go : ∀ {a b}, Reach Step a b → P a → P b := by
    intro a b h
    induction h with
    | refl => exact id
    | cons h _ ih => exact fun ha => ih (closed ha h)
  exact go hn (seedIn n)

abbrev StandardDiagram := {g : Graph // Standard (.finite g)}
def StandardLt (a b : StandardDiagram) : Prop := CompareLt a.val b.val

theorem compareLt_trans {a b c : Graph} (hab : CompareLt a b)
    (hbc : CompareLt b c) : CompareLt a c :=
  Comparison.graphCompare_lt_trans compare (fun _ _ => Nat.compare_eq_eq)
    Comparison.nat_compare_lt_trans hab hbc

theorem compareLt_irrefl (g : Graph) : ¬ CompareLt g g :=
  Comparison.graphCompare_lt_irrefl compare (fun _ _ => Nat.compare_eq_eq) g

def termCompare : Term → Term → Ordering
  | .finite a, .finite b => Columns.graphCompare compare a b
  | .finite _, .top => .lt
  | .top, .finite _ => .gt
  | .top, .top => .eq

abbrev StandardTerm := {a : Term // Standard a}
def TermLt (a b : StandardTerm) : Prop := termCompare a.val b.val = .lt

def forgetTop (a : StandardTerm) : Option StandardDiagram :=
  match a with
  | ⟨.top, _⟩ => none
  | ⟨.finite g, hg⟩ => some ⟨g, hg⟩

theorem termLt_iff_adjoined (a b : StandardTerm) : TermLt a b ↔
    AdjoinTopLt StandardLt (forgetTop a) (forgetTop b) := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  cases a <;> cases b <;>
    simp [TermLt, termCompare, forgetTop, AdjoinTopLt, StandardLt, CompareLt, ARD.CompareLt]

theorem term_wellFounded_of_finite (h : WellFounded StandardLt) :
    WellFounded TermLt := by
  have hi := InvImage.wf forgetTop (wellFounded_adjoinTop h)
  exact Subrelation.wf (fun {a b} hab => (termLt_iff_adjoined a b).mp hab) hi

theorem term_total_of_finite
    (ht : ∀ a b : StandardDiagram, a = b ∨ StandardLt a b ∨ StandardLt b a)
    (a b : StandardTerm) : a = b ∨ TermLt a b ∨ TermLt b a := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  cases a with
  | top =>
    cases b with
    | top => exact .inl rfl
    | finite b => exact .inr (.inr rfl)
  | finite a =>
    cases b with
    | top => exact .inr (.inl rfl)
    | finite b =>
      rcases ht ⟨a, ha⟩ ⟨b, hb⟩ with heq | hl | hr
      · exact .inl (Subtype.ext (congrArg Term.finite (congrArg Subtype.val heq)))
      · exact .inr (.inl hl)
      · exact .inr (.inr hr)

#print axioms standard_finite_iff
#print axioms compareLt_trans
#print axioms term_wellFounded_of_finite
#print axioms term_total_of_finite

end OrdinalFormal.ARDSkyline

