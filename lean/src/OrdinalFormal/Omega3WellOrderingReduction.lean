import OrdinalFormal.Omega3ColumnDecrease
import OrdinalFormal.ColumnReachability

/-!
# Actual Omega-LRD3 standard-order reduction

The sole remaining premise is accessibility of every actual finite seed.
All comparator, generated-row, prefix-joining, nesting and standard-domain
closure facts are proved from the executable definition. The final theorem
uses the actual `Term.top`, not a new substitute for its standard domain.
This file is a reduction, not an unconditional well-ordering proof.
-/

namespace OrdinalFormal.Omega3WellOrderingReduction
open Columns OmegaLRD3
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 4096

abbrev GraphStep := ColumnReachability.Step cmp rowPackage

theorem step_toGraph {a b : Diagram} (h : Step b a) : GraphStep b.toGraph a.toGraph := by
  obtain ⟨hn, n, rfl⟩ := h
  exact ⟨Omega3ColumnDecrease.toGraph_ne_nil hn, n, (fs_toGraph a n).symm⟩

theorem step_ofGraph {a b : Graph Diagram} (h : GraphStep b a) :
    Step (Diagram.ofGraph b) (Diagram.ofGraph a) := by
  obtain ⟨hn, n, rfl⟩ := h
  constructor
  · intro he
    have ht := congrArg Diagram.toGraph he
    exact hn (by simpa [Diagram.toGraph] using ht)
  · refine ⟨n, ?_⟩
    rw [fs_ofGraph, Diagram.toGraph_ofGraph]

theorem reach_toGraph {a b : Diagram} (h : Reach Step a b) :
    Reach GraphStep a.toGraph b.toGraph := by
  induction h with
  | refl => exact .refl _
  | cons h _ ih => exact .cons (step_toGraph h) ih

theorem graph_accessible {a : Diagram} (h : Acc Step a) : Acc GraphStep a.toGraph := by
  apply Subrelation.accessible (r := fun b a : Graph Diagram => Step (Diagram.ofGraph b) (Diagram.ofGraph a))
  · exact fun {_ _} h => step_ofGraph h
  · exact InvImage.accessible (r := Step) (a := a.toGraph) Diagram.ofGraph
      (by simpa only [Diagram.ofGraph_toGraph] using h)

abbrev StandardDiagram := {a : Diagram // Standard (.finite a)}
def StandardLt (a b : StandardDiagram) : Prop := cmp a.val b.val = .lt

def GraphStandard (g : Graph Diagram) : Prop := Standard (.finite (Diagram.ofGraph g))

theorem graph_standard_closed {a b : Graph Diagram} (ha : GraphStandard a)
    (h : GraphStep b a) : GraphStandard b := by
  obtain ⟨_, n, hn⟩ := step_ofGraph h
  change Standard (.finite (Diagram.ofGraph b))
  rw [← hn]
  exact Standard.child ha n

theorem graph_standard_covered (g : Graph Diagram) (hg : GraphStandard g) :
    SeedDomain (Step := GraphStep) (fun n => (seed n).toGraph) g := by
  obtain ⟨n, hn⟩ := (standard_finite_iff (Diagram.ofGraph g)).mp hg
  exact ⟨n, by simpa only [Diagram.toGraph_ofGraph] using reach_toGraph hn⟩

theorem graph_standard_step_lt {a b : Graph Diagram} (ha : GraphStandard a)
    (h : GraphStep b a) : graphCompare cmp b a = .lt := by
  have hh := Omega3ColumnDecrease.standard_step_lt ha (step_ofGraph h)
  rwa [Omega3Comparison.cmp_eq_graphCompare, Diagram.toGraph_ofGraph,
    Diagram.toGraph_ofGraph] at hh

theorem graph_standard_wellFounded_of_seed_accessible
    (seedAcc : ∀ n, Acc Step (seed n)) :
    WellFounded (fun a b : {g : Graph Diagram // GraphStandard g} =>
      graphCompare cmp a.val b.val = .lt) := by
  apply ColumnReachability.covered_domain_wellFounded cmp rowPackage
    @graph_standard_closed (fun n => (seed n).toGraph)
  · intro n
    change Standard (.finite (Diagram.ofGraph (seed n).toGraph))
    rw [Diagram.ofGraph_toGraph]
    exact Standard.child Standard.top n
  · exact graph_standard_covered
  · exact fun n => graph_accessible (seedAcc n)
  · exact fun n => reach_toGraph (seed_reachable n)
  · exact fun _ _ _ hab hbc => Comparison.graphCompare_lt_trans cmp
      Omega3Comparison.cmp_eq_iff Omega3Comparison.cmp_lt_trans hab hbc
  · exact fun a _ => Comparison.graphCompare_lt_irrefl cmp Omega3Comparison.cmp_eq_iff a
  · exact fun ha h => graph_standard_step_lt ha h

def toStandardGraph (a : StandardDiagram) : {g : Graph Diagram // GraphStandard g} :=
  ⟨a.val.toGraph, by
    change Standard (.finite (Diagram.ofGraph a.val.toGraph))
    rw [Diagram.ofGraph_toGraph]
    exact a.property⟩

theorem standard_wellFounded_of_seed_accessible
    (seedAcc : ∀ n, Acc Step (seed n)) : WellFounded StandardLt := by
  refine ⟨fun a => ?_⟩
  apply Subrelation.accessible (r := fun a b : StandardDiagram =>
    graphCompare cmp (toStandardGraph a).val (toStandardGraph b).val = .lt)
  · intro b c h
    exact (Omega3Comparison.cmp_eq_graphCompare b.val c.val) ▸ h
  · exact InvImage.accessible toStandardGraph
      ((graph_standard_wellFounded_of_seed_accessible seedAcc).apply (toStandardGraph a))

/-- Totality needs no accessibility premise: actual finite syntax is totally compared. -/
theorem standard_total (a b : StandardDiagram) :
    a = b ∨ StandardLt a b ∨ StandardLt b a := by
  rcases Omega3Comparison.cmp_trichotomy a.val b.val with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inr h)

theorem standard_step_wellFounded_of_seed_accessible
    (seedAcc : ∀ n, Acc Step (seed n)) :
    WellFounded (fun a b : StandardDiagram => Step a.val b.val) := by
  refine ⟨fun a => ?_⟩
  obtain ⟨n, hn⟩ := (standard_finite_iff a.val).mp a.property
  exact InvImage.accessible (fun a : StandardDiagram => a.val)
    (Reach.accessible (seedAcc n) hn)

abbrev StandardTerm := {t : Term // Standard t}

/-- The unique external top is above exactly all finite standard terms. -/
def TermLt (a b : StandardTerm) : Prop :=
  match a.val, b.val with
  | .finite a, .finite b => cmp a b = .lt
  | .finite _, .top => True
  | .top, _ => False

def toOption (a : StandardTerm) : Option StandardDiagram :=
  match a with
  | ⟨.top, _⟩ => none
  | ⟨.finite a, ha⟩ => some ⟨a, ha⟩

theorem termLt_iff (a b : StandardTerm) :
    TermLt a b ↔ AdjoinTopLt StandardLt (toOption a) (toOption b) := by
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  cases a <;> cases b <;> rfl

theorem with_top_wellFounded_of_seed_accessible
    (seedAcc : ∀ n, Acc Step (seed n)) : WellFounded TermLt := by
  have hw := wellFounded_adjoinTop (standard_wellFounded_of_seed_accessible seedAcc)
  refine ⟨fun a => ?_⟩
  apply Subrelation.accessible
    (r := fun a b : StandardTerm => AdjoinTopLt StandardLt (toOption a) (toOption b))
  · exact fun {b c} h => (termLt_iff b c).mp h
  · exact InvImage.accessible toOption (hw.apply (toOption a))

theorem with_top_total (a b : StandardTerm) : a = b ∨ TermLt a b ∨ TermLt b a := by
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  cases a with
  | top =>
    cases b with
    | top => exact Or.inl rfl
    | finite b => exact Or.inr (Or.inr trivial)
  | finite a =>
    cases b with
    | top => exact Or.inr (Or.inl trivial)
    | finite b =>
      rcases Omega3Comparison.cmp_trichotomy a b with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl (Subtype.ext (congrArg Term.finite h))
      · exact Or.inr (Or.inr h)

#print axioms standard_wellFounded_of_seed_accessible
#print axioms with_top_wellFounded_of_seed_accessible
#print axioms with_top_total

end OrdinalFormal.Omega3WellOrderingReduction
