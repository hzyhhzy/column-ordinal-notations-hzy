import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Order.RelClasses
import OrdinalFormal.ReflectionTransport

/-!
# Finite-demand semantics: finite data and strict predecessor locality

This is a new semantic backend, not a change to any notation's rules. All
labelings in its defining quantifiers are genuinely finite (`Fin n → Ordinal`).
The Nat-indexed labeling below is only the zero extension used to connect the
already proved finite geometric transport interface.

The recursion stage is (upper endpoint, row, root). Internal edges may have
arbitrary rows. Only edges to the current endpoint use the admissibility
guard. No reflection principle, initial representation, or accessibility is
assumed here. This host-Lean construction is not yet a KP derivation certificate.
-/

namespace FiniteDemand

open OrdinalFormal.ReflectionTransport

universe u v
variable {Row : Type v}

abbrev Label := Ordinal.{u}
abbrev Rel (Row : Type v) := Row → Label.{u} → Label.{u} → Label.{u} → Prop
abbrev Stage (Row : Type v) := Label.{u} × (Row × Label.{u})

def Earlier (rowLt : Row → Row → Prop) : Stage.{u} Row → Stage.{u} Row → Prop :=
  Prod.Lex (· < ·) (Prod.Lex rowLt (· < ·))

theorem earlier_wellFounded (rowLt : Row → Row → Prop) (h : WellFounded rowLt) :
    WellFounded (Earlier.{u} rowLt) :=
  Ordinal.lt_wf.prod_lex (h.prod_lex Ordinal.lt_wf)

def domain (a : Label.{u}) : Prop := Ordinal.omega0 < a

noncomputable def labels {n : Nat} (f : Fin n → Label.{u}) (i : Nat) : Label.{u} :=
  if hi : i < n then f ⟨i, hi⟩ else 0

@[simp] theorem labels_apply {n : Nat} (f : Fin n → Label.{u}) {i : Nat} (hi : i < n) :
    labels f i = f ⟨i, hi⟩ := by simp [labels, hi]

/-- The finite diagram and endpoint template, including all index guards. -/
structure Shape (Row : Type v) where
  diagram : Diagram Row
  cut : Nat
  cut_lt : cut < diagram.size
  needs : List (TopAtom Row)
  needs_valid : ∀ d ∈ needs, d.Valid diagram.size

def Ends (R : Rel.{u} Row) (needs : List (TopAtom Row))
    (f : Nat → Label.{u}) (b : Label.{u}) : Prop :=
  ∀ d ∈ needs, d.Holds R f b

def Input (rowLt : Row → Row → Prop) (R : Rel.{u} Row) (s : Stage.{u} Row)
    (a : Label.{u}) (A : Shape Row) (f : Fin A.diagram.size → Label.{u}) : Prop :=
  Representation (· < ·) domain R A.diagram (labels f) ∧
  Bounded (· < ·) A.diagram.size (labels f) s.1 ∧
  labels f A.cut = a ∧
  (∀ d ∈ A.needs, Admissible rowLt (· < ·) s.2.1 A.cut s.2.2 (labels f) d) ∧
  Ends R A.needs (labels f) s.1

def Output (R : Rel.{u} Row) (a : Label.{u}) (A : Shape Row)
    (f g : Fin A.diagram.size → Label.{u}) : Prop :=
  Representation (· < ·) domain R A.diagram (labels g) ∧
  (∀ i, i < A.cut → labels g i = labels f i) ∧
  Bounded (· < ·) A.diagram.size (labels g) a ∧
  Ends R A.needs (labels g) a

def Demands (rowLt : Row → Row → Prop) (R : Rel.{u} Row)
    (s : Stage.{u} Row) (a : Label.{u}) : Prop :=
  ∀ (A : Shape Row) (f : Fin A.diagram.size → Label.{u}),
    Input rowLt R s a A f → ∃ g, Output R a A f g

def Guard (s : Stage.{u} Row) (a : Label.{u}) : Prop :=
  s.2.2 ≤ a ∧ a < s.1 ∧ domain a

def Rule (rowLt : Row → Row → Prop) (R : Rel.{u} Row)
    (s : Stage.{u} Row) (a : Label.{u}) : Prop :=
  Guard s a ∧ Demands rowLt R s a

def AgreeEarlier (rowLt : Row → Row → Prop) (s : Stage.{u} Row)
    (R S : Rel.{u} Row) : Prop :=
  ∀ k theta a b, Earlier rowLt (b, k, theta) s → (R k theta a b ↔ S k theta a b)

theorem AgreeEarlier.symm {rowLt : Row → Row → Prop} {s : Stage.{u} Row}
    {R S : Rel.{u} Row} (h : AgreeEarlier rowLt s R S) : AgreeEarlier rowLt s S R :=
  fun k theta a b ht => (h k theta a b ht).symm

/-- Internal edges end below the stage. Their row and root are unrestricted. -/
theorem representation_transfer {rowLt : Row → Row → Prop} {s : Stage.{u} Row}
    {R S : Rel.{u} Row} (h : AgreeEarlier rowLt s R S)
    {G : Diagram Row} {f : Nat → Label.{u}}
    (hf : Representation (· < ·) domain R G f)
    (hb : Bounded (· < ·) G.size f s.1) :
    Representation (· < ·) domain S G f := by
  refine ⟨hf.domain, hf.ordered, ?_⟩
  intro e he
  exact (h e.layer (f e.root) (f e.parent) (f e.child)
    (Prod.Lex.left _ _ (hb e.child (G.valid e he).2.2))).mp (hf.relations e he)

theorem admissible_earlier {rowLt : Row → Row → Prop} {s : Stage.{u} Row}
    {cut : Nat} {f : Nat → Label.{u}} {d : TopAtom Row}
    (h : Admissible rowLt (· < ·) s.2.1 cut s.2.2 f d) :
    Earlier rowLt (s.1, d.layer, f d.root) s := by
  rcases h with h | ⟨h, _, hr⟩
  · exact Prod.Lex.right _ (Prod.Lex.left _ _ h)
  · have hs : s = (s.1, s.2.1, s.2.2) := rfl
    rw [hs, h]
    exact Prod.Lex.right _ (Prod.Lex.right _ hr)

theorem input_transfer {rowLt : Row → Row → Prop} {s : Stage.{u} Row}
    {R S : Rel.{u} Row} (h : AgreeEarlier rowLt s R S)
    {a : Label.{u}} {A : Shape Row} {f : Fin A.diagram.size → Label.{u}}
    (hf : Input rowLt R s a A f) : Input rowLt S s a A f := by
  rcases hf with ⟨hr, hb, hc, ha, he⟩
  refine ⟨representation_transfer h hr hb, hb, hc, ha, ?_⟩
  intro d hd
  exact (h d.layer (labels f d.root) (labels f d.parent) s.1
    (admissible_earlier (ha d hd))).mp (he d hd)

theorem output_transfer {rowLt : Row → Row → Prop} {s : Stage.{u} Row}
    {R S : Rel.{u} Row} (h : AgreeEarlier rowLt s R S)
    {a : Label.{u}} (hab : a < s.1) {A : Shape Row}
    {f g : Fin A.diagram.size → Label.{u}} (hg : Output R a A f g) : Output S a A f g := by
  rcases hg with ⟨hr, hf, hb, he⟩
  refine ⟨representation_transfer h hr (fun i hi => lt_trans (hb i hi) hab), hf, hb, ?_⟩
  intro d hd
  exact (h d.layer (labels g d.root) (labels g d.parent) a
    (Prod.Lex.left _ _ hab)).mp (he d hd)

/-- Every query in the actual defining test is strictly earlier. -/
theorem rule_congr {rowLt : Row → Row → Prop} {s : Stage.{u} Row}
    {R S : Rel.{u} Row} (h : AgreeEarlier rowLt s R S) (a : Label.{u}) :
    Rule rowLt R s a ↔ Rule rowLt S s a := by
  suffices ∀ (R S : Rel.{u} Row), AgreeEarlier rowLt s R S →
      Rule rowLt R s a → Rule rowLt S s a from
    ⟨this R S h, this S R h.symm⟩
  intro R S h hrs
  refine ⟨hrs.1, ?_⟩
  intro A f hf
  obtain ⟨g, hg⟩ := hrs.2 A f (input_transfer h.symm hf)
  exact ⟨g, output_transfer h hrs.1.2.1 hg⟩

end FiniteDemand

#print axioms FiniteDemand.earlier_wellFounded
#print axioms FiniteDemand.representation_transfer
#print axioms FiniteDemand.rule_congr
