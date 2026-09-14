import ARDCore
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Order.RelClasses

/-! Finite demands with row anchors evaluated by the current labeling.
All shapes are finite natural-number data; the ordinal control row is a value,
not an immutable parameter stored in a shape. -/
namespace ARDDemand
open OrdinalFormal
open OrdinalFormal.ReflectionTransport
universe u

abbrev Label := Ordinal.{u}
abbrev Rel := Label.{u} → Label.{u} → Label.{u} → Label.{u} → Prop
abbrev Stage := Label.{u} × (Label.{u} × Label.{u})
def Earlier : Stage.{u} → Stage.{u} → Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))
theorem earlier_wellFounded : WellFounded Earlier.{u} :=
  Ordinal.lt_wf.prod_lex (Ordinal.lt_wf.prod_lex Ordinal.lt_wf)
def domain (a : Label.{u}) : Prop := Ordinal.omega0 < a
noncomputable def labels {n : Nat} (f : Fin n → Label.{u}) (i : Nat) : Label.{u} :=
  if hi : i < n then f ⟨i, hi⟩ else 0
@[simp] theorem labels_apply {n : Nat} (f : Fin n → Label.{u}) {i : Nat} (hi : i < n) :
    labels f i = f ⟨i, hi⟩ := by simp [labels, hi]

structure Shape where
  graph : ARD.Graph
  valid : ARD.Valid graph
  cut : Nat
  cut_lt : cut < graph.length
  needs : List ARD.Entry
  needs_valid : ∀ d ∈ needs, ARD.NeedValid graph.length d

def Input (R : Rel.{u}) (s : Stage.{u}) (a : Label.{u})
    (A : Shape) (f : Fin A.graph.length → Label.{u}) : Prop :=
  ARD.Holds (· < ·) domain R A.graph (labels f) ∧
  Bounded (· < ·) A.graph.length (labels f) s.1 ∧ labels f A.cut = a ∧
  (∀ d ∈ A.needs, ARD.Admissible (· < ·) s.2.1 A.cut s.2.2 (labels f) d) ∧
  ARD.Ends R A.needs (labels f) s.1
def Output (R : Rel.{u}) (a : Label.{u}) (A : Shape)
    (f g : Fin A.graph.length → Label.{u}) : Prop :=
  ARD.Holds (· < ·) domain R A.graph (labels g) ∧
  (∀ i, i < A.cut → labels g i = labels f i) ∧
  Bounded (· < ·) A.graph.length (labels g) a ∧ ARD.Ends R A.needs (labels g) a
def Demands (R : Rel.{u}) (s : Stage.{u}) (a : Label.{u}) : Prop :=
  ∀ (A : Shape) (f : Fin A.graph.length → Label.{u}), Input R s a A f → ∃ g, Output R a A f g
def Guard (s : Stage.{u}) (a : Label.{u}) : Prop :=
  s.2.1 < s.1 ∧ s.2.2 ≤ a ∧ a < s.1 ∧ domain a
def Rule (R : Rel.{u}) (s : Stage.{u}) (a : Label.{u}) : Prop := Guard s a ∧ Demands R s a
def AgreeEarlier (s : Stage.{u}) (R S : Rel.{u}) : Prop :=
  ∀ k theta a b, Earlier (b,k,theta) s → (R k theta a b ↔ S k theta a b)
theorem AgreeEarlier.symm {s : Stage.{u}} {R S : Rel.{u}} (h : AgreeEarlier s R S) :
    AgreeEarlier s S R := fun k t a b ht => (h k t a b ht).symm

theorem representation_transfer {s : Stage.{u}} {R S : Rel.{u}} (h : AgreeEarlier s R S)
    {G : ARD.Graph} {f : Nat → Label.{u}} (hf : ARD.Holds (· < ·) domain R G f)
    (hb : Bounded (· < ·) G.length f s.1) : ARD.Holds (· < ·) domain S G f := by
  refine ⟨hf.domain, hf.ordered, ?_⟩
  intro j e he
  have hj : j < G.length := by
    by_contra hn
    have hz : G[j]?.getD [] = [] := by simp [List.getElem?_eq_none (by omega : G.length ≤ j)]
    simpa [hz] using he
  exact (h (f e.row) (f e.root) (f e.parent) (f j)
    (Prod.Lex.left _ _ (hb j hj))).mp (hf.relations j e he)
theorem admissible_earlier {s : Stage.{u}} {cut : Nat} {f : Nat → Label.{u}} {d : ARD.Entry}
    (h : ARD.Admissible (· < ·) s.2.1 cut s.2.2 f d) :
    Earlier (s.1, f d.row, f d.root) s := by
  rcases h with h | ⟨h, _, hr⟩
  · exact Prod.Lex.right _ (Prod.Lex.left _ _ h)
  · have hs : s = (s.1,s.2.1,s.2.2) := rfl
    rw [hs, h]
    exact Prod.Lex.right _ (Prod.Lex.right _ hr)
theorem input_transfer {s : Stage.{u}} {R S : Rel.{u}} (h : AgreeEarlier s R S)
    {a : Label.{u}} {A : Shape} {f : Fin A.graph.length → Label.{u}}
    (hf : Input R s a A f) : Input S s a A f := by
  rcases hf with ⟨hr,hb,hc,ha,he⟩
  refine ⟨representation_transfer h hr hb,hb,hc,ha,?_⟩
  intro d hd
  exact (h (labels f d.row) (labels f d.root) (labels f d.parent) s.1
    (admissible_earlier (ha d hd))).mp (he d hd)
theorem output_transfer {s : Stage.{u}} {R S : Rel.{u}} (h : AgreeEarlier s R S)
    {a : Label.{u}} (hab : a < s.1) {A : Shape} {f g : Fin A.graph.length → Label.{u}}
    (hg : Output R a A f g) : Output S a A f g := by
  rcases hg with ⟨hr,hf,hb,he⟩
  refine ⟨representation_transfer h hr (fun i hi => lt_trans (hb i hi) hab),hf,hb,?_⟩
  intro d hd
  exact (h (labels g d.row) (labels g d.root) (labels g d.parent) a
    (Prod.Lex.left _ _ hab)).mp (he d hd)
theorem rule_congr {s : Stage.{u}} {R S : Rel.{u}} (h : AgreeEarlier s R S) (a : Label.{u}) :
    Rule R s a ↔ Rule S s a := by
  suffices ∀ (R S : Rel.{u}), AgreeEarlier s R S → Rule R s a → Rule S s a from
    ⟨this R S h,this S R h.symm⟩
  intro R S h hrs
  refine ⟨hrs.1,?_⟩
  intro A f hf
  obtain ⟨g,hg⟩ := hrs.2 A f (input_transfer h.symm hf)
  exact ⟨g,output_transfer h hrs.1.2.2.1 hg⟩
end ARDDemand
#print axioms ARDDemand.rule_congr
