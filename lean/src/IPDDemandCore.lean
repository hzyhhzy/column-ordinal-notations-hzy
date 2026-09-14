import IPDGraphCore
import IPDProfileCountable
import Mathlib.SetTheory.Ordinal.Basic

/-!
# IPD finite-demand semantics and causal dependency order

The recursion order is (right endpoint, profile, parent), not ARD's old row
order. Profiles are evaluated at current ROOT labels and the specified SELF
endpoint. These definitions contain no well-ordering or supply premise.
-/

namespace IPD.Semantics
set_option autoImplicit false
set_option maxHeartbeats 1000000
universe u

abbrev Label := Ordinal.{u}
abbrev Rel := Profile Label.{u} → Label.{u} → Label.{u} → Prop
abbrev Stage := Label.{u} × (Profile Label.{u} × Label.{u})

def Earlier : Stage.{u} → Stage.{u} → Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))

theorem earlier_wellFounded : WellFounded Earlier.{u} :=
  Ordinal.lt_wf.prod_lex ((profile_wellFounded Label.{u}).prod_lex Ordinal.lt_wf)

def domain (a : Label.{u}) : Prop := Ordinal.omega0 < a
def Bounded (n : Nat) (f : Nat → Label.{u}) (b : Label.{u}) : Prop := ∀ i, i < n → f i < b

structure Rep (R : Rel.{u}) (g : Graph) (f : Nat → Label.{u}) : Prop where
  domain : ∀ i, i < g.length → Semantics.domain (f i)
  ordered : ∀ i j, i < j → j < g.length → f i < f j
  relations : ∀ j e, e ∈ g[j]?.getD [] → R (renameProfile f e.profile) (f e.parent) (f j)

def endpointMap (m : Nat) (f : Nat → Label.{u}) (b : Label.{u}) (i : Nat) : Label.{u} :=
  if i = m then b else f i

def endpointProfile (m : Nat) (f : Nat → Label.{u}) (b : Label.{u}) (e : Edge) : Profile Label.{u} :=
  renameProfile (endpointMap m f b) e.profile

def Ends (R : Rel.{u}) (m : Nat) (needs : Column) (f : Nat → Label.{u}) (b : Label.{u}) : Prop :=
  ∀ e ∈ needs, R (endpointProfile m f b e) (f e.parent) b

def Admissible (s : Stage.{u}) (m : Nat) (f : Nat → Label.{u}) (e : Edge) : Prop :=
  Prod.Lex (· < ·) (· < ·) (endpointProfile m f s.1 e, f e.parent) s.2

noncomputable def labels {n : Nat} (f : Fin n → Label.{u}) (i : Nat) : Label.{u} :=
  if hi : i < n then f ⟨i, hi⟩ else 0

@[simp] theorem labels_apply {n : Nat} (f : Fin n → Label.{u}) {i : Nat} (hi : i < n) :
    labels f i = f ⟨i, hi⟩ := by simp [labels, hi]

structure Shape where
  graph : Graph
  valid : Valid graph
  cut : Nat
  cut_lt : cut < graph.length
  needs : Column
  needs_valid : ∀ e ∈ needs, e.Valid graph.length

instance edgeCountable : Countable Edge :=
  Function.Injective.countable (f := fun e : Edge => (e.parent, e.profile))
    (by intro a b h; cases a; cases b; simpa only [Prod.mk.injEq, Edge.mk.injEq] using h)

instance shapeCountable : Countable Shape :=
  Function.Injective.countable (f := fun A : Shape => (A.graph, A.cut, A.needs))
    (by intro a b h; cases a; cases b; simpa only [Prod.mk.injEq, Shape.mk.injEq] using h)

def Input (R : Rel.{u}) (s : Stage.{u}) (A : Shape) (f : Fin A.graph.length → Label.{u}) : Prop :=
  Rep R A.graph (labels f) ∧ Bounded A.graph.length (labels f) s.1 ∧
  labels f A.cut = s.2.2 ∧ (∀ e ∈ A.needs, Admissible s A.graph.length (labels f) e) ∧
  Ends R A.graph.length A.needs (labels f) s.1

def Output (R : Rel.{u}) (a : Label.{u}) (A : Shape)
    (f g : Fin A.graph.length → Label.{u}) : Prop :=
  Rep R A.graph (labels g) ∧ (∀ i, i < A.cut → labels g i = labels f i) ∧
  Bounded A.graph.length (labels g) a ∧ Ends R A.graph.length A.needs (labels g) a

def Demands (R : Rel.{u}) (s : Stage.{u}) : Prop :=
  ∀ (A : Shape) (f : Fin A.graph.length → Label.{u}), Input R s A f → ∃ g, Output R s.2.2 A f g

def Guard (s : Stage.{u}) : Prop :=
  domain s.2.2 ∧ s.2.2 < s.1 ∧ ProfileAtoms (fun x => x ≤ s.2.2 ∨ x = s.1) s.2.1

def Rule (R : Rel.{u}) (s : Stage.{u}) : Prop := Guard s ∧ Demands R s

def AgreeEarlier (s : Stage.{u}) (R S : Rel.{u}) : Prop :=
  ∀ t a b, Earlier (b, t, a) s → (R t a b ↔ S t a b)

theorem AgreeEarlier.symm {s : Stage.{u}} {R S : Rel.{u}} (h : AgreeEarlier s R S) :
    AgreeEarlier s S R := fun t a b ht => (h t a b ht).symm

theorem representation_transfer {s : Stage.{u}} {R S : Rel.{u}} (h : AgreeEarlier s R S)
    {G : Graph} {f : Nat → Label.{u}} (hf : Rep R G f) (hb : Bounded G.length f s.1) :
    Rep S G f := by
  refine ⟨hf.domain, hf.ordered, ?_⟩
  intro j e he
  have hj : j < G.length := by
    by_contra hn
    have hz : G[j]?.getD [] = [] := by rw [List.getElem?_eq_none (by omega)]; rfl
    simpa only [hz, List.not_mem_nil] using he
  exact (h (renameProfile f e.profile) (f e.parent) (f j)
    (Prod.Lex.left _ _ (hb j hj))).mp (hf.relations j e he)

theorem input_transfer {s : Stage.{u}} {R S : Rel.{u}} (h : AgreeEarlier s R S)
    {A : Shape} {f : Fin A.graph.length → Label.{u}} (hf : Input R s A f) : Input S s A f := by
  rcases hf with ⟨hr, hb, hc, ha, he⟩
  refine ⟨representation_transfer h hr hb, hb, hc, ha, ?_⟩
  intro e hem
  exact (h (endpointProfile A.graph.length (labels f) s.1 e) (labels f e.parent) s.1
    (Prod.Lex.right _ (ha e hem))).mp (he e hem)

theorem output_transfer {s : Stage.{u}} {R S : Rel.{u}} (h : AgreeEarlier s R S)
    {a : Label.{u}} (hab : a < s.1) {A : Shape} {f g : Fin A.graph.length → Label.{u}}
    (hg : Output R a A f g) : Output S a A f g := by
  rcases hg with ⟨hr, hp, hb, he⟩
  refine ⟨representation_transfer h hr (fun i hi => lt_trans (hb i hi) hab), hp, hb, ?_⟩
  intro e hem
  exact (h (endpointProfile A.graph.length (labels g) a e) (labels g e.parent) a
    (Prod.Lex.left _ _ hab)).mp (he e hem)

theorem rule_congr {s : Stage.{u}} {R S : Rel.{u}} (h : AgreeEarlier s R S) :
    Rule R s ↔ Rule S s := by
  suffices ∀ R S, AgreeEarlier s R S → Rule R s → Rule S s from ⟨this R S h, this S R h.symm⟩
  intro R S h hrs
  refine ⟨hrs.1, ?_⟩
  intro A f hf
  obtain ⟨g, hg⟩ := hrs.2 A f (input_transfer h.symm hf)
  exact ⟨g, output_transfer h hrs.1.2.1 hg⟩

end IPD.Semantics

#print axioms IPD.Semantics.earlier_wellFounded
#print axioms IPD.Semantics.shapeCountable
#print axioms IPD.Semantics.rule_congr
