import ARDDemandReflection
import Mathlib.Data.List.Shortlex
import Mathlib.Order.WellFounded
import Mathlib.Data.Countable.Basic

/-!
# Actual least finite witnesses

Bad witnesses are minimized by shape code followed by the shortlex order of
their finite ordinal labeling. Extensions use a fixed shape and minimize the
finite labeling. Neither operation is an assumed reflection or supply map.

`Extends` fixes ONLY the pref strictly before the cut. It deliberately does
not fix a cut label or a controlling root. This includes the empty pref.
Weak-theory set coding of these minimizations is still a separate obligation.
-/

namespace ARDDemand
open OrdinalFormal.ReflectionTransport

universe u

open OrdinalFormal
instance entryCountable : Countable ARD.Entry :=
  Function.Injective.countable (f := fun e : ARD.Entry => (e.row,e.parent,e.root))
    (by intro a b h; cases a; cases b; simpa only [Prod.mk.injEq, Columns.Entry.mk.injEq] using h)
instance shapeCountable : Countable Shape :=
  Function.Injective.countable (f := fun A : Shape => (A.graph,A.cut,A.needs))
    (by intro a b h; cases a; cases b; simpa only [Prod.mk.injEq, Shape.mk.injEq] using h)

abbrev Packet := (A : Shape) × (Fin A.graph.length → Label.{u})

noncomputable def shapeCode (A : Shape) : Nat :=
  @Encodable.encode _ (Encodable.ofCountable (Shape)) A

theorem shapeCode_injective : Function.Injective (shapeCode) :=
  @Encodable.encode_injective _ (Encodable.ofCountable (Shape))

def TupleEarlier {n : Nat} : (Fin n → Label.{u}) → (Fin n → Label.{u}) → Prop :=
  InvImage (List.Shortlex (· < ·)) List.ofFn

theorem tupleEarlier_wellFounded (n : Nat) : WellFounded (@TupleEarlier.{u} n) :=
  InvImage.wf List.ofFn (List.Shortlex.wf Ordinal.lt_wf)

noncomputable def PacketEarlier : Packet.{u} → Packet.{u} → Prop :=
  InvImage (Prod.Lex (· < ·) (List.Shortlex (· < ·)))
    (fun p => (shapeCode p.1, List.ofFn p.2))

theorem packetEarlier_wellFounded : WellFounded (PacketEarlier.{u}) :=
  InvImage.wf _ (Nat.lt_wfRel.wf.prod_lex (List.Shortlex.wf Ordinal.lt_wf))

def Bad 
    (k : Label.{u}) (theta a kappa : Label.{u}) (p : Packet.{u}) : Prop :=
  Input relation (kappa, k, theta) a p.1 p.2 ∧
  ¬ ∃ g, Output relation a p.1 p.2 g

theorem exists_bad 
    {k : Label.{u}} {theta a kappa : Label.{u}}
    (hg : Guard (kappa, k, theta) a) (hn : ¬ relation k theta a kappa) :
    ∃ p, Bad k theta a kappa p := by
  classical
  have hd : ¬ Demands relation (kappa, k, theta) a := by
    intro hd
    exact hn ((relation_iff k theta a kappa).mpr ⟨hg, hd⟩)
  simp only [Demands, not_forall, _root_.not_imp] at hd
  obtain ⟨A, f, hf, hn⟩ := hd
  exact ⟨⟨A, f⟩, hf, hn⟩

noncomputable def leastBad 
    (k : Label.{u}) (theta a kappa : Label.{u})
    (h : ∃ p, Bad k theta a kappa p) : Packet.{u} :=
  packetEarlier_wellFounded.min {p | Bad k theta a kappa p} h

theorem leastBad_spec 
    (k : Label.{u}) (theta a kappa : Label.{u}) (h : ∃ p, Bad k theta a kappa p) :
    Bad k theta a kappa (leastBad k theta a kappa h) :=
  packetEarlier_wellFounded.min_mem _ h

/-- The coordinate operations of the least bad finite input, or zero. -/
noncomputable def badOp 
    (k : Label.{u}) (i : Nat) (theta a kappa : Label.{u}) : Label.{u} := by
  classical
  exact if h : ∃ p, Bad k theta a kappa p
    then labels (leastBad k theta a kappa h).2 i else 0

theorem badOp_eq 
    (k : Label.{u}) (i : Nat) (theta a kappa : Label.{u}) (h : ∃ p, Bad k theta a kappa p) :
    badOp k i theta a kappa = labels (leastBad k theta a kappa h).2 i := by
  simp [badOp, h]

theorem badOp_lt 
    (k : Label.{u}) (i : Nat) (theta a kappa : Label.{u}) (hk : 0 < kappa) :
    badOp k i theta a kappa < kappa := by
  classical
  by_cases h : ∃ p, Bad k theta a kappa p
  · rw [badOp_eq k i theta a kappa h]
    by_cases hi : i < (leastBad k theta a kappa h).1.graph.length
    · exact (leastBad_spec k theta a kappa h).1.2.1 i hi
    · simp [labels, hi, hk]
  · simp [badOp, h, hk]

def Extends (R : Rel.{u}) (kappa : Label.{u}) (A : Shape)
    (pref : Fin A.cut → Label.{u}) (f : Fin A.graph.length → Label.{u}) : Prop :=
  ARD.Holds (· < ·) domain R A.graph (labels f) ∧
  Bounded (· < ·) A.graph.length (labels f) kappa ∧
  (∀ i : Fin A.cut, labels f i = pref i) ∧
  ARD.Ends R A.needs (labels f) kappa

noncomputable def leastExtension (R : Rel.{u}) (kappa : Label.{u}) (A : Shape)
    (pref : Fin A.cut → Label.{u}) (h : ∃ f, Extends R kappa A pref f) :
    Fin A.graph.length → Label.{u} :=
  (tupleEarlier_wellFounded A.graph.length).min {f | Extends R kappa A pref f} h

theorem leastExtension_spec (R : Rel.{u}) (kappa : Label.{u}) (A : Shape)
    (pref : Fin A.cut → Label.{u}) (h : ∃ f, Extends R kappa A pref f) :
    Extends R kappa A pref (leastExtension R kappa A pref h) :=
  (tupleEarlier_wellFounded A.graph.length).min_mem _ h

noncomputable def extOp (R : Rel.{u}) (kappa : Label.{u}) (A : Shape) (i : Nat)
    (pref : Fin A.cut → Label.{u}) : Label.{u} := by
  classical
  exact if h : ∃ f, Extends R kappa A pref f
    then labels (leastExtension R kappa A pref h) i else 0

theorem extOp_eq (R : Rel.{u}) (kappa : Label.{u}) (A : Shape) (i : Nat)
    (pref : Fin A.cut → Label.{u}) (h : ∃ f, Extends R kappa A pref f) :
    extOp R kappa A i pref = labels (leastExtension R kappa A pref h) i := by
  simp [extOp, h]

theorem extOp_lt (R : Rel.{u}) (kappa : Label.{u}) (A : Shape) (i : Nat)
    (pref : Fin A.cut → Label.{u}) (hk : 0 < kappa) : extOp R kappa A i pref < kappa := by
  classical
  by_cases h : ∃ f, Extends R kappa A pref f
  · rw [extOp_eq R kappa A i pref h]
    by_cases hi : i < A.graph.length
    · exact (leastExtension_spec R kappa A pref h).2.1 i hi
    · simp [labels, hi, hk]
  · simp [extOp, h, hk]

end ARDDemand

#print axioms ARDDemand.exists_bad
#print axioms ARDDemand.leastBad_spec
#print axioms ARDDemand.badOp_lt
#print axioms ARDDemand.leastExtension_spec
#print axioms ARDDemand.extOp_lt
