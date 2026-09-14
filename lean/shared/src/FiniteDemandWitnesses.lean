import FiniteDemandReflection
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

namespace FiniteDemand
open OrdinalFormal.ReflectionTransport

universe u v
variable {Row : Type v}

instance atomCountable [Countable Row] : Countable (Atom Row) :=
  Function.Injective.countable (f := fun e : Atom Row => (e.layer, e.root, e.parent, e.child))
    (by intro a b h; cases a; cases b; simpa only [Prod.mk.injEq, Atom.mk.injEq] using h)

instance topAtomCountable [Countable Row] : Countable (TopAtom Row) :=
  Function.Injective.countable (f := fun e : TopAtom Row => (e.layer, e.root, e.parent))
    (by intro a b h; cases a; cases b; simpa only [Prod.mk.injEq, TopAtom.mk.injEq] using h)

instance diagramCountable [Countable Row] : Countable (Diagram Row) :=
  Function.Injective.countable (f := fun G : Diagram Row => (G.size, G.atoms))
    (by intro a b h; cases a; cases b; simpa only [Prod.mk.injEq, Diagram.mk.injEq] using h)

instance shapeCountable [Countable Row] : Countable (Shape Row) :=
  Function.Injective.countable (f := fun A : Shape Row => (A.diagram, A.cut, A.needs))
    (by intro a b h; cases a; cases b; simpa only [Prod.mk.injEq, Shape.mk.injEq] using h)

abbrev Packet (Row : Type v) := (A : Shape Row) × (Fin A.diagram.size → Label.{u})

noncomputable def shapeCode [Countable Row] (A : Shape Row) : Nat :=
  @Encodable.encode _ (Encodable.ofCountable (Shape Row)) A

theorem shapeCode_injective [Countable Row] : Function.Injective (@shapeCode Row _) :=
  @Encodable.encode_injective _ (Encodable.ofCountable (Shape Row))

def TupleEarlier {n : Nat} : (Fin n → Label.{u}) → (Fin n → Label.{u}) → Prop :=
  InvImage (List.Shortlex (· < ·)) List.ofFn

theorem tupleEarlier_wellFounded (n : Nat) : WellFounded (@TupleEarlier.{u} n) :=
  InvImage.wf List.ofFn (List.Shortlex.wf Ordinal.lt_wf)

noncomputable def PacketEarlier [Countable Row] : Packet.{u} Row → Packet.{u} Row → Prop :=
  InvImage (Prod.Lex (· < ·) (List.Shortlex (· < ·)))
    (fun p => (shapeCode p.1, List.ofFn p.2))

theorem packetEarlier_wellFounded [Countable Row] : WellFounded (@PacketEarlier.{u} Row _) :=
  InvImage.wf _ (Nat.lt_wfRel.wf.prod_lex (List.Shortlex.wf Ordinal.lt_wf))

def Bad (rowLt : Row → Row → Prop) (hw : WellFounded rowLt)
    (k : Row) (theta a kappa : Label.{u}) (p : Packet.{u} Row) : Prop :=
  Input rowLt (relation rowLt hw) (kappa, k, theta) a p.1 p.2 ∧
  ¬ ∃ g, Output (relation rowLt hw) a p.1 p.2 g

theorem exists_bad {rowLt : Row → Row → Prop} {hw : WellFounded rowLt}
    {k : Row} {theta a kappa : Label.{u}}
    (hg : Guard (kappa, k, theta) a) (hn : ¬ relation rowLt hw k theta a kappa) :
    ∃ p, Bad rowLt hw k theta a kappa p := by
  classical
  have hd : ¬ Demands rowLt (relation rowLt hw) (kappa, k, theta) a := by
    intro hd
    exact hn ((relation_iff rowLt hw k theta a kappa).mpr ⟨hg, hd⟩)
  simp only [Demands, not_forall, _root_.not_imp] at hd
  obtain ⟨A, f, hf, hn⟩ := hd
  exact ⟨⟨A, f⟩, hf, hn⟩

noncomputable def leastBad [Countable Row] (rowLt : Row → Row → Prop) (hw : WellFounded rowLt)
    (k : Row) (theta a kappa : Label.{u})
    (h : ∃ p, Bad rowLt hw k theta a kappa p) : Packet.{u} Row :=
  packetEarlier_wellFounded.min {p | Bad rowLt hw k theta a kappa p} h

theorem leastBad_spec [Countable Row] (rowLt : Row → Row → Prop) (hw : WellFounded rowLt)
    (k : Row) (theta a kappa : Label.{u}) (h : ∃ p, Bad rowLt hw k theta a kappa p) :
    Bad rowLt hw k theta a kappa (leastBad rowLt hw k theta a kappa h) :=
  packetEarlier_wellFounded.min_mem _ h

/-- The coordinate operations of the least bad finite input, or zero. -/
noncomputable def badOp [Countable Row] (rowLt : Row → Row → Prop) (hw : WellFounded rowLt)
    (k : Row) (i : Nat) (theta a kappa : Label.{u}) : Label.{u} := by
  classical
  exact if h : ∃ p, Bad rowLt hw k theta a kappa p
    then labels (leastBad rowLt hw k theta a kappa h).2 i else 0

theorem badOp_eq [Countable Row] (rowLt : Row → Row → Prop) (hw : WellFounded rowLt)
    (k : Row) (i : Nat) (theta a kappa : Label.{u}) (h : ∃ p, Bad rowLt hw k theta a kappa p) :
    badOp rowLt hw k i theta a kappa = labels (leastBad rowLt hw k theta a kappa h).2 i := by
  simp [badOp, h]

theorem badOp_lt [Countable Row] (rowLt : Row → Row → Prop) (hw : WellFounded rowLt)
    (k : Row) (i : Nat) (theta a kappa : Label.{u}) (hk : 0 < kappa) :
    badOp rowLt hw k i theta a kappa < kappa := by
  classical
  by_cases h : ∃ p, Bad rowLt hw k theta a kappa p
  · rw [badOp_eq rowLt hw k i theta a kappa h]
    by_cases hi : i < (leastBad rowLt hw k theta a kappa h).1.diagram.size
    · exact (leastBad_spec rowLt hw k theta a kappa h).1.2.1 i hi
    · simp [labels, hi, hk]
  · simp [badOp, h, hk]

def Extends (R : Rel.{u} Row) (kappa : Label.{u}) (A : Shape Row)
    (pref : Fin A.cut → Label.{u}) (f : Fin A.diagram.size → Label.{u}) : Prop :=
  Representation (· < ·) domain R A.diagram (labels f) ∧
  Bounded (· < ·) A.diagram.size (labels f) kappa ∧
  (∀ i : Fin A.cut, labels f i = pref i) ∧
  Ends R A.needs (labels f) kappa

noncomputable def leastExtension (R : Rel.{u} Row) (kappa : Label.{u}) (A : Shape Row)
    (pref : Fin A.cut → Label.{u}) (h : ∃ f, Extends R kappa A pref f) :
    Fin A.diagram.size → Label.{u} :=
  (tupleEarlier_wellFounded A.diagram.size).min {f | Extends R kappa A pref f} h

theorem leastExtension_spec (R : Rel.{u} Row) (kappa : Label.{u}) (A : Shape Row)
    (pref : Fin A.cut → Label.{u}) (h : ∃ f, Extends R kappa A pref f) :
    Extends R kappa A pref (leastExtension R kappa A pref h) :=
  (tupleEarlier_wellFounded A.diagram.size).min_mem _ h

noncomputable def extOp (R : Rel.{u} Row) (kappa : Label.{u}) (A : Shape Row) (i : Nat)
    (pref : Fin A.cut → Label.{u}) : Label.{u} := by
  classical
  exact if h : ∃ f, Extends R kappa A pref f
    then labels (leastExtension R kappa A pref h) i else 0

theorem extOp_eq (R : Rel.{u} Row) (kappa : Label.{u}) (A : Shape Row) (i : Nat)
    (pref : Fin A.cut → Label.{u}) (h : ∃ f, Extends R kappa A pref f) :
    extOp R kappa A i pref = labels (leastExtension R kappa A pref h) i := by
  simp [extOp, h]

theorem extOp_lt (R : Rel.{u} Row) (kappa : Label.{u}) (A : Shape Row) (i : Nat)
    (pref : Fin A.cut → Label.{u}) (hk : 0 < kappa) : extOp R kappa A i pref < kappa := by
  classical
  by_cases h : ∃ f, Extends R kappa A pref f
  · rw [extOp_eq R kappa A i pref h]
    by_cases hi : i < A.diagram.size
    · exact (leastExtension_spec R kappa A pref h).2.1 i hi
    · simp [labels, hi, hk]
  · simp [extOp, h, hk]

end FiniteDemand

#print axioms FiniteDemand.exists_bad
#print axioms FiniteDemand.leastBad_spec
#print axioms FiniteDemand.badOp_lt
#print axioms FiniteDemand.leastExtension_spec
#print axioms FiniteDemand.extOp_lt
