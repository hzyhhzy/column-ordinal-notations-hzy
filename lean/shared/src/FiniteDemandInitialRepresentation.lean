import FiniteDemandClosedSupply
import OrdinalFormal.ColumnRepresentation

/-!
# Initial representations from the paper's auxiliary enumeration hypothesis

Successive heights are the explicitly defined finitary hull heights; no
dependent sequence of ad hoc semantic choices is assumed. Every finite valid
diagram, including diagrams with arbitrary internal row labels, is represented.

`Ambient` is precisely the remaining ambient ordinal/enumeration input, not an
assumption that any diagrams have representations or that reflection holds.
Its host-Lean instantiation and weak-theory L construction are separate steps.
-/

namespace FiniteDemand
open OrdinalFormal.ReflectionTransport

universe u v
variable {Row : Type v} [Countable Row]

structure Ambient where
  kappa : Label.{u}
  enumerate : Label.{u} → Nat → Label.{u}
  omega_lt : Ordinal.omega0 < kappa
  uncountable : ¬ (Set.Iio kappa).Countable
  bounded : ∀ a, a < kappa → ∀ n, enumerate a n < kappa
  covers : ∀ a, a < kappa → ∀ b, b < a → ∃ n, enumerate a n = b

def ClosedHeight (rowLt : Row → Row → Prop) (hw : WellFounded rowLt)
    (E : Ambient.{u}) (a : Label.{u}) : Prop :=
  a < E.kappa ∧ domain a ∧ BadClosed rowLt hw E.kappa a ∧
    ExtClosed (relation rowLt hw) E.kappa a

noncomputable def heightSequence (rowLt : Row → Row → Prop) (hw : WellFounded rowLt)
    (E : Ambient.{u}) : Nat → Label.{u}
  | 0 => ClosedSupply.nextHeight rowLt hw E.kappa E.enumerate 0
  | n + 1 => ClosedSupply.nextHeight rowLt hw E.kappa E.enumerate (heightSequence rowLt hw E n)

theorem next_height_spec (rowLt : Row → Row → Prop) (hw : WellFounded rowLt)
    (E : Ambient.{u}) (a : Label.{u}) (ha : a < E.kappa) :
    a < ClosedSupply.nextHeight rowLt hw E.kappa E.enumerate a ∧
    ClosedHeight rowLt hw E (ClosedSupply.nextHeight rowLt hw E.kappa E.enumerate a) :=
  ClosedSupply.nextHeight_spec rowLt hw E.enumerate E.omega_lt E.uncountable
    E.bounded E.covers a ha

theorem heightSequence_closed (rowLt : Row → Row → Prop) (hw : WellFounded rowLt)
    (E : Ambient.{u}) (n : Nat) : ClosedHeight rowLt hw E (heightSequence rowLt hw E n) := by
  induction n with
  | zero => exact (next_height_spec rowLt hw E 0 (lt_trans Ordinal.omega0_pos E.omega_lt)).2
  | succ n ih => exact (next_height_spec rowLt hw E _ ih.1).2

theorem heightSequence_strictMono (rowLt : Row → Row → Prop) (hw : WellFounded rowLt)
    (E : Ambient.{u}) : StrictMono (heightSequence rowLt hw E) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact (next_height_spec rowLt hw E _ (heightSequence_closed rowLt hw E n).1).1

theorem heightSequence_represents (rowLt : Row → Row → Prop) (hw : WellFounded rowLt)
    (E : Ambient.{u}) (G : Diagram Row) :
    Representation (· < ·) domain (relation rowLt hw) G (heightSequence rowLt hw E) := by
  let f := heightSequence rowLt hw E
  have hf := heightSequence_strictMono rowLt hw E
  refine ⟨(fun i _ => (heightSequence_closed rowLt hw E i).2.1), (fun i j hij _ => hf hij), ?_⟩
  intro e he
  rcases G.valid e he with ⟨hrp, hpc, _hc⟩
  have hp := heightSequence_closed rowLt hw E e.parent
  have hc := heightSequence_closed rowLt hw E e.child
  exact closed_heights_related rowLt hw (hf hpc) hc.1 hp.2.1 hp.2.2.1 hp.2.2.2 hc.2.2.1
    e.layer (f e.root) (hf.monotone hrp)

theorem initial_representation (rowLt : Row → Row → Prop) (hw : WellFounded rowLt)
    (E : Ambient.{u}) (G : Diagram Row) :
    ∃ f, Representation (· < ·) domain (relation rowLt hw) G f ∧
      Bounded (· < ·) G.size f E.kappa :=
  ⟨heightSequence rowLt hw E, heightSequence_represents rowLt hw E G,
    fun i _ => (heightSequence_closed rowLt hw E i).1⟩

/-- Exact initial supply for the already proved executable column interfaces. -/
theorem initial_columns (rowLt : Row → Row → Prop) (hw : WellFounded rowLt)
    (E : Ambient.{u}) (g : OrdinalFormal.Columns.Graph Row) (hg : OrdinalFormal.Columns.Valid g) :
    ∃ f : Nat → Label.{u},
      OrdinalFormal.ColumnRepresentation.Holds (· < ·) domain (relation rowLt hw) g f := by
  obtain ⟨f, hf, _⟩ := initial_representation rowLt hw E
    (OrdinalFormal.ColumnRepresentation.toDiagram g hg)
  exact ⟨f, (OrdinalFormal.ColumnRepresentation.holds_iff_representation
    (· < ·) domain (relation rowLt hw) g hg f).mpr hf⟩

end FiniteDemand

#print axioms FiniteDemand.heightSequence_strictMono
#print axioms FiniteDemand.heightSequence_represents
#print axioms FiniteDemand.initial_columns
