import ARDClosedSupply
import FiniteDemandHostAmbient
/-! Unconditional ordinary-Lean initial supply for every valid finite ARD graph.
The only intermediate ambient structure is instantiated below by the existing
actual omega-one environment; no reflection or accessibility premise remains. -/
namespace ARDDemand
open OrdinalFormal
open OrdinalFormal.ReflectionTransport
universe u
abbrev Ambient := FiniteDemand.Ambient.{u}
def ClosedHeight (E : Ambient.{u}) (a : Label.{u}) : Prop :=
  a < E.kappa ∧ domain a ∧ BadClosed E.kappa a ∧ ExtClosed relation E.kappa a
noncomputable def heightSequence (E : Ambient.{u}) : Nat → Label.{u}
  | 0 => ClosedSupply.nextHeight E.kappa E.enumerate 0
  | n+1 => ClosedSupply.nextHeight E.kappa E.enumerate (heightSequence E n)
theorem next_height_spec (E : Ambient.{u}) (a : Label.{u}) (ha : a < E.kappa) :
    a < ClosedSupply.nextHeight E.kappa E.enumerate a ∧
      ClosedHeight E (ClosedSupply.nextHeight E.kappa E.enumerate a) :=
  ClosedSupply.nextHeight_spec E.enumerate E.omega_lt E.uncountable E.bounded E.covers a ha
theorem heightSequence_closed (E : Ambient.{u}) (n : Nat) :
    ClosedHeight E (heightSequence E n) := by
  induction n with
  | zero => exact (next_height_spec E 0 (lt_trans Ordinal.omega0_pos E.omega_lt)).2
  | succ n ih => exact (next_height_spec E _ ih.1).2
theorem heightSequence_strictMono (E : Ambient.{u}) : StrictMono (heightSequence E) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact (next_height_spec E _ (heightSequence_closed E n).1).1
theorem heightSequence_represents (E : Ambient.{u}) (G : ARD.Graph) (hv : ARD.Valid G) :
    ARD.Holds (· < ·) domain relation G (heightSequence E) := by
  let f := heightSequence E
  have hf := heightSequence_strictMono E
  refine ⟨(fun i _ => (heightSequence_closed E i).2.1),(fun i j hij _ => hf hij),?_⟩
  intro j a ha
  rcases hv j a ha with ⟨hrow,hroot,hparent⟩
  have hp := heightSequence_closed E a.parent
  have hc := heightSequence_closed E j
  exact closed_heights_related (hf hparent) hc.1 hp.2.1 hp.2.2.1 hp.2.2.2 hc.2.2.1
    (f a.row) (f a.root) (hf hrow) (hf.monotone hroot)
theorem initial_representation (E : Ambient.{u}) (G : ARD.Graph) (hv : ARD.Valid G) :
    ∃ f, ARD.Holds (· < ·) domain relation G f ∧ Bounded (· < ·) G.length f E.kappa :=
  ⟨heightSequence E,heightSequence_represents E G hv,fun i _ => (heightSequence_closed E i).1⟩
theorem initial (G : ARD.Graph) (hv : ARD.Valid G) :
    ∃ f : Nat → Label.{u}, ARD.Holds (· < ·) domain relation G f ∧
      Bounded (· < ·) G.length f FiniteDemand.HostAmbient.actual.kappa :=
  initial_representation FiniteDemand.HostAmbient.actual G hv
end ARDDemand
#print axioms ARDDemand.heightSequence_represents
#print axioms ARDDemand.initial
