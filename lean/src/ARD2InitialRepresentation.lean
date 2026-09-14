import ARD2ClosedSupply
import FiniteDemandHostAmbient

/-! Unconditional ordinary-Lean initial representations. The finite template
rebinding handles row SELF, root SELF, and double SELF without fixing either
coordinate to the parent. The ambient below is instantiated by actual omega1. -/
namespace ARD2Demand
open OrdinalFormal
open OrdinalFormal.ReflectionTransport
set_option autoImplicit false
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

theorem atEnd_prefix {n : Nat} (f : Nat → Label.{u}) (i : Nat) (hi : i ≤ n) :
    ARD2.atEnd n (labels (fun j : Fin n => f j)) (f n) i = f i := by
  by_cases hlt : i < n
  · simp [ARD2.atEnd,hlt,labels]
  · have heq : i = n := by omega
    subst i
    simp [ARD2.atEnd]

theorem heightSequence_represents (E : Ambient.{u}) (G : ARD2.Graph) (hv : ARD2.Valid G) :
    ARD2.Holds (· < ·) domain relation G (heightSequence E) := by
  let f := heightSequence E
  have hf : StrictMono f := heightSequence_strictMono E
  refine ⟨(fun i _ => (heightSequence_closed E i).2.1),(fun i j hij _ => hf hij),?_⟩
  intro j a ha
  rcases hv j a ha with ⟨hrow,hroot,hparent⟩
  have hp := heightSequence_closed E a.parent
  have hc := heightSequence_closed E j
  let T := Template.ofEntry j a ⟨hrow,hroot,hparent⟩
  let F : Fin j → Label.{u} := fun i => f i
  have hrel := closed_heights_related (hf hparent) hc.1 hp.2.1 hp.2.2.1 hp.2.2.2 hc.2.2.1
    T F (fun i => hf i.isLt)
  change relation (ARD2.atEnd j (labels (fun i : Fin j => f i)) (f j) a.row)
    (ARD2.atEnd j (labels (fun i : Fin j => f i)) (f j) a.root) (f a.parent) (f j) at hrel
  rw [atEnd_prefix f a.row hrow,atEnd_prefix f a.root hroot] at hrel
  exact hrel

theorem initial_representation (E : Ambient.{u}) (G : ARD2.Graph) (hv : ARD2.Valid G) :
    ∃ f, ARD2.Holds (· < ·) domain relation G f ∧
      Bounded (· < ·) G.length f E.kappa :=
  ⟨heightSequence E,heightSequence_represents E G hv,fun i _ => (heightSequence_closed E i).1⟩

theorem initial (G : ARD2.Graph) (hv : ARD2.Valid G) :
    ∃ f : Nat → Label.{u}, ARD2.Holds (· < ·) domain relation G f ∧
      Bounded (· < ·) G.length f FiniteDemand.HostAmbient.actual.kappa :=
  initial_representation FiniteDemand.HostAmbient.actual G hv

end ARD2Demand

#print axioms ARD2Demand.heightSequence_represents
#print axioms ARD2Demand.initial
