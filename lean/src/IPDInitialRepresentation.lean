import IPDClosedSupply
import IPDFiniteLabels
import FiniteDemandHostAmbient

/-! Unconditional ordinary-Lean representation supply for every valid finite
IPD graph. The generic omega-one ambient object supplies only ordinals and
their enumerators, not a notation relation, reflection, or well-ordering. -/

namespace IPD.Semantics
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

theorem heightSequence_closed (E : Ambient.{u}) (n : Nat) : ClosedHeight E (heightSequence E n) := by
  induction n with
  | zero => exact (next_height_spec E 0 (lt_trans Ordinal.omega0_pos E.omega_lt)).2
  | succ n ih => exact (next_height_spec E _ ih.1).2

theorem heightSequence_strictMono (E : Ambient.{u}) : StrictMono (heightSequence E) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact (next_height_spec E _ (heightSequence_closed E n).1).1

theorem heightSequence_represents (E : Ambient.{u}) (G : Graph) (hv : Valid G) :
    Rep relation G (heightSequence E) := by
  let f := heightSequence E
  have hf := heightSequence_strictMono E
  refine ⟨(fun i _ => (heightSequence_closed E i).2.1),(fun i j hij _ => hf hij),?_⟩
  intro j e he
  have hev := hv j e he
  have hp := heightSequence_closed E e.parent
  have hc := heightSequence_closed E j
  let T := Template.ofEdge j e hev
  let p : Fin j → Label.{u} := fun i => f i
  have hroot : ∀ i : Fin j, p i < f j := fun i => hf i.isLt
  have hvalid : ProfileAtoms (fun x => x ≤ f e.parent ∨ x = E.kappa) (T.eval p E.kappa) := by
    change ProfileAtoms _ ((Template.ofEdge j e hev).eval (fun i => f i) E.kappa)
    rw [Template.ofEdge_eval]
    apply profileAtoms_rename _ _ _ ?_ _ hev.2
    intro i hi
    rcases hi with hi | rfl
    · have hij : i < j := lt_of_le_of_lt hi hev.1
      exact Or.inl (by simpa [endpointMap,ne_of_lt hij] using hf.monotone hi)
    · exact Or.inr (by simp [endpointMap])
  have hr := closed_heights_related (hf hev.1) hc.1 hp.2.1 hp.2.2.1 hp.2.2.2 hc.2.2.1
    T p hroot hvalid
  change relation ((Template.ofEdge j e hev).eval (fun i => f i) (f j)) (f e.parent) (f j) at hr
  rw [Template.ofEdge_eval j e hev f (f j),endpointProfile_self] at hr
  exact hr

theorem initial_representation (E : Ambient.{u}) (G : Graph) (hv : Valid G) :
    ∃ f, Rep relation G f ∧ Bounded G.length f E.kappa :=
  ⟨heightSequence E,heightSequence_represents E G hv,fun i _ => (heightSequence_closed E i).1⟩

theorem initial (G : Graph) (hv : Valid G) :
    ∃ f : Nat → Label.{u}, Rep relation G f ∧
      Bounded G.length f FiniteDemand.HostAmbient.actual.kappa :=
  initial_representation FiniteDemand.HostAmbient.actual G hv

end IPD.Semantics

#print axioms IPD.Semantics.heightSequence_represents
#print axioms IPD.Semantics.initial
