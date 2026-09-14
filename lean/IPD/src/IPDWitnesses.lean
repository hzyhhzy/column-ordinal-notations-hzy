import IPDTemplates
import Mathlib.Data.List.Shortlex

/-! Actual least failed demands and least finite extensions. The operations
used by the countable hull are indexed by finite templates, not by semantic
ordinal profiles. These definitions assert no reflection principle. -/

namespace IPD.Semantics
set_option autoImplicit false
universe u

abbrev Packet := (A : Shape) × (Fin A.graph.length → Label.{u})

noncomputable def shapeCode (A : Shape) : Nat :=
  @Encodable.encode _ (Encodable.ofCountable Shape) A

def TupleEarlier {n : Nat} : (Fin n → Label.{u}) → (Fin n → Label.{u}) → Prop :=
  InvImage (List.Shortlex (· < ·)) List.ofFn

theorem tupleEarlier_wellFounded (n : Nat) : WellFounded (@TupleEarlier.{u} n) :=
  InvImage.wf List.ofFn (List.Shortlex.wf Ordinal.lt_wf)

noncomputable def PacketEarlier : Packet.{u} → Packet.{u} → Prop :=
  InvImage (Prod.Lex (· < ·) (List.Shortlex (· < ·)))
    (fun p => (shapeCode p.1,List.ofFn p.2))

theorem packetEarlier_wellFounded : WellFounded PacketEarlier.{u} :=
  InvImage.wf _ (Nat.lt_wfRel.wf.prod_lex (List.Shortlex.wf Ordinal.lt_wf))

def Bad (t : Profile Label.{u}) (a kappa : Label.{u}) (p : Packet.{u}) : Prop :=
  Input relation (kappa,t,a) p.1 p.2 ∧ ¬ ∃ g, Output relation a p.1 p.2 g

theorem exists_bad {t : Profile Label.{u}} {a kappa : Label.{u}}
    (hg : Guard (kappa,t,a)) (hn : ¬ relation t a kappa) : ∃ p, Bad t a kappa p := by
  classical
  have hd : ¬ Demands relation (kappa,t,a) := by
    intro hd
    exact hn ((relation_iff t a kappa).mpr ⟨hg,hd⟩)
  simp only [Demands,not_forall,_root_.not_imp] at hd
  obtain ⟨A,f,hf,hn⟩ := hd
  exact ⟨⟨A,f⟩,hf,hn⟩

noncomputable def leastBad (t : Profile Label.{u}) (a kappa : Label.{u})
    (h : ∃ p, Bad t a kappa p) : Packet.{u} :=
  packetEarlier_wellFounded.min {p | Bad t a kappa p} h

theorem leastBad_spec (t : Profile Label.{u}) (a kappa : Label.{u})
    (h : ∃ p, Bad t a kappa p) : Bad t a kappa (leastBad t a kappa h) :=
  packetEarlier_wellFounded.min_mem _ h

noncomputable def badOp (T : Template) (i : Nat) (f : Fin T.arity → Label.{u})
    (a kappa : Label.{u}) : Label.{u} := by
  classical
  exact if h : ∃ p, Bad (T.eval f kappa) a kappa p
    then labels (leastBad (T.eval f kappa) a kappa h).2 i else 0

theorem badOp_eq (T : Template) (i : Nat) (f : Fin T.arity → Label.{u})
    (a kappa : Label.{u}) (h : ∃ p, Bad (T.eval f kappa) a kappa p) :
    badOp T i f a kappa = labels (leastBad (T.eval f kappa) a kappa h).2 i := by
  simp [badOp,h]

theorem badOp_lt (T : Template) (i : Nat) (f : Fin T.arity → Label.{u})
    (a kappa : Label.{u}) (hk : 0 < kappa) : badOp T i f a kappa < kappa := by
  classical
  by_cases h : ∃ p, Bad (T.eval f kappa) a kappa p
  · rw [badOp_eq T i f a kappa h]
    by_cases hi : i < (leastBad (T.eval f kappa) a kappa h).1.graph.length
    · exact (leastBad_spec (T.eval f kappa) a kappa h).1.2.1 i hi
    · simp [labels,hi,hk]
  · simp [badOp,h,hk]

def Extends (R : Rel.{u}) (kappa : Label.{u}) (A : Shape)
    (pref : Fin A.cut → Label.{u}) (f : Fin A.graph.length → Label.{u}) : Prop :=
  Rep R A.graph (labels f) ∧ Bounded A.graph.length (labels f) kappa ∧
  (∀ i : Fin A.cut, labels f i = pref i) ∧ Ends R A.graph.length A.needs (labels f) kappa

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
  simp [extOp,h]

theorem extOp_lt (R : Rel.{u}) (kappa : Label.{u}) (A : Shape) (i : Nat)
    (pref : Fin A.cut → Label.{u}) (hk : 0 < kappa) : extOp R kappa A i pref < kappa := by
  classical
  by_cases h : ∃ f, Extends R kappa A pref f
  · rw [extOp_eq R kappa A i pref h]
    by_cases hi : i < A.graph.length
    · exact (leastExtension_spec R kappa A pref h).2.1 i hi
    · simp [labels,hi,hk]
  · simp [extOp,h,hk]

end IPD.Semantics

#print axioms IPD.Semantics.exists_bad
#print axioms IPD.Semantics.leastBad_spec
#print axioms IPD.Semantics.badOp_lt
#print axioms IPD.Semantics.leastExtension_spec
#print axioms IPD.Semantics.extOp_lt
