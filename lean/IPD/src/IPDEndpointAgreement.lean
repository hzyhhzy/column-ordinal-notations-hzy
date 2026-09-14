import IPDWitnesses

/-! Endpoint coherence for moving SELF profiles, proved by the actual
profile-parent well-order. The closure conditions below are subsequently
constructed by countably many actual witness operations. -/

namespace IPD.Semantics
set_option autoImplicit false
set_option maxHeartbeats 1200000
universe u

def RootEarlier : (Profile Label.{u} × Label.{u}) → (Profile Label.{u} × Label.{u}) → Prop :=
  Prod.Lex (· < ·) (· < ·)

theorem rootEarlier_wellFounded : WellFounded RootEarlier.{u} :=
  (profile_wellFounded Label.{u}).prod_lex Ordinal.lt_wf

def BadClosed (kappa delta : Label.{u}) : Prop :=
  ∀ (T : Template) i (f : Fin T.arity → Label.{u}) a,
    (∀ j, f j < delta) → a < delta → badOp T i f a kappa < delta

def ExtClosed (R : Rel.{u}) (kappa delta : Label.{u}) : Prop :=
  ∀ (A : Shape) i (pref : Fin A.cut → Label.{u}),
    (∀ j, pref j < delta) → extOp R kappa A i pref < delta

theorem bounded_tuple {n : Nat} {f : Fin n → Label.{u}} {b : Label.{u}}
    (hf : Bounded n (labels f) b) : ∀ i, f i < b := by
  intro i
  simpa only [labels_apply f i.isLt] using hf i i.isLt

theorem admissible_endpoint_iff {kappa delta : Label.{u}} (hdk : delta ≤ kappa)
    (T : Template) (p : Fin T.arity → Label.{u}) (hp : ∀ i, p i < delta)
    (a : Label.{u}) (A : Shape) (f : Fin A.graph.length → Label.{u})
    (hf : Bounded A.graph.length (labels f) delta) (e : Edge) (he : e ∈ A.needs) :
    Admissible (kappa,T.eval p kappa,a) A.graph.length (labels f) e ↔
      Admissible (delta,T.eval p delta,a) A.graph.length (labels f) e := by
  let U := Template.ofEdge A.graph.length e (A.needs_valid e he)
  change Prod.Lex (· < ·) (· < ·) (U.eval f kappa,labels f e.parent) (T.eval p kappa,a) ↔
    Prod.Lex (· < ·) (· < ·) (U.eval f delta,labels f e.parent) (T.eval p delta,a)
  rw [Prod.lex_def,Prod.lex_def,
    template_lt_endpoint_iff hdk U T f p (bounded_tuple hf) hp,
    template_eq_endpoint_iff hdk U T f p (bounded_tuple hf) hp]

def AgreementBelow (delta kappa : Label.{u}) (s : Profile Label.{u} × Label.{u}) : Prop :=
  ∀ (T : Template) (p : Fin T.arity → Label.{u}) a,
    RootEarlier (T.eval p delta,a) s → (∀ i, p i < delta) → a < delta →
      (relation (T.eval p kappa) a kappa ↔ relation (T.eval p delta) a delta)

theorem ends_endpoint_iff {kappa delta : Label.{u}} {s : Profile Label.{u} × Label.{u}}
    (ih : AgreementBelow delta kappa s) {A : Shape} {f : Fin A.graph.length → Label.{u}}
    (hb : Bounded A.graph.length (labels f) delta)
    (ha : ∀ e ∈ A.needs, Admissible (delta,s.1,s.2) A.graph.length (labels f) e) :
    Ends relation A.graph.length A.needs (labels f) kappa ↔
      Ends relation A.graph.length A.needs (labels f) delta := by
  have he : ∀ e ∈ A.needs,
      relation (endpointProfile A.graph.length (labels f) kappa e) (labels f e.parent) kappa ↔
      relation (endpointProfile A.graph.length (labels f) delta e) (labels f e.parent) delta := by
    intro e he
    exact ih (Template.ofEdge A.graph.length e (A.needs_valid e he)) f (labels f e.parent)
      (ha e he) (bounded_tuple hb) (hb e.parent (A.needs_valid e he).1)
  exact ⟨fun h e hem => (he e hem).mp (h e hem),fun h e hem => (he e hem).mpr (h e hem)⟩

theorem endpoint_agreement {kappa delta : Label.{u}} (hdk : delta < kappa)
    (hclosed : BadClosed kappa delta) (T : Template) (p : Fin T.arity → Label.{u})
    (hp : ∀ i, p i < delta) (a : Label.{u}) (ha : a < delta) :
    relation (T.eval p kappa) a kappa ↔ relation (T.eval p delta) a delta := by
  have hall : ∀ s : Profile Label.{u} × Label.{u},
      ∀ (T : Template) (p : Fin T.arity → Label.{u}), (∀ i, p i < delta) →
      T.eval p delta = s.1 → s.2 < delta →
      (relation (T.eval p kappa) s.2 kappa ↔ relation (T.eval p delta) s.2 delta) := by
    intro s
    induction s using rootEarlier_wellFounded.induction with
    | h s ih =>
      intro T p hp hs ha
      have ih' : AgreementBelow delta kappa s := by
        intro U q b he hq hb
        exact ih (U.eval q delta,b) he U q hq rfl hb
      constructor
      · intro hr
        have hrule := (relation_iff (T.eval p kappa) s.2 kappa).mp hr
        apply (relation_iff (T.eval p delta) s.2 delta).mpr
        refine ⟨⟨hrule.1.1,ha,
          (template_valid_endpoint_iff hdk ha T p hp).mp hrule.1.2.2⟩,?_⟩
        intro A f hf
        apply hrule.2 A f
        refine ⟨hf.1,(fun i hi => lt_trans (hf.2.1 i hi) hdk),hf.2.2.1,?_,?_⟩
        · intro e he
          exact (admissible_endpoint_iff hdk.le T p hp s.2 A f hf.2.1 e he).mpr
            (hf.2.2.2.1 e he)
        · apply (ends_endpoint_iff ih' hf.2.1 ?_).mpr hf.2.2.2.2
          simpa only [hs] using hf.2.2.2.1
      · intro hr
        classical
        by_contra hn
        have hg : Guard (kappa,T.eval p kappa,s.2) :=
          ⟨parent_domain hr,lt_trans ha hdk,
            (template_valid_endpoint_iff hdk ha T p hp).mpr (profile_valid hr)⟩
        have hex := exists_bad hg hn
        let q := leastBad (T.eval p kappa) s.2 kappa hex
        have hq : Bad (T.eval p kappa) s.2 kappa q :=
          leastBad_spec (T.eval p kappa) s.2 kappa hex
        have hqb : Bounded q.1.graph.length (labels q.2) delta := by
          intro i _hi
          rw [← badOp_eq T i p s.2 kappa hex]
          exact hclosed T i p s.2 hp ha
        have had : ∀ e ∈ q.1.needs,
            Admissible (delta,T.eval p delta,s.2) q.1.graph.length (labels q.2) e := by
          intro e he
          exact (admissible_endpoint_iff hdk.le T p hp s.2 q.1 q.2 hqb e he).mp
            (hq.1.2.2.2.1 e he)
        have hin : Input relation (delta,T.eval p delta,s.2) q.1 q.2 := by
          refine ⟨hq.1.1,hqb,hq.1.2.2.1,had,?_⟩
          apply (ends_endpoint_iff ih' hqb ?_).mp hq.1.2.2.2.2
          simpa only [hs] using had
        exact hq.2 (((relation_iff (T.eval p delta) s.2 delta).mp hr).2 q.1 q.2 hin)
  exact hall (T.eval p delta,a) T p hp rfl ha

/-- The controlling profile itself need not lie below the reflected height.
The extension witness forgets it, and retains only the prefix and endpoint needs. -/
theorem closed_reflects {kappa delta : Label.{u}} (hdk : delta < kappa) (hd : domain delta)
    (hbad : BadClosed kappa delta) (hext : ExtClosed relation kappa delta)
    (t : Profile Label.{u}) (hv : ProfileAtoms (fun x => x ≤ delta ∨ x = kappa) t) :
    relation t delta kappa := by
  apply (relation_iff t delta kappa).mpr
  refine ⟨⟨hd,hdk,hv⟩,?_⟩
  intro A f hf
  let pref : Fin A.cut → Label.{u} := fun i => labels f i
  have hpref : ∀ i, pref i < delta := by
    intro i
    change labels f i < delta
    have hcut : labels f A.cut = delta := hf.2.2.1
    rw [← hcut]
    exact hf.1.ordered i A.cut i.isLt A.cut_lt
  have hex : ∃ g, Extends relation kappa A pref g :=
    ⟨f,hf.1,hf.2.1,(fun _ => rfl),hf.2.2.2.2⟩
  let g := leastExtension relation kappa A pref hex
  have hg : Extends relation kappa A pref g := leastExtension_spec relation kappa A pref hex
  have hgb : Bounded A.graph.length (labels g) delta := by
    intro i _hi
    rw [← extOp_eq relation kappa A i pref hex]
    exact hext A i pref hpref
  refine ⟨g,hg.1,?_,hgb,?_⟩
  · intro i hi
    exact hg.2.2.1 ⟨i,hi⟩
  · intro e he
    exact (endpoint_agreement hdk hbad (Template.ofEdge A.graph.length e (A.needs_valid e he))
      g (bounded_tuple hgb) (labels g e.parent) (hgb e.parent (A.needs_valid e he).1)).mp
        (hg.2.2.2 e he)

theorem closed_heights_related {kappa alpha beta : Label.{u}} (hab : alpha < beta)
    (hbk : beta < kappa) (ha : domain alpha) (hbadA : BadClosed kappa alpha)
    (hextA : ExtClosed relation kappa alpha) (hbadB : BadClosed kappa beta)
    (T : Template) (f : Fin T.arity → Label.{u}) (hf : ∀ i, f i < beta)
    (hv : ProfileAtoms (fun x => x ≤ alpha ∨ x = kappa) (T.eval f kappa)) :
    relation (T.eval f beta) alpha beta :=
  (endpoint_agreement hbk hbadB T f hf alpha hab).mp
    (closed_reflects (lt_trans hab hbk) ha hbadA hextA (T.eval f kappa) hv)

end IPD.Semantics

#print axioms IPD.Semantics.admissible_endpoint_iff
#print axioms IPD.Semantics.endpoint_agreement
#print axioms IPD.Semantics.closed_reflects
#print axioms IPD.Semantics.closed_heights_related
