import ARD2Witnesses

/-! Endpoint coherence for two independently moving SELF coordinates. The
pair induction interleaves all four SELF cases; the closure predicates are
subsequently constructed from actual least witness operations. -/
namespace ARD2Demand
open OrdinalFormal
open OrdinalFormal.ReflectionTransport
set_option autoImplicit false
set_option maxHeartbeats 1200000
universe u

def BadClosed (kappa delta : Label.{u}) : Prop :=
  ∀ (T : Template) i (f : Fin T.arity → Label.{u}) a,
    (∀ j, f j < delta) → a < delta → badOp T i f a kappa < delta

def ExtClosed (R : Rel.{u}) (kappa delta : Label.{u}) : Prop :=
  ∀ (A : Shape) i (pref : Fin A.cut → Label.{u}),
    (∀ j, pref j < delta) → extOp R kappa A i pref < delta

theorem bounded_tuple {n : Nat} {f : Fin n → Label.{u}} {b : Label.{u}}
    (hf : Bounded (· < ·) n (labels f) b) : ∀ i, f i < b := by
  intro i
  simpa only [labels_apply f i.isLt] using hf i i.isLt

theorem admissible_endpoint_iff {kappa delta : Label.{u}} (hdk : delta ≤ kappa)
    (T : Template) (p : Fin T.arity → Label.{u}) (hp : ∀ i, p i < delta)
    (A : Shape) (f : Fin A.graph.length → Label.{u})
    (hf : Bounded (· < ·) A.graph.length (labels f) delta)
    (e : ARD2.Entry) (he : e ∈ A.needs) :
    ARD2.Admissible (· < ·) (T.eval p kappa).1 (T.eval p kappa).2
      A.graph.length (labels f) kappa e ↔
    ARD2.Admissible (· < ·) (T.eval p delta).1 (T.eval p delta).2
      A.graph.length (labels f) delta e := by
  have h := template_lt_endpoint_iff hdk
    (Template.ofEntry A.graph.length e (A.needs_valid e he)) T f p (bounded_tuple hf) hp
  simpa only [RootEarlier,Prod.lex_def,Template.eval,Template.ofEntry,ARD2.Admissible] using h

def AgreementBelow (delta kappa : Label.{u}) (s : Label.{u} × Label.{u}) : Prop :=
  ∀ (T : Template) (p : Fin T.arity → Label.{u}) a,
    RootEarlier (T.eval p delta) s → (∀ i, p i < delta) → a < delta →
      (pairRelation (T.eval p kappa) a kappa ↔ pairRelation (T.eval p delta) a delta)

theorem ends_endpoint_iff {kappa delta : Label.{u}} {s : Label.{u} × Label.{u}}
    (ih : AgreementBelow delta kappa s) {A : Shape}
    {f : Fin A.graph.length → Label.{u}}
    (hb : Bounded (· < ·) A.graph.length (labels f) delta)
    (ha : ∀ e ∈ A.needs,
      ARD2.Admissible (· < ·) s.1 s.2 A.graph.length (labels f) delta e) :
    ARD2.Ends relation A.graph.length A.needs (labels f) kappa ↔
      ARD2.Ends relation A.graph.length A.needs (labels f) delta := by
  have he : ∀ e ∈ A.needs,
      relation (ARD2.atEnd A.graph.length (labels f) kappa e.row)
        (ARD2.atEnd A.graph.length (labels f) kappa e.root) (labels f e.parent) kappa ↔
      relation (ARD2.atEnd A.graph.length (labels f) delta e.row)
        (ARD2.atEnd A.graph.length (labels f) delta e.root) (labels f e.parent) delta := by
    intro e hem
    apply ih (Template.ofEntry A.graph.length e (A.needs_valid e hem)) f (labels f e.parent)
    · simpa only [RootEarlier,Prod.lex_def,Template.eval,Template.ofEntry,ARD2.Admissible]
        using ha e hem
    · exact bounded_tuple hb
    · exact hb e.parent (A.needs_valid e hem).2.2
  exact ⟨fun h e hem => (he e hem).mp (h e hem),fun h e hem => (he e hem).mpr (h e hem)⟩

theorem endpoint_agreement {kappa delta : Label.{u}} (hdk : delta < kappa)
    (hclosed : BadClosed kappa delta) (T : Template) (p : Fin T.arity → Label.{u})
    (hp : ∀ i, p i < delta) (a : Label.{u}) (ha : a < delta) :
    pairRelation (T.eval p kappa) a kappa ↔ pairRelation (T.eval p delta) a delta := by
  have hall : ∀ s : Label.{u} × Label.{u},
      ∀ (T : Template) (p : Fin T.arity → Label.{u}), (∀ i, p i < delta) →
      T.eval p delta = s → ∀ a, a < delta →
      (pairRelation (T.eval p kappa) a kappa ↔ pairRelation (T.eval p delta) a delta) := by
    intro s
    induction s using rootEarlier_wellFounded.induction with
    | h s ih =>
      intro T p hp hs a ha
      have ih' : AgreementBelow delta kappa s := by
        intro U q b he hq hb
        exact ih (U.eval q delta) he U q hq rfl b hb
      constructor
      · intro hr
        have hrule := (pair_relation_iff (T.eval p kappa) a kappa).mp hr
        apply (pair_relation_iff (T.eval p delta) a delta).mpr
        have hbound := T.eval_bounded p hp
        refine ⟨⟨hbound.1,hbound.2,ha,hrule.1.2.2.2⟩,?_⟩
        intro A f hf
        apply hrule.2 A f
        refine ⟨hf.1,(fun i hi => lt_trans (hf.2.1 i hi) hdk),hf.2.2.1,?_,?_⟩
        · intro e he
          exact (admissible_endpoint_iff hdk.le T p hp A f hf.2.1 e he).mpr
            (hf.2.2.2.1 e he)
        · apply (ends_endpoint_iff ih' hf.2.1 ?_).mpr hf.2.2.2.2
          simpa only [hs] using hf.2.2.2.1
      · intro hr
        classical
        by_contra hn
        have hbound := T.eval_bounded p (fun i => lt_trans (hp i) hdk)
        have hg : Guard (kappa,T.eval p kappa) a :=
          ⟨hbound.1,hbound.2,lt_trans ha hdk,pair_parent_domain hr⟩
        have hex := exists_bad hg hn
        let q := leastBad (T.eval p kappa) a kappa hex
        have hq : Bad (T.eval p kappa) a kappa q :=
          leastBad_spec (T.eval p kappa) a kappa hex
        have hqb : Bounded (· < ·) q.1.graph.length (labels q.2) delta := by
          intro i _hi
          rw [← badOp_eq T i p a kappa hex]
          exact hclosed T i p a hp ha
        have had : ∀ e ∈ q.1.needs,
            ARD2.Admissible (· < ·) (T.eval p delta).1 (T.eval p delta).2
              q.1.graph.length (labels q.2) delta e := by
          intro e he
          exact (admissible_endpoint_iff hdk.le T p hp q.1 q.2 hqb e he).mp
            (hq.1.2.2.2.1 e he)
        have hin : Input relation (delta,T.eval p delta) a q.1 q.2 := by
          refine ⟨hq.1.1,hqb,hq.1.2.2.1,had,?_⟩
          apply (ends_endpoint_iff ih' hqb ?_).mp hq.1.2.2.2.2
          simpa only [hs] using had
        exact hq.2 (((pair_relation_iff (T.eval p delta) a delta).mp hr).2 q.1 q.2 hin)
  exact hall (T.eval p delta) T p hp rfl a ha

/-- Both controlling coordinates may exceed the reflected parent delta.
Only newly chosen ordinary template labels must be below delta. -/
theorem closed_reflects {kappa delta : Label.{u}} (hdk : delta < kappa) (hd : domain delta)
    (hbad : BadClosed kappa delta) (hext : ExtClosed relation kappa delta)
    (t : Label.{u} × Label.{u}) (hv : t.1 ≤ kappa ∧ t.2 ≤ kappa) :
    pairRelation t delta kappa := by
  apply (pair_relation_iff t delta kappa).mpr
  refine ⟨⟨hv.1,hv.2,hdk,hd⟩,?_⟩
  intro A f hf
  let pref : Fin A.cut → Label.{u} := fun i => labels f i
  have hpref : ∀ i, pref i < delta := by
    intro i
    change labels f i < delta
    rw [← hf.2.2.1]
    exact hf.1.ordered i A.cut i.isLt A.cut_lt
  have hex : ∃ g, Extends relation kappa A pref g :=
    ⟨f,hf.1,hf.2.1,(fun _ => rfl),hf.2.2.2.2⟩
  let g := leastExtension relation kappa A pref hex
  have hg : Extends relation kappa A pref g := leastExtension_spec relation kappa A pref hex
  have hgb : Bounded (· < ·) A.graph.length (labels g) delta := by
    intro i _hi
    rw [← extOp_eq relation kappa A i pref hex]
    exact hext A i pref hpref
  refine ⟨g,hg.1,?_,hgb,?_⟩
  · intro i hi
    exact hg.2.2.1 ⟨i,hi⟩
  · intro e he
    exact (endpoint_agreement hdk hbad
      (Template.ofEntry A.graph.length e (A.needs_valid e he)) g (bounded_tuple hgb)
      (labels g e.parent) (hgb e.parent (A.needs_valid e he).2.2)).mp (hg.2.2.2 e he)

theorem closed_heights_related {kappa alpha beta : Label.{u}} (hab : alpha < beta)
    (hbk : beta < kappa) (ha : domain alpha) (hbadA : BadClosed kappa alpha)
    (hextA : ExtClosed relation kappa alpha) (hbadB : BadClosed kappa beta)
    (T : Template) (f : Fin T.arity → Label.{u}) (hf : ∀ i, f i < beta) :
    pairRelation (T.eval f beta) alpha beta :=
  (endpoint_agreement hbk hbadB T f hf alpha hab).mp
    (closed_reflects (lt_trans hab hbk) ha hbadA hextA (T.eval f kappa)
      (T.eval_bounded f (fun i => lt_trans (hf i) hbk)))

end ARD2Demand

#print axioms ARD2Demand.admissible_endpoint_iff
#print axioms ARD2Demand.endpoint_agreement
#print axioms ARD2Demand.closed_reflects
#print axioms ARD2Demand.closed_heights_related
