import ARDWitnesses
/-! Endpoint agreement and strong supply for dynamically evaluated row anchors. -/
namespace ARDDemand
open OrdinalFormal
open OrdinalFormal.ReflectionTransport
universe u
def RootEarlier : (Label.{u} × Label.{u}) → (Label.{u} × Label.{u}) → Prop :=
  Prod.Lex (· < ·) (· < ·)
theorem rootEarlier_wellFounded : WellFounded RootEarlier.{u} :=
  Ordinal.lt_wf.prod_lex Ordinal.lt_wf
def BadClosed (kappa delta : Label.{u}) : Prop :=
  ∀ k i theta a, k < delta → theta < delta → a < delta → badOp k i theta a kappa < delta
def ExtClosed (R : Rel.{u}) (kappa delta : Label.{u}) : Prop :=
  ∀ (A : Shape) i (pref : Fin A.cut → Label.{u}),
    (∀ j, pref j < delta) → extOp R kappa A i pref < delta
theorem admissible_rootEarlier {s : Label.{u} × Label.{u}}
    {cut : Nat} {f : Nat → Label.{u}} {d : ARD.Entry}
    (h : ARD.Admissible (· < ·) s.1 cut s.2 f d) :
    RootEarlier (f d.row,f d.root) s := by
  rcases h with hl | ⟨heq,_,hr⟩
  · exact Prod.Lex.left _ _ hl
  · have hs : s = (s.1,s.2) := rfl
    rw [hs,heq]
    exact Prod.Lex.right _ hr
theorem ends_endpoint_iff {kappa delta : Label.{u}} {s : Label.{u} × Label.{u}}
    (ih : ∀ t, RootEarlier t s → t.1 < delta → ∀ a, a < delta →
      (relation t.1 t.2 a kappa ↔ relation t.1 t.2 a delta))
    {A : Shape} {f : Nat → Label.{u}} (hb : Bounded (· < ·) A.graph.length f delta)
    (ha : ∀ d ∈ A.needs, ARD.Admissible (· < ·) s.1 A.cut s.2 f d) :
    ARD.Ends relation A.needs f kappa ↔ ARD.Ends relation A.needs f delta := by
  have he : ∀ d ∈ A.needs,
      relation (f d.row) (f d.root) (f d.parent) kappa ↔
        relation (f d.row) (f d.root) (f d.parent) delta := by
    intro d hd
    exact ih (f d.row,f d.root) (admissible_rootEarlier (ha d hd))
      (hb d.row (A.needs_valid d hd).1) (f d.parent) (hb d.parent (A.needs_valid d hd).2.2)
  exact ⟨fun h d hd => (he d hd).mp (h d hd),fun h d hd => (he d hd).mpr (h d hd)⟩

theorem endpoint_agreement {kappa delta : Label.{u}} (hdk : delta < kappa)
    (hclosed : BadClosed kappa delta) (k theta a : Label.{u}) (hk : k < delta) (ha : a < delta) :
    relation k theta a kappa ↔ relation k theta a delta := by
  have hall : ∀ s : Label.{u} × Label.{u}, s.1 < delta → ∀ a, a < delta →
      (relation s.1 s.2 a kappa ↔ relation s.1 s.2 a delta) := by
    intro s
    induction s using rootEarlier_wellFounded.induction with
    | h s ih =>
      intro hs a ha
      constructor
      · intro hr
        have hrule := (relation_iff s.1 s.2 a kappa).mp hr
        apply (relation_iff s.1 s.2 a delta).mpr
        refine ⟨⟨hs,hrule.1.2.1,ha,hrule.1.2.2.2⟩,?_⟩
        intro A f hf
        apply hrule.2 A f
        refine ⟨hf.1,(fun i hi => lt_trans (hf.2.1 i hi) hdk),hf.2.2.1,hf.2.2.2.1,?_⟩
        exact (ends_endpoint_iff ih hf.2.1 hf.2.2.2.1).mpr hf.2.2.2.2
      · intro hr
        classical
        by_contra hn
        have hg : Guard (kappa,s.1,s.2) a :=
          ⟨lt_trans hs hdk,root_le hr,lt_trans ha hdk,parent_domain hr⟩
        have hex := exists_bad hg hn
        let p := leastBad s.1 s.2 a kappa hex
        have hp : Bad s.1 s.2 a kappa p := leastBad_spec s.1 s.2 a kappa hex
        have hbp : Bounded (· < ·) p.1.graph.length (labels p.2) delta := by
          intro i _hi
          rw [← badOp_eq s.1 i s.2 a kappa hex]
          exact hclosed s.1 i s.2 a hs (lt_of_le_of_lt (root_le hr) ha) ha
        have hin : Input relation (delta,s.1,s.2) a p.1 p.2 :=
          ⟨hp.1.1,hbp,hp.1.2.2.1,hp.1.2.2.2.1,
            (ends_endpoint_iff ih hbp hp.1.2.2.2.1).mp hp.1.2.2.2.2⟩
        exact hp.2 (((relation_iff s.1 s.2 a delta).mp hr).2 p.1 p.2 hin)
  exact hall (k,theta) hk a ha

/-- The control row may be at or above delta. Only the newly reflected row
values must be below delta when endpoint agreement is invoked. -/
theorem closed_reflects {kappa delta : Label.{u}} (hdk : delta < kappa) (hd : domain delta)
    (hbad : BadClosed kappa delta) (hext : ExtClosed relation kappa delta)
    (k theta : Label.{u}) (hk : k < kappa) (htheta : theta ≤ delta) :
    relation k theta delta kappa := by
  apply (relation_iff k theta delta kappa).mpr
  refine ⟨⟨hk,htheta,hdk,hd⟩,?_⟩
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
  · intro d hd
    exact (endpoint_agreement hdk hbad (labels g d.row) (labels g d.root) (labels g d.parent)
      (hgb d.row (A.needs_valid d hd).1) (hgb d.parent (A.needs_valid d hd).2.2)).mp
        (hg.2.2.2 d hd)
theorem closed_heights_related {kappa alpha beta : Label.{u}} (hab : alpha < beta)
    (hbk : beta < kappa) (ha : domain alpha) (hbadA : BadClosed kappa alpha)
    (hextA : ExtClosed relation kappa alpha) (hbadB : BadClosed kappa beta)
    (k theta : Label.{u}) (hk : k < beta) (ht : theta ≤ alpha) : relation k theta alpha beta :=
  (endpoint_agreement hbk hbadB k theta alpha hk hab).mp
    (closed_reflects (lt_trans hab hbk) ha hbadA hextA k theta (lt_trans hk hbk) ht)
end ARDDemand
#print axioms ARDDemand.endpoint_agreement
#print axioms ARDDemand.closed_reflects
#print axioms ARDDemand.closed_heights_related
