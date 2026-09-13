import ARDDemandRecursion
namespace ARDDemand
open OrdinalFormal
open OrdinalFormal.ReflectionTransport
universe u
theorem strict {k theta a b : Label.{u}} (h : relation k theta a b) : a < b :=
  ((relation_iff k theta a b).mp h).1.2.2.1
theorem row_lt {k theta a b : Label.{u}} (h : relation k theta a b) : k < b :=
  ((relation_iff k theta a b).mp h).1.1
theorem parent_domain {k theta a b : Label.{u}} (h : relation k theta a b) : domain a :=
  ((relation_iff k theta a b).mp h).1.2.2.2
theorem root_le {k theta a b : Label.{u}} (h : relation k theta a b) : theta ≤ a :=
  ((relation_iff k theta a b).mp h).1.2.1
theorem root_weaken {k small large a b : Label.{u}} (hle : small ≤ large)
    (h : relation k large a b) : relation k small a b := by
  have hfull := (relation_iff k large a b).mp h
  apply (relation_iff k small a b).mpr
  refine ⟨⟨hfull.1.1,le_trans hle hfull.1.2.1,hfull.1.2.2⟩,?_⟩
  intro A f hf
  apply hfull.2 A f
  refine ⟨hf.1,hf.2.1,hf.2.2.1,?_,hf.2.2.2.2⟩
  intro d hd
  rcases hf.2.2.2.1 d hd with hl | ⟨heq,hcut,hr⟩
  · exact Or.inl hl
  · exact Or.inr ⟨heq,hcut,lt_of_lt_of_le hr hle⟩
theorem lower_rows {low high theta eta a b : Label.{u}} (hl : low < high) (he : eta ≤ a)
    (h : relation high theta a b) : relation low eta a b := by
  have hfull := (relation_iff high theta a b).mp h
  apply (relation_iff low eta a b).mpr
  refine ⟨⟨lt_trans hl hfull.1.1,he,hfull.1.2.2⟩,?_⟩
  intro A f hf
  apply hfull.2 A f
  refine ⟨hf.1,hf.2.1,hf.2.2.1,?_,hf.2.2.2.2⟩
  intro d hd
  apply Or.inl
  rcases hf.2.2.2.1 d hd with hlow | ⟨heq,_,_⟩
  · exact lt_trans hlow hl
  · exact heq ▸ hl

theorem representation_labels {R : Rel.{u}} {G : ARD.Graph} (hv : ARD.Valid G)
    {f g : Nat → Label.{u}} (hfg : ∀ i, i < G.length → g i = f i)
    (hf : ARD.Holds (· < ·) domain R G f) : ARD.Holds (· < ·) domain R G g := by
  refine ⟨?_,?_,?_⟩
  · intro i hi
    rw [hfg i hi]
    exact hf.domain i hi
  · intro i j hij hj
    rw [hfg i (lt_trans hij hj),hfg j hj]
    exact hf.ordered i j hij hj
  · intro j e he
    have hj : j < G.length := by
      by_contra hn
      have hz : G[j]?.getD [] = [] := by simp [List.getElem?_eq_none (by omega : G.length ≤ j)]
      simpa [hz] using he
    rcases hv j e he with ⟨hk,hr,hp⟩
    rw [hfg e.row (by omega),hfg e.root (by omega),hfg e.parent (by omega),hfg j hj]
    exact hf.relations j e he
theorem ends_labels {R : Rel.{u}} {n : Nat} {needs : List ARD.Entry}
    {f g : Nat → Label.{u}} {b : Label.{u}} (hfg : ∀ i, i < n → g i = f i)
    (hv : ∀ d ∈ needs, ARD.NeedValid n d) (hf : ARD.Ends R needs f b) :
    ARD.Ends R needs g b := by
  intro d hd
  rcases hv d hd with ⟨hk,hr,hp⟩
  rw [hfg d.row hk,hfg d.root (by omega),hfg d.parent hp]
  exact hf d hd
theorem finite_reflection : ARD.FiniteReflection (· < ·) domain relation.{u} := by
  intro G cut K theta beta f needs hv hcut hf hbound hcontrol hvalid hadmiss hends
  let A : Shape := ⟨G,hv,cut,hcut,needs,hvalid⟩
  let F : Fin G.length → Label.{u} := fun i => f i.val
  have hF : ∀ i, i < G.length → labels F i = f i := fun i hi => labels_apply F hi
  have hin : Input relation (beta,K,theta) (f cut) A F := by
    refine ⟨representation_labels hv hF hf,?_,hF cut hcut,?_,ends_labels hF hvalid hends⟩
    · intro i hi
      rw [hF i hi]
      exact hbound i hi
    · intro d hd
      have hk := (hvalid d hd).1
      have hr : d.root < G.length := lt_of_le_of_lt (hvalid d hd).2.1 (hvalid d hd).2.2
      unfold ARD.Admissible
      rw [hF d.row hk,hF d.root hr]
      exact hadmiss d hd
  obtain ⟨g,hg,hfixed,hbelow,hnew⟩ := ((relation_iff K theta (f cut) beta).mp hcontrol).2 A F hin
  refine ⟨labels g,hg,?_,hbelow,hnew⟩
  intro i hi
  exact (hfixed i hi).trans (hF i (lt_trans hi hcut))
end ARDDemand
#print axioms ARDDemand.strict
#print axioms ARDDemand.root_weaken
#print axioms ARDDemand.lower_rows
#print axioms ARDDemand.finite_reflection
