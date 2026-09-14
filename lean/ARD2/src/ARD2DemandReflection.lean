import ARD2DemandRecursion
namespace ARD2Demand
open OrdinalFormal
open OrdinalFormal.ReflectionTransport
universe u
theorem strict {k theta a b : Label.{u}} (h : relation k theta a b) : a < b :=
  ((relation_iff k theta a b).mp h).1.2.2.1
theorem row_le {k theta a b : Label.{u}} (h : relation k theta a b) : k ≤ b :=
  ((relation_iff k theta a b).mp h).1.1
theorem parent_domain {k theta a b : Label.{u}} (h : relation k theta a b) : domain a :=
  ((relation_iff k theta a b).mp h).1.2.2.2
theorem root_le {k theta a b : Label.{u}} (h : relation k theta a b) : theta ≤ b :=
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
  rcases hf.2.2.2.1 d hd with hl | ⟨heq,hr⟩
  · exact Or.inl hl
  · exact Or.inr ⟨heq,lt_of_lt_of_le hr hle⟩
theorem lower_rows {low high theta eta a b : Label.{u}} (hl : low < high) (he : eta ≤ b)
    (h : relation high theta a b) : relation low eta a b := by
  have hfull := (relation_iff high theta a b).mp h
  apply (relation_iff low eta a b).mpr
  refine ⟨⟨le_trans hl.le hfull.1.1,he,hfull.1.2.2⟩,?_⟩
  intro A f hf
  apply hfull.2 A f
  refine ⟨hf.1,hf.2.1,hf.2.2.1,?_,hf.2.2.2.2⟩
  intro d hd
  apply Or.inl
  rcases hf.2.2.2.1 d hd with hlow | ⟨heq,_⟩
  · exact lt_trans hlow hl
  · exact heq ▸ hl

theorem representation_labels {R : Rel.{u}} {G : ARD2.Graph} (hv : ARD2.Valid G)
    {f g : Nat → Label.{u}} (hfg : ∀ i, i < G.length → g i = f i)
    (hf : ARD2.Holds (· < ·) domain R G f) : ARD2.Holds (· < ·) domain R G g := by
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
theorem atEnd_labels {n : Nat} {f g : Nat → Label.{u}} (b : Label.{u})
    (hfg : ∀ i, i < n → g i = f i) (i : Nat) :
    ARD2.atEnd n g b i = ARD2.atEnd n f b i := by
  unfold ARD2.atEnd
  split
  · rename_i hi; exact hfg i hi
  · rfl
theorem ends_labels {R : Rel.{u}} {n : Nat} {needs : List ARD2.Entry}
    {f g : Nat → Label.{u}} {b : Label.{u}} (hfg : ∀ i, i < n → g i = f i)
    (hv : ∀ d ∈ needs, ARD2.NeedValid n d) (hf : ARD2.Ends R n needs f b) :
    ARD2.Ends R n needs g b := by
  intro d hd
  rw [atEnd_labels b hfg d.row, atEnd_labels b hfg d.root,
    hfg d.parent (hv d hd).2.2]
  exact hf d hd
theorem finite_reflection : ARD2.FiniteReflection (· < ·) domain relation.{u} := by
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
      unfold ARD2.Admissible
      rw [atEnd_labels beta hF d.row, atEnd_labels beta hF d.root]
      exact hadmiss d hd
  obtain ⟨g,hg,hfixed,hbelow,hnew⟩ := ((relation_iff K theta (f cut) beta).mp hcontrol).2 A F hin
  refine ⟨labels g,hg,?_,hbelow,hnew⟩
  intro i hi
  exact (hfixed i hi).trans (hF i (lt_trans hi hcut))
end ARD2Demand
#print axioms ARD2Demand.strict
#print axioms ARD2Demand.root_weaken
#print axioms ARD2Demand.lower_rows
#print axioms ARD2Demand.finite_reflection


