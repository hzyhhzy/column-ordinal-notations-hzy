import IPDTemplates

/-! Finite graph labelings and total Nat functions agree on exactly the
addresses used by valid edges. No global monotonicity outside that range. -/

namespace IPD.Semantics
set_option autoImplicit false
universe u

theorem member_column_lt {G : Graph} {j : Nat} {e : Edge}
    (he : e ∈ G[j]?.getD []) : j < G.length := by
  by_contra hn
  have hz : G[j]?.getD [] = [] := by rw [List.getElem?_eq_none (by omega)]; rfl
  simpa only [hz,List.not_mem_nil] using he

theorem representation_labels {R : Rel.{u}} {G : Graph} (hv : Valid G)
    {f g : Nat → Label.{u}} (hfg : ∀ i, i < G.length → g i = f i)
    (hf : Rep R G f) : Rep R G g := by
  refine ⟨?_,?_,?_⟩
  · intro i hi
    rw [hfg i hi]
    exact hf.domain i hi
  · intro i j hij hj
    rw [hfg i (lt_trans hij hj),hfg j hj]
    exact hf.ordered i j hij hj
  · intro j e he
    have hj := member_column_lt he
    have hev := hv j e he
    have hparent : e.parent < j := hev.1
    have heq : renameProfile g e.profile = renameProfile f e.profile :=
      renameProfile_congr_on _ _ _ (fun i hi => by
        apply hfg
        rcases hi with hi | rfl <;> omega) _ hev.2
    rw [heq,hfg e.parent (lt_trans hev.1 hj),hfg j hj]
    exact hf.relations j e he

theorem endpointProfile_labels {m : Nat} {e : Edge} (hv : e.Valid m)
    {f g : Nat → Label.{u}} (hfg : ∀ i, i < m → g i = f i) (b : Label.{u}) :
    endpointProfile m g b e = endpointProfile m f b e := by
  apply renameProfile_congr_on _ _ _ ?_ _ hv.2
  intro i hi
  by_cases him : i = m
  · simp [endpointMap,him]
  · have hip : i ≤ e.parent := hi.resolve_right him
    have him' : i < m := lt_of_le_of_lt hip hv.1
    simp [endpointMap,him,hfg i him']

theorem ends_labels {R : Rel.{u}} {m : Nat} {needs : Column}
    (hv : ∀ e ∈ needs, e.Valid m) {f g : Nat → Label.{u}}
    (hfg : ∀ i, i < m → g i = f i) {b : Label.{u}} (hf : Ends R m needs f b) :
    Ends R m needs g b := by
  intro e he
  rw [endpointProfile_labels (hv e he) hfg b,hfg e.parent (hv e he).1]
  exact hf e he

theorem Template.ofEdge_eval (m : Nat) (e : Edge) (he : e.Valid m)
    (f : Nat → Label.{u}) (b : Label.{u}) :
    (Template.ofEdge m e he).eval (fun i => f i) b = endpointProfile m f b e :=
  endpointProfile_labels he (fun i hi => labels_apply (fun j : Fin m => f j) hi) b

@[simp] theorem endpointMap_self (m : Nat) (f : Nat → Label.{u}) : endpointMap m f (f m) = f := by
  funext i
  by_cases h : i = m <;> simp [endpointMap,h]

@[simp] theorem endpointProfile_self (m : Nat) (f : Nat → Label.{u}) (e : Edge) :
    endpointProfile m f (f m) e = renameProfile f e.profile := by
  simp only [endpointProfile,endpointMap_self]

/-- Finite reflection in the total-labeling interface used by graph splicing. -/
theorem finite_reflection_nat (t : Profile Label.{u}) (a b : Label.{u})
    (hr : relation t a b) (A : Shape) (f : Nat → Label.{u})
    (hf : Rep relation A.graph f) (hb : Bounded A.graph.length f b) (hc : f A.cut = a)
    (ha : ∀ e ∈ A.needs, Admissible (b,t,a) A.graph.length f e)
    (he : Ends relation A.graph.length A.needs f b) :
    ∃ g : Nat → Label.{u}, Rep relation A.graph g ∧
      (∀ i, i < A.cut → g i = f i) ∧ Bounded A.graph.length g a ∧
      Ends relation A.graph.length A.needs g a := by
  let F : Fin A.graph.length → Label.{u} := fun i => f i
  have hF : ∀ i, i < A.graph.length → labels F i = f i := fun i hi => labels_apply F hi
  have hin : Input relation (b,t,a) A F := by
    refine ⟨representation_labels A.valid hF hf,?_,(hF A.cut A.cut_lt).trans hc,?_,
      ends_labels A.needs_valid hF he⟩
    · intro i hi
      rw [hF i hi]
      exact hb i hi
    · intro e hem
      change Prod.Lex (· < ·) (· < ·)
        (endpointProfile A.graph.length (labels F) b e,labels F e.parent) (t,a)
      rw [endpointProfile_labels (A.needs_valid e hem) hF b,hF e.parent (A.needs_valid e hem).1]
      exact ha e hem
  obtain ⟨g,hg,hfixed,hbelow,hnew⟩ := finite_reflection t a b hr A F hin
  refine ⟨labels g,hg,?_,hbelow,hnew⟩
  intro i hi
  exact (hfixed i hi).trans (hF i (lt_trans hi A.cut_lt))

end IPD.Semantics

#print axioms IPD.Semantics.representation_labels
#print axioms IPD.Semantics.Template.ofEdge_eval
#print axioms IPD.Semantics.finite_reflection_nat
