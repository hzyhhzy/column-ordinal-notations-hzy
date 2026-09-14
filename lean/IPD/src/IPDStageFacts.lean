import IPDSemanticEdges
import IPDSpliceLabels

/-! The induction invariant keeps facts for every original source column,
not just the currently appended tail, plus the original last-column templates
with a virtual SELF at beta. -/

namespace IPD.Semantics
set_option autoImplicit false
set_option maxHeartbeats 1200000
universe u

def SourceFacts (G : Graph) (e : Edge) (b : Nat) (f : Nat → Label.{u}) : Prop :=
  ∀ j, j < G.length-1 → ∀ t ∈ G[j]?.getD [],
    relation (renameProfile f (moveEdge e.parent (G.length-1-e.parent) b t).profile)
      (f (shift e.parent (G.length-1-e.parent) b t.parent))
      (f (shift e.parent (G.length-1-e.parent) b j))

structure StageRep (G : Graph) (e : Edge) (b : Nat) (f : Nat → Label.{u}) (beta : Label.{u}) : Prop where
  rep : Rep relation (stage G e b) f
  bounded : Bounded (stageWidth G e b) f beta
  source : SourceFacts G e b f
  top : Ends relation (stageWidth G e b) (oldNeeds G e b) f beta

theorem representation_take {R : Rel.{u}} {G : Graph} {f : Nat → Label.{u}}
    (hf : Rep R G f) (n : Nat) : Rep R (G.take n) f := by
  refine ⟨?_,?_,?_⟩
  · intro i hi
    exact hf.domain i (by simp only [List.length_take] at hi; omega)
  · intro i j hij hj
    exact hf.ordered i j hij (by simp only [List.length_take] at hj; omega)
  · intro j t ht
    rw [List.getElem?_take] at ht
    split at ht
    · exact hf.relations j t ht
    · simp at ht

theorem stage_init {G : Graph} {f : Nat → Label.{u}} (hf : Rep relation G f)
    (hl : 0 < G.length) (e : Edge) : StageRep G e 0 f (f (G.length-1)) := by
  have hlast : G.length-1 < G.length := by omega
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [stage_zero] using representation_take hf (G.length-1)
  · intro i hi
    have hi' : i < G.length-1 := by simpa [stageWidth] using hi
    exact hf.ordered i (G.length-1) hi' hlast
  · intro j hj t ht
    simpa only [moveEdge,renameProfile_comp,Function.comp_def,shift_zero] using hf.relations j t ht
  · intro t ht
    obtain ⟨old,hold,rfl⟩ := List.mem_map.mp ht
    rw [List.getLast?_eq_getElem?] at hold
    simpa only [stageWidth,Nat.zero_mul,Nat.add_zero,endpointProfile,moveEdge,
      renameProfile_comp,Function.comp_def,shift_zero,endpointMap_self] using
      hf.relations (G.length-1) old hold

theorem sourceFacts_splice {G : Graph} (hv : Valid G) {e : Edge}
    (he : e.parent < G.length-1) (b : Nat) (f r : Nat → Label.{u})
    (hfix : ∀ i, i < stageCut G e b → r i = f i) (hs : SourceFacts G e b f) :
    SourceFacts G e (b+1) (spliceLabel (stageWidth G e b) (stageCut G e b) f r) := by
  intro j hj t ht
  rw [shifted_profile_reuse he b f r hfix j hj t (hv j t ht),
    shifted_label_reuse he b f r hfix t.parent (lt_trans (hv j t ht).1 hj),
    shifted_label_reuse he b f r hfix j hj]
  exact hs j hj t ht

theorem oldNeeds_splice {G : Graph} (hv : Valid G) {e : Edge}
    (he : e.parent < G.length-1) (b : Nat) (f r : Nat → Label.{u}) (beta : Label.{u})
    (hfix : ∀ i, i < stageCut G e b → r i = f i)
    (htop : Ends relation (stageWidth G e b) (oldNeeds G e b) f beta) :
    Ends relation (stageWidth G e (b+1)) (oldNeeds G e (b+1))
      (spliceLabel (stageWidth G e b) (stageCut G e b) f r) beta := by
  intro t ht
  obtain ⟨old,hold,rfl⟩ := List.mem_map.mp ht
  have hold' := hold
  rw [List.getLast?_eq_getElem?] at hold'
  have hov := hv (G.length-1) old hold'
  change relation (endpointProfile _ _ _ _)
    (spliceLabel (stageWidth G e b) (stageCut G e b) f r
      (shift e.parent (G.length-1-e.parent) (b+1) old.parent)) _
  rw [shifted_endpoint_profile_reuse he b f r beta hfix old hov,
    shifted_label_reuse he b f r hfix old.parent hov.1]
  exact htop _ (List.mem_map_of_mem hold)

end IPD.Semantics

#print axioms IPD.Semantics.stage_init
#print axioms IPD.Semantics.sourceFacts_splice
#print axioms IPD.Semantics.oldNeeds_splice
