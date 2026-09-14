import IPDStageFacts

/-! Actual whole-graph splice: every edge is old, a copied source, or a seam.
Normalization selects an already justified edge. The original source and
virtual-endpoint facts are retained for the next block. -/

namespace IPD.Semantics
set_option autoImplicit false
set_option maxHeartbeats 1500000
universe u

theorem block_relations {G : Graph} (hv : Valid G) {e : Edge}
    (he : e.parent < G.length-1) (b : Nat) (f r : Nat → Label.{u})
    (hs : SourceFacts G e (b+1) (spliceLabel (stageWidth G e b) (stageCut G e b) f r))
    (hn : Ends relation (stageWidth G e b) (seam G e b) r (f (stageCut G e b)))
    (i : Nat) (hi : i < G.length-1-e.parent) :
    ∀ t ∈ (block G e b)[i]?.getD [],
      relation (renameProfile (spliceLabel (stageWidth G e b) (stageCut G e b) f r) t.profile)
        (spliceLabel (stageWidth G e b) (stageCut G e b) f r t.parent)
        (spliceLabel (stageWidth G e b) (stageCut G e b) f r (stageWidth G e b+i)) := by
  intro t ht
  simp only [block,List.getElem?_map,List.getElem?_range,hi,Option.map_some,Option.getD_some] at ht
  have hm := normalize_mem _ t ht
  rcases List.mem_append.mp hm with hsource | hseam
  · obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hsource
    have hh := hs (e.parent+i) (by omega) old hold
    simpa only [shift_source he b i,moveEdge] using hh
  · split at hseam
    · rename_i hi0
      subst i
      have htvalid : t.Valid (stageWidth G e b) := by
        simpa only [shift_last he b] using seam_valid hv e b t hseam
      simpa only [Nat.add_zero] using splice_seam_relation f r t htvalid (hn t hseam)
    · simp at hseam

theorem splice_representation {G : Graph} (hv : Valid G) {e : Edge}
    (he : e.parent < G.length-1) (b : Nat) (f r : Nat → Label.{u})
    (hf : Rep relation (stage G e b) f) (hr : Rep relation (stage G e b) r)
    (hb : Bounded (stageWidth G e b) r (f (stageCut G e b)))
    (hs : SourceFacts G e (b+1) (spliceLabel (stageWidth G e b) (stageCut G e b) f r))
    (hn : Ends relation (stageWidth G e b) (seam G e b) r (f (stageCut G e b))) :
    Rep relation (stage G e (b+1)) (spliceLabel (stageWidth G e b) (stageCut G e b) f r) := by
  have hfo : ∀ i j, i < j → j < stageWidth G e b → f i < f j := by
    intro i j hij hj
    exact hf.ordered i j hij (by simpa only [stage_length] using hj)
  have hro : ∀ i j, i < j → j < stageWidth G e b → r i < r j := by
    intro i j hij hj
    exact hr.ordered i j hij (by simpa only [stage_length] using hj)
  refine ⟨?_,?_,?_⟩
  · intro i hi
    rw [stage_length,stageWidth_succ he] at hi
    by_cases hin : i < stageWidth G e b
    · rw [splice_old f r hin]
      exact hr.domain i (by simpa only [stage_length] using hin)
    · simp only [spliceLabel,OrdinalFormal.ReflectionTransport.spliceLabel,if_neg hin]
      apply hf.domain
      rw [stage_length]
      have hcut := stageCut_lt he b
      omega
  · intro i j hij hj
    rw [stage_length,stageWidth_succ he] at hj
    exact OrdinalFormal.ReflectionTransport.spliceLabel_ordered (· < ·) (fun h1 h2 => lt_trans h1 h2)
      f r (stageCut_lt he b) hfo hro hb i j hij hj
  · intro j t ht
    rw [stage_succ,List.getElem?_append] at ht
    split at ht
    · rename_i hj
      have hold : Rep relation (stage G e b)
          (spliceLabel (stageWidth G e b) (stageCut G e b) f r) :=
        representation_labels (stage_valid hv e he b)
          (fun i hi => splice_old f r (by simpa only [stage_length] using hi)) hr
      exact hold.relations j t ht
    · rename_i hj
      rw [stage_length] at ht hj
      have hi : j-stageWidth G e b < G.length-1-e.parent := by
        have hm := member_column_lt ht
        simpa only [block_length] using hm
      have hh := block_relations hv he b f r hs hn (j-stageWidth G e b) hi t ht
      have heq : stageWidth G e b+(j-stageWidth G e b) = j := by omega
      simpa only [heq] using hh

theorem stage_step {G : Graph} (hv : Valid G) {e : Edge}
    (he : controller (G.getLast?.getD []) = some e) (b : Nat)
    (f : Nat → Label.{u}) (beta : Label.{u}) (h : StageRep G e b f beta) :
    ∃ next : Nat → Label.{u}, StageRep G e (b+1) next beta := by
  have hcut := control_parent_lt hv he
  have ho : ∀ i j, i < j → j < stageWidth G e b → f i < f j := by
    intro i j hij hj
    exact h.rep.ordered i j hij (by simpa only [stage_length] using hj)
  have hseam := seam_usable hv he b f beta ho h.bounded h.top
  let A : Shape := {
    graph := stage G e b
    valid := stage_valid hv e hcut b
    cut := stageCut G e b
    cut_lt := by rw [stage_length]; exact stageCut_lt hcut b
    needs := seam G e b
    needs_valid := by
      intro t ht
      rw [stage_length]
      simpa only [shift_last hcut b] using seam_valid hv e b t ht }
  let c := moveEdge e.parent (G.length-1-e.parent) b e
  let T := endpointProfile (stageWidth G e b) f beta c
  have hc : relation T (f (stageCut G e b)) beta := h.top c (oldNeeds_controller he b)
  obtain ⟨r,hr,hfix,hrb,hrn⟩ := finite_reflection_nat T (f (stageCut G e b)) beta hc A f h.rep
    (by simpa only [A,stage_length] using h.bounded) rfl
    (by simpa only [A,stage_length,c,T,moveEdge,stageCut] using hseam.1)
    (by simpa only [A,stage_length] using hseam.2)
  have hrb' : Bounded (stageWidth G e b) r (f (stageCut G e b)) := by
    simpa only [A,stage_length] using hrb
  have hrn' : Ends relation (stageWidth G e b) (seam G e b) r (f (stageCut G e b)) := by
    simpa only [A,stage_length] using hrn
  have hs := sourceFacts_splice hv hcut b f r hfix h.source
  refine ⟨spliceLabel (stageWidth G e b) (stageCut G e b) f r,
    splice_representation hv hcut b f r h.rep hr hrb' hs hrn',?_,hs,
    oldNeeds_splice hv hcut b f r beta hfix h.top⟩
  intro i hi
  rw [stageWidth_succ hcut] at hi
  exact OrdinalFormal.ReflectionTransport.spliceLabel_bounded (· < ·) (fun h1 h2 => lt_trans h1 h2)
    f r beta (strict hc) h.bounded hrb' i hi

theorem stages_represented {G : Graph} (hv : Valid G) {e : Edge}
    (he : controller (G.getLast?.getD []) = some e)
    (f : Nat → Label.{u}) (hf : Rep relation G f) (n : Nat) :
    ∃ g : Nat → Label.{u}, StageRep G e n g (f (G.length-1)) := by
  induction n with
  | zero =>
    have hcut := control_parent_lt hv he
    exact ⟨f,stage_init hf (by omega) e⟩
  | succ n ih =>
    obtain ⟨g,hg⟩ := ih
    exact stage_step hv he n g (f (G.length-1)) hg

end IPD.Semantics

#print axioms IPD.Semantics.splice_representation
#print axioms IPD.Semantics.stage_step
#print axioms IPD.Semantics.stages_represented
