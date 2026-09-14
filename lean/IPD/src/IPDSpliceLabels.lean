import IPDGraphGeometry
import IPDFiniteLabels

/-! Every nested atomic reference is transported in a splice. The virtual
SELF stays at beta for the next stage; the actual seam SELF becomes f(cut). -/

namespace IPD.Semantics
set_option autoImplicit false
set_option maxHeartbeats 1000000
universe u

abbrev spliceLabel := @OrdinalFormal.ReflectionTransport.spliceLabel

theorem splice_old {n c i : Nat} (f r : Nat → Label.{u}) (hi : i < n) :
    spliceLabel n c f r i = r i :=
  OrdinalFormal.ReflectionTransport.spliceLabel_old f r hi

theorem splice_first (n c : Nat) (f r : Nat → Label.{u}) : spliceLabel n c f r n = f c :=
  OrdinalFormal.ReflectionTransport.spliceLabel_first n c f r

theorem shifted_label_reuse {G : Graph} {e : Edge} (he : e.parent < G.length-1)
    (b : Nat) (f r : Nat → Label.{u})
    (hfix : ∀ i, i < stageCut G e b → r i = f i) (i : Nat) (hi : i < G.length-1) :
    spliceLabel (stageWidth G e b) (stageCut G e b) f r
      (shift e.parent (G.length-1-e.parent) (b+1) i) =
      f (shift e.parent (G.length-1-e.parent) b i) := by
  rw [shift_block_transition he]
  exact OrdinalFormal.ReflectionTransport.spliceLabel_move f r (stageCut_lt he b).le
    (shifted_lt_last he b i hi) hfix

theorem shifted_profile_reuse {G : Graph} {e : Edge} (he : e.parent < G.length-1)
    (b : Nat) (f r : Nat → Label.{u})
    (hfix : ∀ i, i < stageCut G e b → r i = f i)
    (j : Nat) (hj : j < G.length-1) (t : Edge) (ht : t.Valid j) :
    renameProfile (spliceLabel (stageWidth G e b) (stageCut G e b) f r)
      (moveEdge e.parent (G.length-1-e.parent) (b+1) t).profile =
      renameProfile f (moveEdge e.parent (G.length-1-e.parent) b t).profile := by
  change renameProfile _ (renameProfile _ t.profile) = renameProfile _ (renameProfile _ t.profile)
  rw [renameProfile_comp,renameProfile_comp]
  apply renameProfile_congr_on _ _ _ ?_ _ ht.2
  intro i hi
  apply shifted_label_reuse he b f r hfix i
  have hparent := ht.1
  rcases hi with hi | rfl <;> omega

theorem shifted_endpoint_profile_reuse {G : Graph} {e : Edge} (he : e.parent < G.length-1)
    (b : Nat) (f r : Nat → Label.{u}) (beta : Label.{u})
    (hfix : ∀ i, i < stageCut G e b → r i = f i) (t : Edge) (ht : t.Valid (G.length-1)) :
    endpointProfile (stageWidth G e (b+1))
      (spliceLabel (stageWidth G e b) (stageCut G e b) f r) beta
      (moveEdge e.parent (G.length-1-e.parent) (b+1) t) =
    endpointProfile (stageWidth G e b) f beta (moveEdge e.parent (G.length-1-e.parent) b t) := by
  change renameProfile _ (renameProfile _ t.profile) = renameProfile _ (renameProfile _ t.profile)
  rw [renameProfile_comp,renameProfile_comp]
  apply renameProfile_congr_on _ _ _ ?_ _ ht.2
  intro i hi
  dsimp only [Function.comp_def]
  rcases hi with hi | rfl
  · have hil : i < G.length-1 := lt_of_le_of_lt hi ht.1
    simp only [endpointMap,if_neg (ne_of_lt (shifted_lt_last he (b+1) i hil)),
      if_neg (ne_of_lt (shifted_lt_last he b i hil))]
    exact shifted_label_reuse he b f r hfix i hil
  · simp [shift_last he,endpointMap]

theorem splice_seam_profile {n c : Nat} (f r : Nat → Label.{u})
    (t : Edge) (ht : t.Valid n) :
    renameProfile (spliceLabel n c f r) t.profile = endpointProfile n r (f c) t := by
  apply renameProfile_congr_on _ _ _ ?_ _ ht.2
  intro i hi
  rcases hi with hi | rfl
  · have hin : i < n := lt_of_le_of_lt hi ht.1
    rw [splice_old f r hin]
    simp only [endpointMap,if_neg (ne_of_lt hin)]
  · rw [splice_first]
    simp [endpointMap]

theorem splice_seam_relation {n c : Nat} (f r : Nat → Label.{u})
    (t : Edge) (ht : t.Valid n)
    (hr : relation (endpointProfile n r (f c) t) (r t.parent) (f c)) :
    relation (renameProfile (spliceLabel n c f r) t.profile)
      (spliceLabel n c f r t.parent) (spliceLabel n c f r n) := by
  rw [splice_seam_profile f r t ht,
    splice_old f r ht.1,splice_first]
  exact hr

end IPD.Semantics

#print axioms IPD.Semantics.shifted_profile_reuse
#print axioms IPD.Semantics.shifted_endpoint_profile_reuse
#print axioms IPD.Semantics.splice_seam_relation
