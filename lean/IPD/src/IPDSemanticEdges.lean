import IPDGraphController
import IPDFiniteLabels

/-! Interpreting local comparisons and seam weakenings in an actual finite
ordinal labeling, with SELF interpreted at its virtual endpoint. -/

namespace IPD.Semantics
set_option autoImplicit false
set_option maxHeartbeats 1200000
universe u

theorem endpointMap_strict {m : Nat} {f : Nat → Label.{u}} {b : Label.{u}}
    (hf : ∀ i j, i < j → j < m → f i < f j) (hb : Bounded m f b) :
    ∀ i j, i ≤ m → j ≤ m → i < j → endpointMap m f b i < endpointMap m f b j := by
  intro i j hi hj hij
  have him : i < m := by omega
  by_cases hjm : j = m
  · simpa [endpointMap,hjm,ne_of_lt him] using hb i him
  · have hjm' : j < m := by omega
    simpa [endpointMap,hjm,ne_of_lt him] using hf i j hij hjm'

theorem edge_support_bounded {m : Nat} {e : Edge} (he : e.Valid m) :
    ProfileAtoms (fun i => i ≤ m) e.profile := by
  apply profileAtoms_mono _ e.profile he.2
  intro i hi
  rcases hi with hi | rfl
  · exact le_trans hi (le_of_lt he.1)
  · exact le_rfl

theorem endpointProfile_lt {m : Nat} {f : Nat → Label.{u}} {b : Label.{u}}
    (hf : ∀ i j, i < j → j < m → f i < f j) (hb : Bounded m f b)
    {a e : Edge} (ha : a.Valid m) (he : e.Valid m) (h : a.profile < e.profile) :
    endpointProfile m f b a < endpointProfile m f b e :=
  renameProfile_lt_on (fun i => i ≤ m) (endpointMap m f b) (endpointMap_strict hf hb)
    _ _ (edge_support_bounded ha) (edge_support_bounded he) h

theorem endpointProfile_valid {m : Nat} {f : Nat → Label.{u}} {b : Label.{u}}
    (hf : ∀ i j, i < j → j < m → f i < f j) {e : Edge} (he : e.Valid m) :
    ProfileAtoms (fun x => x ≤ f e.parent ∨ x = b) (endpointProfile m f b e) := by
  apply profileAtoms_rename _ _ _ ?_ _ he.2
  intro i hi
  rcases hi with hi | rfl
  · have him : i < m := lt_of_le_of_lt hi he.1
    apply Or.inl
    simp only [endpointMap,if_neg (ne_of_lt him)]
    rcases hi.eq_or_lt with heq | hlt
    · exact le_of_eq (congrArg f heq)
    · exact le_of_lt (hf i e.parent hlt he.1)
  · exact Or.inr (by simp [endpointMap])

theorem endpoint_weaken {m : Nat} {f : Nat → Label.{u}} {b : Label.{u}}
    (hf : ∀ i j, i < j → j < m → f i < f j) (hb : Bounded m f b)
    {a e : Edge} (ha : a.Valid m) (he : e.Valid m)
    (hp : a.parent = e.parent) (h : a.profile ≤ e.profile)
    (hr : relation (endpointProfile m f b e) (f e.parent) b) :
    relation (endpointProfile m f b a) (f a.parent) b := by
  have hle : endpointProfile m f b a ≤ endpointProfile m f b e := by
    rcases h.eq_or_lt with heq | hlt
    · exact le_of_eq (congrArg (renameProfile (endpointMap m f b)) heq)
    · exact le_of_lt (endpointProfile_lt hf hb ha he hlt)
  have hv := endpointProfile_valid (b := b) hf ha
  rw [hp] at hv ⊢
  exact profile_weaken hle hv hr

theorem control_admissible {m : Nat} {f : Nat → Label.{u}} {b : Label.{u}}
    (hf : ∀ i j, i < j → j < m → f i < f j) (hb : Bounded m f b)
    {a e : Edge} (ha : a.Valid m) (he : e.Valid m) (h : ControlLt a e) :
    Admissible (b,endpointProfile m f b e,f e.parent) m f a := by
  rcases h with h | ⟨hprof,hparent⟩
  · exact Prod.Lex.left _ _ (endpointProfile_lt hf hb ha he h)
  · have hp : endpointProfile m f b a = endpointProfile m f b e :=
      congrArg (renameProfile (endpointMap m f b)) hprof
    change Prod.Lex (· < ·) (· < ·)
      (endpointProfile m f b a,f a.parent) (endpointProfile m f b e,f e.parent)
    rw [hp]
    exact Prod.Lex.right _ (hf _ _ hparent he.1)

def oldNeeds (G : Graph) (e : Edge) (b : Nat) : Column :=
  (G.getLast?.getD []).map (moveEdge e.parent (G.length-1-e.parent) b)

theorem oldNeeds_valid {G : Graph} (hv : Valid G) {e : Edge}
    (he : e.parent < G.length-1) (b : Nat) :
    ∀ t ∈ oldNeeds G e b, t.Valid (stageWidth G e b) := by
  intro t ht
  obtain ⟨old,hold,rfl⟩ := List.mem_map.mp ht
  rw [List.getLast?_eq_getElem?] at hold
  simpa only [shift_last he b] using moveEdge_valid e.parent (G.length-1-e.parent) b
    (G.length-1) old (hv _ old hold)

theorem oldNeeds_controller {G : Graph} {e : Edge}
    (he : controller (G.getLast?.getD []) = some e) (b : Nat) :
    moveEdge e.parent (G.length-1-e.parent) b e ∈ oldNeeds G e b :=
  List.mem_map_of_mem (controller_mem he)

theorem seam_usable {G : Graph} (hv : Valid G) {e : Edge}
    (he : controller (G.getLast?.getD []) = some e) (b : Nat)
    (f : Nat → Label.{u}) (beta : Label.{u})
    (hf : ∀ i j, i < j → j < stageWidth G e b → f i < f j)
    (hb : Bounded (stageWidth G e b) f beta)
    (htop : Ends relation (stageWidth G e b) (oldNeeds G e b) f beta) :
    let c := moveEdge e.parent (G.length-1-e.parent) b e
    (∀ t ∈ seam G e b,
      Admissible (beta,endpointProfile (stageWidth G e b) f beta c,f c.parent)
        (stageWidth G e b) f t) ∧
      Ends relation (stageWidth G e b) (seam G e b) f beta := by
  dsimp only
  have hcut := control_parent_lt hv he
  have hctrl := oldNeeds_valid hv hcut b _ (oldNeeds_controller he b)
  have hseam : ∀ t ∈ seam G e b, t.Valid (stageWidth G e b) := by
    intro t ht
    simpa only [shift_last hcut b] using seam_valid hv e b t ht
  constructor
  · intro t ht
    obtain ⟨old,hold,hp,hprof,hl⟩ := seam_spec hv he b t ht
    exact control_admissible hf hb (hseam t ht) hctrl hl
  · intro t ht
    obtain ⟨old,hold,hp,hprof,_⟩ := seam_spec hv he b t ht
    have hm : moveEdge e.parent (G.length-1-e.parent) b old ∈ oldNeeds G e b :=
      List.mem_map_of_mem hold
    exact endpoint_weaken hf hb (hseam t ht) (oldNeeds_valid hv hcut b _ hm)
      hp hprof (htop _ hm)

end IPD.Semantics

#print axioms IPD.Semantics.endpoint_weaken
#print axioms IPD.Semantics.control_admissible
#print axioms IPD.Semantics.seam_usable
