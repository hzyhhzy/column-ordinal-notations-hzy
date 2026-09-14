import OrdinalFormal.ReflectionTransport

/-!
An explicit raw old/copy/seam diagram. Root closure may be performed AFTER
reflection and label splicing; it does not have to be smuggled into an exact
copy classification. This is a finite construction, not a semantic existence
axiom. The final transport theorem still displays its reflection assumptions.
-/

namespace OrdinalFormal.SpliceConstruction

open ReflectionTransport
set_option maxHeartbeats 500000

universe u v
variable {Row : Type u} {Label : Type v}

theorem moveColumn_mono {n cut i j : Nat} (hCut : cut ≤ n) (h : i ≤ j) :
    moveColumn n cut i ≤ moveColumn n cut j := by
  unfold moveColumn
  split <;> split <;> omega

theorem moveColumn_strict {n cut i j : Nat} (hCut : cut ≤ n) (h : i < j) :
    moveColumn n cut i < moveColumn n cut j := by
  unfold moveColumn
  split <;> split <;> omega

theorem moved_valid {n cut : Nat} (hCut : cut ≤ n) {e : Atom Row}
    (he : e.Valid n) : (moveAtom n cut e).Valid (n + (n - cut)) := by
  exact ⟨moveColumn_mono hCut he.1, moveColumn_strict hCut he.2.1,
    moveColumn_lt hCut he.2.2⟩

def seamAtom (n : Nat) (d : TopAtom Row) : Atom Row :=
  ⟨d.layer, d.root, d.parent, n⟩

def rawSplice (G : Diagram Row) (cut : Nat) (facts : List (Atom Row))
    (needs : List (TopAtom Row)) (hCut : cut < G.size)
    (hFacts : ∀ e ∈ facts, e.Valid G.size)
    (hNeeds : ∀ d ∈ needs, d.Valid G.size) : Diagram Row where
  size := G.size + (G.size - cut)
  atoms := G.atoms ++ facts.map (moveAtom G.size cut) ++ needs.map (seamAtom G.size)
  valid := by
    intro e he
    simp only [List.mem_append, List.mem_map] at he
    rcases he with (he | he) | he
    · have hv := G.valid e he
      exact ⟨hv.1, hv.2.1, by have := hv.2.2; omega⟩
    · obtain ⟨s, hs, rfl⟩ := he
      exact moved_valid (Nat.le_of_lt hCut) (hFacts s hs)
    · obtain ⟨d, hd, rfl⟩ := he
      have hv := hNeeds d hd
      exact ⟨hv.1, hv.2, by change G.size < G.size + (G.size - cut); omega⟩

theorem rawSplice_geometry (G : Diagram Row) (cut : Nat) (facts : List (Atom Row))
    (needs : List (TopAtom Row)) (hCut : cut < G.size)
    (hFacts : ∀ e ∈ facts, e.Valid G.size)
    (hNeeds : ∀ d ∈ needs, d.Valid G.size) :
    SpliceGeometry G (rawSplice G cut facts needs hCut hFacts hNeeds) cut facts needs := by
  constructor
  · rfl
  · intro e he
    simp only [rawSplice, List.mem_append, List.mem_map] at he
    rcases he with (he | he) | he
    · exact .inl he
    · obtain ⟨s, hs, rfl⟩ := he
      exact .inr (.inl ⟨s, hs, rfl, rfl, rfl, .inl rfl⟩)
    · obtain ⟨d, hd, rfl⟩ := he
      exact .inr (.inr ⟨d, hd, rfl, rfl, rfl, rfl⟩)

/-- If an actual output graph consists of old, copied and seam edges followed
by root weakening, the same spliced labels represent that actual output.
Root closure does not alter labels, so the reuse identity survives it. -/
theorem reflect_splice_and_close
    (rowLt : Row → Row → Prop)
    (lt : Label → Label → Prop) (D : Label → Prop)
    (R : Row → Label → Label → Label → Prop)
    (hTrans : ∀ {a b c}, lt a b → lt b c → lt a c)
    (hStrict : ∀ {k index a b}, R k index a b → lt a b)
    (hWeak : ∀ {k small large p c}, lt small large → R k large p c → R k small p c)
    (hLower : LowerRows rowLt lt R)
    (reflection : FiniteReflection rowLt lt D R)
    {G H : Diagram Row} {cut controlRoot : Nat} {K : Row}
    (facts : List (Atom Row)) (templates : List (TopAtom Row)) (needs : List (TopAtom Row))
    (hCut : cut < G.size) (hRoot : controlRoot ≤ cut)
    (hFactsValid : ∀ e ∈ facts, e.Valid G.size)
    (hTemplatesValid : ∀ d ∈ templates, d.Valid G.size)
    (hNeedsValid : ∀ d ∈ needs, d.Valid G.size)
    (closed : RootWeakeningGeometry
      (rawSplice G cut facts needs hCut hFactsValid hNeedsValid) H)
    (demands : ∀ d ∈ needs, StepDemand rowLt K cut controlRoot templates d)
    (f : Nat → Label) (beta : Label)
    (hF : Representation lt D R G f) (hBeta : D beta)
    (hBound : Bounded lt G.size f beta)
    (hControl : R K (f controlRoot) (f cut) beta)
    (hFacts : ∀ e ∈ facts, e.Holds R f)
    (hTemplates : ∀ d ∈ templates, d.Holds R f beta) :
    ∃ next : Nat → Label,
      Representation lt D R H next ∧ Bounded lt H.size next beta ∧
      (∀ i, i < G.size → next (moveColumn G.size cut i) = f i) ∧
      ∀ e ∈ facts, (moveAtom G.size cut e).Holds R next := by
  obtain ⟨next, hRep, hNewBound, hReuse, hNewFacts⟩ :=
    exists_bounded_representation_splice_with_lower_rows rowLt lt D R hTrans hStrict
      hWeak hLower reflection (rawSplice_geometry G cut facts needs hCut hFactsValid hNeedsValid)
      hCut hRoot f beta hF hBeta hBound hControl hFactsValid hFacts
      hTemplatesValid hTemplates hNeedsValid demands
  refine ⟨next, representation_rootWeakening lt D R hWeak closed next hRep, ?_, hReuse, hNewFacts⟩
  rw [closed.1]
  exact hNewBound

end OrdinalFormal.SpliceConstruction
