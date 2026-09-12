import Std

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-!
# Arbitrary-row root-indexed representations and reflection transport

Derived from Phyrion1343/1Y-Well-Ordering-Lean,
formalization/OneY/RootIndexed/Representation.lean,
commit 1689b21131b488ec2ba2515bd630360371a2389d, licensed Apache-2.0.
Modified 2026-09-12: generalize natural-number layers to an arbitrary Row type
with an explicit row relation; extend the transport interface to generated
lower-row demands. See the project third-party notices for the upstream license.

This module is parameterized by the label order and the root-indexed semantic
relations.  In particular, `FiniteReflection` below is an interface still to be
instantiated by the proposed truth structures; it is not a theorem about those
structures.  The geometric edge classification is also explicit data, rather
than an assertion that the concrete 1-Y algorithm has already been formalized.

No field postulates descent of 1-Y.  The main transport theorem constructs the
new labeling and checks old edges, copied edges with weakened roots, and seam
edges separately.
-/

namespace OrdinalFormal.ReflectionTransport

universe u v w

structure Atom (Row : Type v) where
  layer : Row
  root : Nat
  parent : Nat
  child : Nat
  deriving DecidableEq

variable {Row : Type v}

def Atom.Valid (e : Atom Row) (n : Nat) : Prop :=
  e.root ≤ e.parent ∧ e.parent < e.child ∧ e.child < n

structure Diagram (Row : Type v) where
  size : Nat
  atoms : List (Atom Row)
  valid : ∀ e ∈ atoms, e.Valid size

structure TopAtom (Row : Type v) where
  layer : Row
  root : Nat
  parent : Nat
  deriving DecidableEq

def TopAtom.Valid (e : TopAtom Row) (n : Nat) : Prop :=
  e.root ≤ e.parent ∧ e.parent < n

variable {α : Type u}

def Atom.Holds (R : Row → α → α → α → Prop) (f : Nat → α) (e : Atom Row) : Prop :=
  R e.layer (f e.root) (f e.parent) (f e.child)

def TopAtom.Holds (R : Row → α → α → α → Prop)
    (f : Nat → α) (top : α) (e : TopAtom Row) : Prop :=
  R e.layer (f e.root) (f e.parent) top

structure Representation (lt : α → α → Prop) (D : α → Prop)
    (R : Row → α → α → α → Prop) (G : Diagram Row) (f : Nat → α) : Prop where
  domain : ∀ i, i < G.size → D (f i)
  ordered : ∀ i j, i < j → j < G.size → lt (f i) (f j)
  relations : ∀ e ∈ G.atoms, e.Holds R f

def Bounded (lt : α → α → Prop) (n : Nat) (f : Nat → α) (bound : α) : Prop :=
  ∀ i, i < n → lt (f i) bound

/-- The left part stays put, while the old final block is moved to the right
of the whole old diagram. -/
def moveColumn (n cut i : Nat) : Nat :=
  if i < cut then i else n + (i - cut)

def moveAtom (n cut : Nat) (e : Atom Row) : Atom Row :=
  { e with root := moveColumn n cut e.root
           parent := moveColumn n cut e.parent
           child := moveColumn n cut e.child }

/-- `g` is the reflected old diagram.  The appended block reuses the old
labels `f`, starting at the cut. -/
def spliceLabel (n cut : Nat) (f g : Nat → α) (i : Nat) : α :=
  if i < n then g i else f (cut + i - n)

theorem spliceLabel_old {n cut i : Nat} (f g : Nat → α) (hi : i < n) :
    spliceLabel n cut f g i = g i := by
  simp [spliceLabel, hi]

theorem spliceLabel_first (n cut : Nat) (f g : Nat → α) :
    spliceLabel n cut f g n = f cut := by
  simp [spliceLabel]

theorem spliceLabel_move {n cut i : Nat} (f g : Nat → α)
    (_hCut : cut ≤ n) (hi : i < n)
    (hFixed : ∀ j, j < cut → g j = f j) :
    spliceLabel n cut f g (moveColumn n cut i) = f i := by
  by_cases hic : i < cut
  · simp [moveColumn, hic, spliceLabel, hi, hFixed i hic]
  · have hNew : ¬n + (i - cut) < n := by omega
    have hIndex : cut + (n + (i - cut)) - n = i := by omega
    simp [moveColumn, hic, spliceLabel, hNew, hIndex]

theorem moveColumn_lt {n cut i : Nat} (hCut : cut ≤ n) (hi : i < n) :
    moveColumn n cut i < n + (n - cut) := by
  unfold moveColumn
  split <;> omega

theorem moveAtom_holds (R : Row → α → α → α → Prop)
    {n cut : Nat} (f g : Nat → α) (e : Atom Row)
    (hCut : cut ≤ n) (he : e.Valid n)
    (hFixed : ∀ j, j < cut → g j = f j) (h : e.Holds R f) :
    (moveAtom n cut e).Holds R (spliceLabel n cut f g) := by
  rcases he with ⟨hRoot, hParent, hChild⟩
  unfold Atom.Holds moveAtom
  rw [spliceLabel_move f g hCut (by omega : e.root < n) hFixed,
      spliceLabel_move f g hCut (by omega : e.parent < n) hFixed,
      spliceLabel_move f g hCut hChild hFixed]
  exact h

def CopyCase (n cut : Nat) (facts : List (Atom Row)) (e : Atom Row) : Prop :=
  ∃ s ∈ facts,
    e.layer = s.layer ∧
    e.parent = moveColumn n cut s.parent ∧
    e.child = moveColumn n cut s.child ∧
    (e.root = moveColumn n cut s.root ∨ (e.root < n ∧ cut ≤ s.root))

def SeamCase (n : Nat) (needs : List (TopAtom Row)) (e : Atom Row) : Prop :=
  ∃ d ∈ needs,
    e.layer = d.layer ∧ e.root = d.root ∧ e.parent = d.parent ∧ e.child = n

/-- This is the finite combinatorial obligation supplied by root-indexed
transport, not a semantic/descent assumption.  The weakened-root branch of
`CopyCase` covers the inserted reference rows. -/
structure SpliceGeometry (G H : Diagram Row) (cut : Nat)
    (facts : List (Atom Row)) (needs : List (TopAtom Row)) : Prop where
  size_eq : H.size = G.size + (G.size - cut)
  classify : ∀ e ∈ H.atoms,
    e ∈ G.atoms ∨ CopyCase G.size cut facts e ∨ SeamCase G.size needs e

theorem spliceLabel_ordered (lt : α → α → Prop)
    (hTrans : ∀ {a b c}, lt a b → lt b c → lt a c)
    {n cut : Nat} (f g : Nat → α) (hCut : cut < n)
    (hF : ∀ i j, i < j → j < n → lt (f i) (f j))
    (hG : ∀ i j, i < j → j < n → lt (g i) (g j))
    (hBelow : Bounded lt n g (f cut)) :
    ∀ i j, i < j → j < n + (n - cut) →
      lt (spliceLabel n cut f g i) (spliceLabel n cut f g j) := by
  intro i j hij hj
  by_cases hjOld : j < n
  · rw [spliceLabel_old f g (by omega : i < n), spliceLabel_old f g hjOld]
    exact hG i j hij hjOld
  · have hjSource : cut + j - n < n := by omega
    have hjAt : cut ≤ cut + j - n := by omega
    by_cases hiOld : i < n
    · rw [spliceLabel_old f g hiOld]
      simp only [spliceLabel, if_neg hjOld]
      by_cases hEqual : cut + j - n = cut
      · rw [hEqual]
        exact hBelow i hiOld
      · exact hTrans (hBelow i hiOld)
          (hF cut (cut + j - n) (by omega) hjSource)
    · simp only [spliceLabel, if_neg hiOld, if_neg hjOld]
      exact hF _ _ (by omega) hjSource

theorem spliceLabel_bounded (lt : α → α → Prop)
    (hTrans : ∀ {a b c}, lt a b → lt b c → lt a c)
    {n cut : Nat} (f g : Nat → α) (beta : α)
    (hControl : lt (f cut) beta)
    (hF : Bounded lt n f beta) (hG : Bounded lt n g (f cut)) :
    Bounded lt (n + (n - cut)) (spliceLabel n cut f g) beta := by
  intro i hi
  by_cases hOld : i < n
  · rw [spliceLabel_old f g hOld]
    exact hTrans (hG i hOld) hControl
  · simp only [spliceLabel, if_neg hOld]
    exact hF _ (by omega)

/-- A completely explicit one-block construction.  All new root-index
relations are proved from preserved old relations, the original reservoir,
strict index weakening, or the reflected seam demands. -/
theorem representation_splice
    (lt : α → α → Prop) (D : α → Prop) (R : Row → α → α → α → Prop)
    (hTrans : ∀ {a b c}, lt a b → lt b c → lt a c)
    (hWeak : ∀ {k small large p c}, lt small large →
      R k large p c → R k small p c)
    {G H : Diagram Row} {cut : Nat} {facts : List (Atom Row)} {needs : List (TopAtom Row)}
    (geometry : SpliceGeometry G H cut facts needs) (hCut : cut < G.size)
    (hFactsValid : ∀ e ∈ facts, e.Valid G.size)
    (hNeedsValid : ∀ d ∈ needs, d.Valid G.size)
    (f g : Nat → α)
    (hF : Representation lt D R G f) (hG : Representation lt D R G g)
    (hFixed : ∀ i, i < cut → g i = f i)
    (hBelow : Bounded lt G.size g (f cut))
    (hFacts : ∀ e ∈ facts, e.Holds R f)
    (hNeeds : ∀ d ∈ needs, d.Holds R g (f cut)) :
    Representation lt D R H (spliceLabel G.size cut f g) := by
  constructor
  · intro i hi
    rw [geometry.size_eq] at hi
    by_cases hOld : i < G.size
    · rw [spliceLabel_old f g hOld]
      exact hG.domain i hOld
    · simp only [spliceLabel, if_neg hOld]
      exact hF.domain _ (by omega)
  · intro i j hij hj
    rw [geometry.size_eq] at hj
    exact spliceLabel_ordered lt hTrans f g hCut hF.ordered hG.ordered
      hBelow i j hij hj
  · intro e he
    rcases geometry.classify e he with hOld | hCopy | hSeam
    · have hv := G.valid e hOld
      unfold Atom.Holds
      rw [spliceLabel_old f g (by rcases hv with ⟨_,_,_⟩; omega : e.root < G.size),
          spliceLabel_old f g (by rcases hv with ⟨_,_,_⟩; omega : e.parent < G.size),
          spliceLabel_old f g hv.2.2]
      exact hG.relations e hOld
    · rcases hCopy with ⟨s, hs, hLayer, hParent, hChild, hRoot⟩
      have hv := hFactsValid s hs
      have hSRoot : s.root < G.size := by rcases hv with ⟨_,_,_⟩; omega
      have hSParent : s.parent < G.size := by rcases hv with ⟨_,_,_⟩; omega
      unfold Atom.Holds
      rw [hLayer, hParent, hChild,
          spliceLabel_move f g (by omega) hSParent hFixed,
          spliceLabel_move f g (by omega) hv.2.2 hFixed]
      rcases hRoot with hSame | ⟨hRootOld, hRootAfterCut⟩
      · rw [hSame, spliceLabel_move f g (by omega) hSRoot hFixed]
        exact hFacts s hs
      · rw [spliceLabel_old f g hRootOld]
        have hIndex : lt (g e.root) (f s.root) := by
          by_cases hEqual : s.root = cut
          · rw [hEqual]
            exact hBelow e.root hRootOld
          · exact hTrans (hBelow e.root hRootOld)
              (hF.ordered cut s.root (by omega) hSRoot)
        exact hWeak hIndex (hFacts s hs)
    · rcases hSeam with ⟨d, hd, hLayer, hRoot, hParent, hChild⟩
      have hv := hNeedsValid d hd
      unfold Atom.Holds
      rw [hLayer, hRoot, hParent, hChild,
          spliceLabel_old f g (by rcases hv with ⟨_,_⟩; omega : d.root < G.size),
          spliceLabel_old f g hv.2, spliceLabel_first]
      exact hNeeds d hd

/-- The reservoir itself is retained with its original labels in the new
last block, even when these stronger atoms are not edges of the current graph. -/
theorem reservoir_splice
    (R : Row → α → α → α → Prop) {n cut : Nat}
    (f g : Nat → α) (facts : List (Atom Row)) (hCut : cut ≤ n)
    (hValid : ∀ e ∈ facts, e.Valid n)
    (hFixed : ∀ i, i < cut → g i = f i)
    (hFacts : ∀ e ∈ facts, e.Holds R f) :
    ∀ e ∈ facts, (moveAtom n cut e).Holds R (spliceLabel n cut f g) := by
  intro e he
  exact moveAtom_holds R f g e hCut (hValid e he) hFixed (hFacts e he)

/-- A virtual-endpoint demand either retains the template's root or lowers
it from the final block to an earlier block. -/
def VirtualCase (cut : Nat) (templates : List (TopAtom Row)) (d : TopAtom Row) : Prop :=
  ∃ s ∈ templates,
    d.layer = s.layer ∧ d.parent = s.parent ∧
    (d.root = s.root ∨ (d.root < cut ∧ cut ≤ s.root))

theorem virtual_demands_from_templates
    (lt : α → α → Prop) (D : α → Prop) (R : Row → α → α → α → Prop)
    (hWeak : ∀ {k small large p c}, lt small large →
      R k large p c → R k small p c)
    {G : Diagram Row} {cut : Nat} (f : Nat → α) (beta : α)
    (hF : Representation lt D R G f)
    (templates needs : List (TopAtom Row))
    (hValid : ∀ s ∈ templates, s.Valid G.size)
    (hTemplate : ∀ s ∈ templates, s.Holds R f beta)
    (hClass : ∀ d ∈ needs, VirtualCase cut templates d) :
    ∀ d ∈ needs, d.Holds R f beta := by
  intro d hd
  rcases hClass d hd with ⟨s, hs, hLayer, hParent, hRoot⟩
  unfold TopAtom.Holds
  rw [hLayer, hParent]
  rcases hRoot with hSame | ⟨hBefore, hAfter⟩
  · rw [hSame]
    exact hTemplate s hs
  · have hv := hValid s hs
    have hRootLt : s.root < G.size := by rcases hv with ⟨_,_⟩; omega
    exact hWeak (hF.ordered d.root s.root (by omega) hRootLt) (hTemplate s hs)

/-- A demand to the ambient endpoint is allowed in a genuinely lower
language with a moving root, or in the controlling language with a fixed,
strictly smaller root index. -/
def Admissible (rowLt : Row → Row → Prop) (lt : α → α → Prop) (K : Row) (cut : Nat)
    (theta : α) (f : Nat → α) (d : TopAtom Row) : Prop :=
  rowLt d.layer K ∨ (d.layer = K ∧ d.root < cut ∧ lt (f d.root) theta)

theorem admissible_of_root_position
    (rowLt : Row → Row → Prop)
    (lt : α → α → Prop) (D : α → Prop) (R : Row → α → α → α → Prop)
    {G : Diagram Row} {cut controlRoot : Nat} {K : Row} (f : Nat → α)
    (hF : Representation lt D R G f) (hCut : cut < G.size)
    (hRoot : controlRoot ≤ cut) (d : TopAtom Row)
    (h : rowLt d.layer K ∨ (d.layer = K ∧ d.root < controlRoot)) :
    Admissible rowLt lt K cut (f controlRoot) f d := by
  rcases h with hLow | ⟨hSame, hBelow⟩
  · exact Or.inl hLow
  · exact Or.inr ⟨hSame, by omega,
      hF.ordered d.root controlRoot hBelow (by omega)⟩

/-- Still-to-be-instantiated semantic interface.  It asserts finite formula
reflection, not the existence of an expanded representation or a decreasing
rank.  The whole previous diagram is finite; its internal atoms may use
arbitrary rows, including rows above the current control. -/
def FiniteReflection (rowLt : Row → Row → Prop) (lt : α → α → Prop) (D : α → Prop)
    (R : Row → α → α → α → Prop) : Prop :=
  ∀ (G : Diagram Row) (cut : Nat) (K : Row) (theta beta : α) (f : Nat → α)
    (needs : List (TopAtom Row)),
    cut < G.size → Representation lt D R G f → D beta →
    Bounded lt G.size f beta →
    R K theta (f cut) beta →
    (∀ d ∈ needs, d.Valid G.size) →
    (∀ d ∈ needs, Admissible rowLt lt K cut theta f d) →
    (∀ d ∈ needs, d.Holds R f beta) →
    ∃ g : Nat → α,
      Representation lt D R G g ∧
      (∀ i, i < cut → g i = f i) ∧
      Bounded lt G.size g (f cut) ∧
      (∀ d ∈ needs, d.Holds R g (f cut))

/-- The reflection interface and purely finite edge classification imply
the actual one-block bounded representation construction.  Virtual beta
demands are derived from templates here, not assumed as a descent result. -/
theorem exists_bounded_representation_splice
    (rowLt : Row → Row → Prop)
    (lt : α → α → Prop) (D : α → Prop) (R : Row → α → α → α → Prop)
    (hTrans : ∀ {a b c}, lt a b → lt b c → lt a c)
    (hStrict : ∀ {k index a b}, R k index a b → lt a b)
    (hWeak : ∀ {k small large p c}, lt small large →
      R k large p c → R k small p c)
    (reflection : FiniteReflection rowLt lt D R)
    {G H : Diagram Row} {cut controlRoot : Nat} {K : Row}
    {facts : List (Atom Row)} {templates needs : List (TopAtom Row)}
    (geometry : SpliceGeometry G H cut facts needs)
    (hCut : cut < G.size) (hRoot : controlRoot ≤ cut)
    (f : Nat → α) (beta : α)
    (hF : Representation lt D R G f) (hBeta : D beta)
    (hBound : Bounded lt G.size f beta)
    (hControl : R K (f controlRoot) (f cut) beta)
    (hFactsValid : ∀ e ∈ facts, e.Valid G.size)
    (hFacts : ∀ e ∈ facts, e.Holds R f)
    (hTemplatesValid : ∀ d ∈ templates, d.Valid G.size)
    (hTemplates : ∀ d ∈ templates, d.Holds R f beta)
    (hNeedsValid : ∀ d ∈ needs, d.Valid G.size)
    (hVirtual : ∀ d ∈ needs, VirtualCase cut templates d)
    (hLevels : ∀ d ∈ needs,
      rowLt d.layer K ∨ (d.layer = K ∧ d.root < controlRoot)) :
    ∃ next : Nat → α,
      Representation lt D R H next ∧ Bounded lt H.size next beta ∧
      (∀ i, i < G.size → next (moveColumn G.size cut i) = f i) ∧
      (∀ e ∈ facts, (moveAtom G.size cut e).Holds R next) := by
  have hNeeds := virtual_demands_from_templates lt D R hWeak f beta hF
    templates needs hTemplatesValid hTemplates hVirtual
  have hAdmissible : ∀ d ∈ needs,
      Admissible rowLt lt K cut (f controlRoot) f d := by
    intro d hd
    exact admissible_of_root_position rowLt lt D R f hF hCut hRoot d (hLevels d hd)
  obtain ⟨g, hG, hFixed, hBelow, hAtAlpha⟩ :=
    reflection G cut K (f controlRoot) beta f needs hCut hF hBeta hBound
      hControl hNeedsValid hAdmissible hNeeds
  refine ⟨spliceLabel G.size cut f g, ?_, ?_, ?_, ?_⟩
  · exact representation_splice lt D R hTrans hWeak geometry hCut
      hFactsValid hNeedsValid f g hF hG hFixed hBelow hFacts hAtAlpha
  · rw [geometry.size_eq]
    exact spliceLabel_bounded lt hTrans f g beta (hStrict hControl) hBound hBelow
  · intro i hi
    exact spliceLabel_move f g (by omega) hi hFixed
  · exact reservoir_splice R f g facts (by omega) hFactsValid hFixed hFacts

def moveTopAtom (n cut : Nat) (d : TopAtom Row) : TopAtom Row :=
  { d with root := moveColumn n cut d.root
           parent := moveColumn n cut d.parent }

/-- A finite-block scheme contains only diagrams, column maps, and the
geometric classification of their edges.  It contains no labeling, stability
relation, reflection, or descent field. -/
structure BlockScheme (Row : Type v) (rowLt : Row → Row → Prop) where
  layer : Row
  graph : Nat → Diagram Row
  cut : Nat → Nat
  controlRoot : Nat → Nat
  facts : Nat → List (Atom Row)
  templates : Nat → List (TopAtom Row)
  needs : Nat → List (TopAtom Row)
  cut_lt : ∀ n, cut n < (graph n).size
  control_le : ∀ n, controlRoot n ≤ cut n
  geometry : ∀ n, SpliceGeometry (graph n) (graph (n+1))
    (cut n) (facts n) (needs n)
  facts_valid : ∀ n e, e ∈ facts n → e.Valid (graph n).size
  templates_valid : ∀ n d, d ∈ templates n → d.Valid (graph n).size
  needs_valid : ∀ n d, d ∈ needs n → d.Valid (graph n).size
  virtual : ∀ n d, d ∈ needs n → VirtualCase (cut n) (templates n) d
  levels : ∀ n d, d ∈ needs n →
    rowLt d.layer layer ∨ (d.layer = layer ∧ d.root < controlRoot n)
  cut_next : ∀ n, cut (n+1) = (graph n).size
  control_next : ∀ n,
    controlRoot (n+1) = moveColumn (graph n).size (cut n) (controlRoot n)
  facts_next : ∀ n, facts (n+1) =
    (facts n).map (moveAtom (graph n).size (cut n))
  templates_next : ∀ n, templates (n+1) =
    (templates n).map (moveTopAtom (graph n).size (cut n))

/-- The finite iteration of the one-block construction.  The original
labels in the last block and their virtual-beta facts are proved to survive
each reflection, rather than being postulated as the next-stage invariant. -/
theorem blockScheme_bounded_representations
    (rowLt : Row → Row → Prop)
    (lt : α → α → Prop) (D : α → Prop) (R : Row → α → α → α → Prop)
    (hTrans : ∀ {a b c}, lt a b → lt b c → lt a c)
    (hStrict : ∀ {k index a b}, R k index a b → lt a b)
    (hWeak : ∀ {k small large p c}, lt small large →
      R k large p c → R k small p c)
    (reflection : FiniteReflection rowLt lt D R)
    (S : BlockScheme Row rowLt) (f₀ : Nat → α) (beta : α)
    (hBeta : D beta)
    (hInitial : Representation lt D R (S.graph 0) f₀)
    (hBound : Bounded lt (S.graph 0).size f₀ beta)
    (hFacts : ∀ e ∈ S.facts 0, e.Holds R f₀)
    (hTemplates : ∀ d ∈ S.templates 0, d.Holds R f₀ beta)
    (hControl : R S.layer (f₀ (S.controlRoot 0)) (f₀ (S.cut 0)) beta) :
    ∀ n, ∃ f : Nat → α,
      Representation lt D R (S.graph n) f ∧
      Bounded lt (S.graph n).size f beta ∧
      (∀ e ∈ S.facts n, e.Holds R f) ∧
      (∀ d ∈ S.templates n, d.Holds R f beta) ∧
      R S.layer (f (S.controlRoot n)) (f (S.cut n)) beta := by
  intro n
  induction n with
  | zero => exact ⟨f₀, hInitial, hBound, hFacts, hTemplates, hControl⟩
  | succ n ih =>
      obtain ⟨f, hRep, hOldBound, hOldFacts, hOldTemplates, hOldControl⟩ := ih
      obtain ⟨next, hNewRep, hNewBound, hReuse, hNewFacts⟩ :=
        exists_bounded_representation_splice rowLt lt D R hTrans hStrict hWeak
          reflection (S.geometry n) (S.cut_lt n) (S.control_le n)
          f beta hRep hBeta hOldBound hOldControl
          (S.facts_valid n) hOldFacts (S.templates_valid n) hOldTemplates
          (S.needs_valid n) (S.virtual n) (S.levels n)
      refine ⟨next, hNewRep, hNewBound, ?_, ?_, ?_⟩
      · intro e he
        rw [S.facts_next n] at he
        obtain ⟨old, hOld, rfl⟩ := List.mem_map.mp he
        exact hNewFacts old hOld
      · intro d hd
        rw [S.templates_next n] at hd
        obtain ⟨old, hOld, rfl⟩ := List.mem_map.mp hd
        have hv := S.templates_valid n old hOld
        have hRootLt : old.root < (S.graph n).size := by
          rcases hv with ⟨_,_⟩; omega
        unfold TopAtom.Holds moveTopAtom
        rw [hReuse old.root hRootLt, hReuse old.parent hv.2]
        exact hOldTemplates old hOld
      · rw [S.control_next n, S.cut_next n]
        have hRootLt : S.controlRoot n < (S.graph n).size :=
          Nat.lt_of_le_of_lt (S.control_le n) (S.cut_lt n)
        rw [hReuse _ hRootLt]
        have hCutReuse := hReuse (S.cut n) (S.cut_lt n)
        simp only [moveColumn, Nat.lt_irrefl, ↓reduceIte, Nat.sub_self,
          Nat.add_zero] at hCutReuse
        rw [hCutReuse]
        exact hOldControl

/-- Prefix restriction records only the graph facts needed for deletion;
the concrete mountain construction must establish this prefix property. -/
def Diagram.IsPrefix (H G : Diagram Row) : Prop :=
  H.size ≤ G.size ∧ ∀ e ∈ H.atoms, e ∈ G.atoms

theorem representation_prefix
    (lt : α → α → Prop) (D : α → Prop) (R : Row → α → α → α → Prop)
    {G H : Diagram Row} (hPrefix : H.IsPrefix G) (f : Nat → α)
    (hF : Representation lt D R G f) : Representation lt D R H f := by
  constructor
  · intro i hi
    exact hF.domain i (Nat.lt_of_lt_of_le hi hPrefix.1)
  · intro i j hij hj
    exact hF.ordered i j hij (Nat.lt_of_lt_of_le hj hPrefix.1)
  · intro e he
    exact hF.relations e (hPrefix.2 e he)

/-- Any representation with the indicated last label; no minimum is chosen. -/
def LastRepresentation (lt : α → α → Prop) (D : α → Prop)
    (R : Row → α → α → α → Prop) (G : Diagram Row) (a : α) : Prop :=
  0 < G.size ∧ ∃ f : Nat → α,
    Representation lt D R G f ∧ f (G.size - 1) = a

theorem last_label_of_bounded_representation
    (lt : α → α → Prop) (D : α → Prop) (R : Row → α → α → α → Prop)
    {G : Diagram Row} (hNonempty : 0 < G.size) (f : Nat → α) (beta : α)
    (hRep : Representation lt D R G f) (hBound : Bounded lt G.size f beta) :
    ∃ a, lt a beta ∧ LastRepresentation lt D R G a := by
  refine ⟨f (G.size - 1), hBound _ (by omega), hNonempty, f, hRep, rfl⟩

theorem proper_prefix_lowers_last_label
    (lt : α → α → Prop) (D : α → Prop) (R : Row → α → α → α → Prop)
    {G H : Diagram Row} (hPrefix : H.IsPrefix G)
    (hStrict : H.size < G.size) (hNonempty : 0 < H.size)
    (beta : α) (hRep : LastRepresentation lt D R G beta) :
    ∃ a, lt a beta ∧ LastRepresentation lt D R H a := by
  obtain ⟨_, f, hF, hLast⟩ := hRep
  refine ⟨f (H.size - 1), ?_, hNonempty, f,
    representation_prefix lt D R hPrefix f hF, rfl⟩
  rw [← hLast]
  exact hF.ordered _ _ (by omega) (by omega)

/-- Accessibility can be proved using any valid label, with a fresh smaller
valid label after each step.  There is no global minimum-label choice here. -/
theorem accessible_of_lowerable_labels
    {State : Type w} (step : State → State → Prop)
    (lt : α → α → Prop) (valid : State → α → Prop)
    (lower : ∀ {s t a}, valid s a → step t s →
      ∃ b, lt b a ∧ valid t b)
    {a : α} (ha : Acc lt a) :
    ∀ s, valid s a → Acc step s := by
  induction ha with
  | intro a _ ih =>
      intro s hs
      apply Acc.intro s
      intro t hStep
      obtain ⟨b, hb, hValid⟩ := lower hs hStep
      exact ih b hb t hValid

theorem wellFounded_of_lowerable_labels
    {State : Type w} (step : State → State → Prop)
    (lt : α → α → Prop) (valid : State → α → Prop)
    (hWF : WellFounded lt)
    (initial : ∀ s, ∃ a, valid s a)
    (lower : ∀ {s t a}, valid s a → step t s →
      ∃ b, lt b a ∧ valid t b) : WellFounded step := by
  constructor
  intro s
  obtain ⟨a, ha⟩ := initial s
  exact accessible_of_lowerable_labels step lt valid lower (hWF.apply a) s ha

#print axioms representation_splice
#print axioms virtual_demands_from_templates
#print axioms exists_bounded_representation_splice
#print axioms blockScheme_bounded_representations
#print axioms wellFounded_of_lowerable_labels

/-! ## Additional lower-row seams

The following interfaces are the extra semantic input used by LRD and by
the fixed-row interpretation of self-indexed graphs. They do not assert
termination, nor are they instantiated by a truth model in this module.
-/

/-- A higher-row relation supplies lower-row relations at every root at or
below its parent label. Equality is explicit, so no order typeclass is needed. -/
def LowerRows (rowLt : Row → Row → Prop) (lt : α → α → Prop)
    (R : Row → α → α → α → Prop) : Prop :=
  ∀ {low high theta eta a b}, rowLt low high →
    (eta = a ∨ lt eta a) → R high theta a b → R low eta a b

/-- A fresh generated demand need not occur in the old endpoint template.
Its parent is the cut, its root is no further right, and its row is lower. -/
def GeneratedCase (rowLt : Row → Row → Prop) (K : Row) (cut : Nat)
    (d : TopAtom Row) : Prop :=
  rowLt d.layer K ∧ d.parent = cut ∧ d.root ≤ cut

/-- A permitted demand is an admissible old-template demand, or a new
strictly lower-row demand. This is finite geometric data, not a semantic axiom. -/
def StepDemand (rowLt : Row → Row → Prop) (K : Row)
    (cut controlRoot : Nat) (templates : List (TopAtom Row))
    (d : TopAtom Row) : Prop :=
  (VirtualCase cut templates d ∧
    (rowLt d.layer K ∨ (d.layer = K ∧ d.root < controlRoot))) ∨
  GeneratedCase rowLt K cut d

theorem generated_demand_holds
    (rowLt : Row → Row → Prop) (lt : α → α → Prop) (D : α → Prop)
    (R : Row → α → α → α → Prop) (hLower : LowerRows rowLt lt R)
    {G : Diagram Row} {cut controlRoot : Nat} {K : Row}
    (f : Nat → α) (beta : α) (hF : Representation lt D R G f)
    (hCut : cut < G.size)
    (hControl : R K (f controlRoot) (f cut) beta)
    (d : TopAtom Row) (h : GeneratedCase rowLt K cut d) :
    d.Holds R f beta := by
  rcases h with ⟨hRow, hParent, hRoot⟩
  unfold TopAtom.Holds
  rw [hParent]
  apply hLower hRow ?_ hControl
  by_cases heq : d.root = cut
  · exact Or.inl (congrArg f heq)
  · exact Or.inr (hF.ordered d.root cut (by omega) hCut)

theorem generated_demand_admissible
    (rowLt : Row → Row → Prop) (lt : α → α → Prop)
    {K : Row} {cut : Nat} (theta : α) (f : Nat → α)
    (d : TopAtom Row) (h : GeneratedCase rowLt K cut d) :
    Admissible rowLt lt K cut theta f d :=
  Or.inl h.1

/-- This is the original one-block proof with both kinds of endpoint
requirements. In particular generated lower rows are justified by `LowerRows`,
not assumed to be old template facts. -/
theorem exists_bounded_representation_splice_with_lower_rows
    (rowLt : Row → Row → Prop)
    (lt : α → α → Prop) (D : α → Prop) (R : Row → α → α → α → Prop)
    (hTrans : ∀ {a b c}, lt a b → lt b c → lt a c)
    (hStrict : ∀ {k index a b}, R k index a b → lt a b)
    (hWeak : ∀ {k small large p c}, lt small large →
      R k large p c → R k small p c)
    (hLower : LowerRows rowLt lt R)
    (reflection : FiniteReflection rowLt lt D R)
    {G H : Diagram Row} {cut controlRoot : Nat} {K : Row}
    {facts : List (Atom Row)} {templates needs : List (TopAtom Row)}
    (geometry : SpliceGeometry G H cut facts needs)
    (hCut : cut < G.size) (hRoot : controlRoot ≤ cut)
    (f : Nat → α) (beta : α)
    (hF : Representation lt D R G f) (hBeta : D beta)
    (hBound : Bounded lt G.size f beta)
    (hControl : R K (f controlRoot) (f cut) beta)
    (hFactsValid : ∀ e ∈ facts, e.Valid G.size)
    (hFacts : ∀ e ∈ facts, e.Holds R f)
    (hTemplatesValid : ∀ d ∈ templates, d.Valid G.size)
    (hTemplates : ∀ d ∈ templates, d.Holds R f beta)
    (hNeedsValid : ∀ d ∈ needs, d.Valid G.size)
    (hDemand : ∀ d ∈ needs, StepDemand rowLt K cut controlRoot templates d) :
    ∃ next : Nat → α,
      Representation lt D R H next ∧ Bounded lt H.size next beta ∧
      (∀ i, i < G.size → next (moveColumn G.size cut i) = f i) ∧
      (∀ e ∈ facts, (moveAtom G.size cut e).Holds R next) := by
  have hNeeds : ∀ d ∈ needs, d.Holds R f beta := by
    intro d hd
    rcases hDemand d hd with ⟨hVirtual, _⟩ | hGenerated
    · apply virtual_demands_from_templates lt D R hWeak (cut := cut) f beta hF
        templates [d] hTemplatesValid hTemplates ?_ d (by simp)
      intro d' hd'
      have heq : d' = d := by simpa using hd'
      subst d'
      exact hVirtual
    · exact generated_demand_holds rowLt lt D R hLower f beta hF hCut
        hControl d hGenerated
  have hAdmissible : ∀ d ∈ needs,
      Admissible rowLt lt K cut (f controlRoot) f d := by
    intro d hd
    rcases hDemand d hd with ⟨_, hLevel⟩ | hGenerated
    · exact admissible_of_root_position rowLt lt D R f hF hCut hRoot d hLevel
    · exact generated_demand_admissible rowLt lt (f controlRoot) f d hGenerated
  obtain ⟨g, hG, hFixed, hBelow, hAtAlpha⟩ :=
    reflection G cut K (f controlRoot) beta f needs hCut hF hBeta hBound
      hControl hNeedsValid hAdmissible hNeeds
  refine ⟨spliceLabel G.size cut f g, ?_, ?_, ?_, ?_⟩
  · exact representation_splice lt D R hTrans hWeak geometry hCut
      hFactsValid hNeedsValid f g hF hG hFixed hBelow hFacts hAtAlpha
  · rw [geometry.size_eq]
    exact spliceLabel_bounded lt hTrans f g beta (hStrict hControl) hBound hBelow
  · intro i hi
    exact spliceLabel_move f g (by omega) hi hFixed
  · exact reservoir_splice R f g facts (by omega) hFactsValid hFixed hFacts

/-- A block scheme with arbitrary finite lower-row generation at each block.
There is no bound on the block count and no terminations or labels in this data. -/
structure GeneratedBlockScheme (Row : Type v) (rowLt : Row → Row → Prop) where
  layer : Row
  graph : Nat → Diagram Row
  cut : Nat → Nat
  controlRoot : Nat → Nat
  facts : Nat → List (Atom Row)
  templates : Nat → List (TopAtom Row)
  needs : Nat → List (TopAtom Row)
  cut_lt : ∀ n, cut n < (graph n).size
  control_le : ∀ n, controlRoot n ≤ cut n
  geometry : ∀ n, SpliceGeometry (graph n) (graph (n+1))
    (cut n) (facts n) (needs n)
  facts_valid : ∀ n e, e ∈ facts n → e.Valid (graph n).size
  templates_valid : ∀ n d, d ∈ templates n → d.Valid (graph n).size
  needs_valid : ∀ n d, d ∈ needs n → d.Valid (graph n).size
  demand : ∀ n d, d ∈ needs n →
    StepDemand rowLt layer (cut n) (controlRoot n) (templates n) d
  cut_next : ∀ n, cut (n+1) = (graph n).size
  control_next : ∀ n,
    controlRoot (n+1) = moveColumn (graph n).size (cut n) (controlRoot n)
  facts_next : ∀ n, facts (n+1) =
    (facts n).map (moveAtom (graph n).size (cut n))
  templates_next : ∀ n, templates (n+1) =
    (templates n).map (moveTopAtom (graph n).size (cut n))

theorem generatedBlockScheme_bounded_representations
    (rowLt : Row → Row → Prop)
    (lt : α → α → Prop) (D : α → Prop) (R : Row → α → α → α → Prop)
    (hTrans : ∀ {a b c}, lt a b → lt b c → lt a c)
    (hStrict : ∀ {k index a b}, R k index a b → lt a b)
    (hWeak : ∀ {k small large p c}, lt small large →
      R k large p c → R k small p c)
    (hLower : LowerRows rowLt lt R)
    (reflection : FiniteReflection rowLt lt D R)
    (S : GeneratedBlockScheme Row rowLt) (f₀ : Nat → α) (beta : α)
    (hBeta : D beta)
    (hInitial : Representation lt D R (S.graph 0) f₀)
    (hBound : Bounded lt (S.graph 0).size f₀ beta)
    (hFacts : ∀ e ∈ S.facts 0, e.Holds R f₀)
    (hTemplates : ∀ d ∈ S.templates 0, d.Holds R f₀ beta)
    (hControl : R S.layer (f₀ (S.controlRoot 0)) (f₀ (S.cut 0)) beta) :
    ∀ n, ∃ f : Nat → α,
      Representation lt D R (S.graph n) f ∧
      Bounded lt (S.graph n).size f beta ∧
      (∀ e ∈ S.facts n, e.Holds R f) ∧
      (∀ d ∈ S.templates n, d.Holds R f beta) ∧
      R S.layer (f (S.controlRoot n)) (f (S.cut n)) beta := by
  intro n
  induction n with
  | zero => exact ⟨f₀, hInitial, hBound, hFacts, hTemplates, hControl⟩
  | succ n ih =>
      obtain ⟨f, hRep, hOldBound, hOldFacts, hOldTemplates, hOldControl⟩ := ih
      obtain ⟨next, hNewRep, hNewBound, hReuse, hNewFacts⟩ :=
        exists_bounded_representation_splice_with_lower_rows rowLt lt D R
          hTrans hStrict hWeak hLower reflection
          (S.geometry n) (S.cut_lt n) (S.control_le n) f beta
          hRep hBeta hOldBound hOldControl (S.facts_valid n) hOldFacts
          (S.templates_valid n) hOldTemplates (S.needs_valid n) (S.demand n)
      refine ⟨next, hNewRep, hNewBound, ?_, ?_, ?_⟩
      · intro e he
        rw [S.facts_next n] at he
        obtain ⟨old, hOld, rfl⟩ := List.mem_map.mp he
        exact hNewFacts old hOld
      · intro d hd
        rw [S.templates_next n] at hd
        obtain ⟨old, hOld, rfl⟩ := List.mem_map.mp hd
        have hv := S.templates_valid n old hOld
        have hRootLt : old.root < (S.graph n).size := by
          rcases hv with ⟨_, _⟩; omega
        unfold TopAtom.Holds moveTopAtom
        rw [hReuse old.root hRootLt, hReuse old.parent hv.2]
        exact hOldTemplates old hOld
      · rw [S.control_next n, S.cut_next n]
        have hRootLt : S.controlRoot n < (S.graph n).size :=
          Nat.lt_of_le_of_lt (S.control_le n) (S.cut_lt n)
        rw [hReuse _ hRootLt]
        have hCutReuse := hReuse (S.cut n) (S.cut_lt n)
        simp only [moveColumn, Nat.lt_irrefl, ↓reduceIte, Nat.sub_self,
          Nat.add_zero] at hCutReuse
        rw [hCutReuse]
        exact hOldControl

/-- Root-downward closure and removal of redundant edges preserve any
representation. The relation only gives finite edge classification. -/
def RootWeakeningGeometry (G H : Diagram Row) : Prop :=
  H.size = G.size ∧ ∀ e ∈ H.atoms, ∃ s ∈ G.atoms,
    e.layer = s.layer ∧ e.parent = s.parent ∧ e.child = s.child ∧ e.root ≤ s.root

theorem representation_rootWeakening
    (lt : α → α → Prop) (D : α → Prop) (R : Row → α → α → α → Prop)
    (hWeak : ∀ {k small large p c}, lt small large →
      R k large p c → R k small p c)
    {G H : Diagram Row} (geometry : RootWeakeningGeometry G H)
    (f : Nat → α) (hF : Representation lt D R G f) :
    Representation lt D R H f := by
  constructor
  · intro i hi
    rw [geometry.1] at hi
    exact hF.domain i hi
  · intro i j hij hj
    rw [geometry.1] at hj
    exact hF.ordered i j hij hj
  · intro e he
    obtain ⟨s, hs, hLayer, hParent, hChild, hRoot⟩ := geometry.2 e he
    unfold Atom.Holds
    rw [hLayer, hParent, hChild]
    by_cases heq : e.root = s.root
    · rw [heq]
      exact hF.relations s hs
    · have hv := G.valid s hs
      have hr : s.root < G.size := by rcases hv with ⟨_, _, _⟩; omega
      exact hWeak (hF.ordered e.root s.root (by omega) hr) (hF.relations s hs)

#print axioms exists_bounded_representation_splice_with_lower_rows
#print axioms generatedBlockScheme_bounded_representations
#print axioms representation_rootWeakening

/-- The concrete relation is oriented `step smaller larger`. Its empty
diagrams are terminal; nonempty targets have smaller valid last labels.
These are explicit obligations, not axioms of the four notation systems. -/
theorem diagram_step_wellFounded_of_initial_and_lowering
    (lt : α → α → Prop) (D : α → Prop) (R : Row → α → α → α → Prop)
    (hWF : WellFounded lt) (step : Diagram Row → Diagram Row → Prop)
    (step_nonempty : ∀ {G H}, step H G → 0 < G.size)
    (initial : ∀ G, ∃ f : Nat → α, Representation lt D R G f)
    (lower : ∀ {G H beta}, LastRepresentation lt D R G beta → step H G →
      0 < H.size → ∃ a, lt a beta ∧ LastRepresentation lt D R H a) :
    WellFounded step := by
  have hAcc : ∀ a, Acc lt a → ∀ G,
      LastRepresentation lt D R G a → Acc step G := by
    intro a ha
    induction ha with
    | intro a _ ih =>
        intro G hG
        apply Acc.intro G
        intro H hHG
        by_cases hH : 0 < H.size
        · obtain ⟨b, hba, hValid⟩ := lower hG hHG hH
          exact ih b hba H hValid
        · apply Acc.intro H
          intro I hIH
          have hPos := step_nonempty hIH
          omega
  constructor
  intro G
  by_cases hG : 0 < G.size
  · obtain ⟨f, hF⟩ := initial G
    exact hAcc (f (G.size - 1)) (hWF.apply _) G ⟨hG, f, hF, rfl⟩
  · apply Acc.intro G
    intro H hHG
    have hPos := step_nonempty hHG
    omega

/-- A proper graph prefix inherits a representation bounded by the original
last label. This supplies the initial reservoir for the block construction. -/
theorem bounded_representation_of_proper_prefix
    (lt : α → α → Prop) (D : α → Prop) (R : Row → α → α → α → Prop)
    {G H : Diagram Row} (hPrefix : H.IsPrefix G) (hStrict : H.size < G.size)
    (beta : α) (hRep : LastRepresentation lt D R G beta) :
    ∃ f : Nat → α, Representation lt D R H f ∧ Bounded lt H.size f beta := by
  obtain ⟨_, f, hF, hLast⟩ := hRep
  refine ⟨f, representation_prefix lt D R hPrefix f hF, ?_⟩
  intro i hi
  rw [← hLast]
  exact hF.ordered i (G.size - 1) (by omega) (by omega)

#print axioms diagram_step_wellFounded_of_initial_and_lowering
#print axioms bounded_representation_of_proper_prefix

end OrdinalFormal.ReflectionTransport
