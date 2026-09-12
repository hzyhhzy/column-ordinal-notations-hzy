import OrdinalFormal.ActualBlockGeometry
import OrdinalFormal.SpliceConstruction

/-!
Generalized from the local `RPDStagedReflection.lean` implementation; the
original module is unchanged. The underlying semantic transport module retains
its upstream attribution and derivation notices.

The actual generated-row block's ordinary and generated seam requirements,
supplied to finite reflection. Generated rows are justified by the explicit
lower-row semantic law and the actual package-decrease property. This module
does not instantiate the truth/reflection model or claim concrete well-ordering.
-/

namespace OrdinalFormal.GeneratedStagedReflection
open Columns
set_option autoImplicit false
set_option maxHeartbeats 700000
universe u v
variable {Row : Type u} {Label : Type v}
variable (cmp : Row → Row → Ordering) (package : Package Row)

def state (g : Graph Row) (e : Entry Row) (b : Nat) : Graph Row :=
  ActualBlockGeometry.stage cmp package g e b

def width (g : Graph Row) (e : Entry Row) (b : Nat) : Nat :=
  g.length - 1 + b * (g.length - 1 - e.parent)

def cut (g : Graph Row) (e : Entry Row) (b : Nat) : Nat :=
  e.parent + b * (g.length - 1 - e.parent)

def shift (g : Graph Row) (e : Entry Row) (b i : Nat) : Nat :=
  move e.parent (g.length - 1 - e.parent) b i

theorem state_length (g : Graph Row) (e : Entry Row) (b : Nat) :
    (state cmp package g e b).length = width g e b := ActualBlockGeometry.stage_length _ _ _ _ _

theorem cut_lt {g : Graph Row} {e : Entry Row} (he : e.parent < g.length - 1) (b : Nat) :
    cut g e b < width g e b := by unfold cut width; omega

theorem shift_lt {g : Graph Row} {e : Entry Row} {i : Nat}
    (hi : i < g.length - 1) (b : Nat) : shift g e b i < width g e b :=
  ExpansionValidity.move_lt_shift _ _ _ hi

theorem shift_cut (g : Graph Row) (e : Entry Row) (b : Nat) :
    shift g e b e.parent = cut g e b := by simp [shift, cut, move]

theorem root_le_cut {g : Graph Row} {e : Entry Row} (hr : e.root ≤ e.parent) (b : Nat) :
    shift g e b e.root ≤ cut g e b := by
  rw [← shift_cut]
  exact ExpansionValidity.move_mono _ _ _ hr

theorem width_succ {g : Graph Row} {e : Entry Row}
    (he : e.parent < g.length - 1) (b : Nat) :
    width g e (b + 1) = width g e b + (width g e b - cut g e b) := by
  unfold width cut
  simp only [Nat.add_mul, Nat.one_mul]
  omega

theorem shift_succ {g : Graph Row} {e : Entry Row}
    (he : e.parent < g.length - 1) (b i : Nat) :
    ReflectionTransport.moveColumn (width g e b) (cut g e b) (shift g e b i) =
      shift g e (b + 1) i :=
  ColumnRepresentation.move_succ _ _ _ _ (Nat.le_of_lt he)

def endpoint (a : Entry Row) : ReflectionTransport.TopAtom Row := ⟨a.row, a.root, a.parent⟩

def seam (g : Graph Row) (e : Entry Row) (b : Nat) : Column Row :=
  ordinarySeam cmp (g.getLast?.getD []) e (g.length - 1 - e.parent) b ++
    generatedSeam package e (g.length - 1 - e.parent) b

def needs (g : Graph Row) (e : Entry Row) (b : Nat) : List (ReflectionTransport.TopAtom Row) :=
  (seam cmp package g e b).map endpoint

def Templates (R : Row → Label → Label → Label → Prop)
    (g : Graph Row) (e : Entry Row) (b : Nat) (f : Nat → Label) (beta : Label) : Prop :=
  ∀ a ∈ g.getLast?.getD [], R a.row (f (shift g e b a.root)) (f (shift g e b a.parent)) beta

def Facts (R : Row → Label → Label → Label → Prop)
    (g : Graph Row) (e : Entry Row) (b : Nat) (f : Nat → Label) : Prop :=
  ∀ j, j < g.length - 1 → ∀ a ∈ g[j]?.getD [],
    R a.row (f (shift g e b a.root)) (f (shift g e b a.parent)) (f (shift g e b j))

theorem seam_valid {g : Graph Row} (hg : Valid g) (e : Entry Row)
    (he : e.parent < g.length - 1) (b : Nat) :
    ∀ a ∈ seam cmp package g e b, a.root ≤ a.parent ∧ a.parent < width g e b := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · apply ExpansionValidity.ordinarySeam_bounds cmp (g.getLast?.getD []) e
      (g.length - 1 - e.parent) b (g.length - 1) ?_ a ha
    intro s hs
    rw [List.getLast?_eq_getElem?] at hs
    exact hg _ s hs
  · obtain ⟨row, _, hm⟩ := List.mem_flatMap.mp ha
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
    have hq' := List.mem_range.mp hq
    have hm' : move e.parent (g.length - 1 - e.parent) b e.parent = cut g e b := shift_cut g e b
    simp only [hm'] at hq' ⊢
    exact ⟨by omega, cut_lt he b⟩

theorem needs_valid {g : Graph Row} (hg : Valid g) (e : Entry Row) (he : e.parent < g.length - 1) (b : Nat) :
    ∀ d ∈ needs cmp package g e b, d.Valid (width g e b) := by
  intro d hd
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hd
  exact seam_valid cmp package hg e he b a ha

/-- Direct weakening of an old endpoint template justifies every real seam
entry, even when its smaller root lies inside the current last block. -/
theorem needs_hold
    (rowLt : Row → Row → Prop)
    (lt : Label → Label → Prop) (D : Label → Prop)
    (R : Row → Label → Label → Label → Prop)
    (hWeak : ∀ {k small large p c}, lt small large → R k large p c → R k small p c)
    (hLower : ReflectionTransport.LowerRows rowLt lt R)
    (hPackage : ∀ high b low, low ∈ package high b → rowLt low high)
    {g : Graph Row} (hg : Valid g) (e : Entry Row)
    (he : Columns.control cmp (g.getLast?.getD []) = some e) (b : Nat)
    (f : Nat → Label) (beta : Label)
    (hF : ColumnRepresentation.Holds lt D R (state cmp package g e b) f)
    (hTemplates : Templates R g e b f beta) :
    ∀ d ∈ needs cmp package g e b, d.Holds R f beta := by
  intro d hd
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hd
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨s, hs, hm⟩ := List.mem_flatMap.mp ha
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
    have hqle : q ≤ shift g e b s.root := by
      have := List.mem_range.mp (List.mem_filter.mp hq).1
      change q < shift g e b s.root + 1 at this
      omega
    have hsBounds : s.root ≤ s.parent ∧ s.parent < g.length - 1 := by
      rw [List.getLast?_eq_getElem?] at hs
      exact hg _ s hs
    change R s.row (f q) (f (shift g e b s.parent)) beta
    by_cases heq : q = shift g e b s.root
    · rw [heq]
      exact hTemplates s hs
    · apply hWeak (hF.ordered q (shift g e b s.root) (by omega) ?_) (hTemplates s hs)
      rw [state_length]
      exact shift_lt (by omega) b
  · obtain ⟨low, hlow, hm⟩ := List.mem_flatMap.mp ha
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
    have hv := ExpansionValidity.control_valid cmp hg he
    have hcontrol := hTemplates e (ExpansionValidity.control_mem cmp he)
    have hqle : q ≤ cut g e b := by
      have hq' := List.mem_range.mp hq
      change q < shift g e b e.parent + 1 at hq'
      rw [shift_cut] at hq'
      omega
    change R low (f q) (f (shift g e b e.parent)) beta
    rw [shift_cut] at hcontrol ⊢
    apply hLower (hPackage e.row b low hlow) ?_ hcontrol
    by_cases hqeq : q = cut g e b
    · exact Or.inl (congrArg f hqeq)
    · apply Or.inr
      apply hF.ordered _ _ (by omega)
      rw [state_length]
      exact cut_lt hv.2 b

theorem needs_admissible
    (rowLt : Row → Row → Prop)
    (lt : Label → Label → Prop) (D : Label → Prop)
    (R : Row → Label → Label → Label → Prop)
    (laws : ColumnRepresentation.RowCompareSound cmp rowLt)
    (hPackage : ∀ high b low, low ∈ package high b → rowLt low high)
    {g : Graph Row} (e : Entry Row)
    (he : e.parent < g.length - 1) (hr : e.root ≤ e.parent) (b : Nat)
    (f : Nat → Label) (hF : ColumnRepresentation.Holds lt D R (state cmp package g e b) f) :
    ∀ d ∈ needs cmp package g e b,
      ReflectionTransport.Admissible rowLt lt e.row (cut g e b)
        (f (shift g e b e.root)) f d := by
  intro d hd
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hd
  rcases List.mem_append.mp ha with ha | ha
  · have hguard := ColumnRepresentation.ordinarySeam_guard cmp rowLt laws _ _ _ _ ha
    rcases hguard with hLow | ⟨hSame, hRoot⟩
    · exact Or.inl hLow
    · refine Or.inr ⟨hSame, ?_, ?_⟩
      · have := root_le_cut (g := g) hr b
        change a.root < shift g e b e.root at hRoot
        change a.root < cut g e b
        omega
      · apply hF.ordered _ _ hRoot
        rw [state_length]
        exact shift_lt (by omega) b
  · obtain ⟨low, hlow, hm⟩ := List.mem_flatMap.mp ha
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hm
    exact Or.inl (hPackage e.row b low hlow)

/-- Finite reflection instantiated with the real current graph and real seam.
The caller supplies the semantic reflection theorem and the current invariant,
not a hypothetical reflected representation or hypothetical valid seam demands. -/
theorem reflect_actual_stage
    (rowLt : Row → Row → Prop)
    (lt : Label → Label → Prop) (D : Label → Prop)
    (R : Row → Label → Label → Label → Prop)
    (hWeak : ∀ {k small large p c}, lt small large → R k large p c → R k small p c)
    (hLower : ReflectionTransport.LowerRows rowLt lt R)
    (hPackage : ∀ high b low, low ∈ package high b → rowLt low high)
    (laws : ColumnRepresentation.RowCompareSound cmp rowLt)
    (reflection : ReflectionTransport.FiniteReflection rowLt lt D R)
    {g : Graph Row} (hg : Valid g) (e : Entry Row)
    (he : Columns.control cmp (g.getLast?.getD []) = some e) (b : Nat)
    (f : Nat → Label) (beta : Label) (hBeta : D beta)
    (hF : ColumnRepresentation.Holds lt D R (state cmp package g e b) f)
    (hBound : ReflectionTransport.Bounded lt (width g e b) f beta)
    (hTemplates : Templates R g e b f beta) :
    ∃ reflected : Nat → Label,
      ColumnRepresentation.Holds lt D R (state cmp package g e b) reflected ∧
      (∀ i, i < cut g e b → reflected i = f i) ∧
      ReflectionTransport.Bounded lt (width g e b) reflected (f (cut g e b)) ∧
      (∀ d ∈ needs cmp package g e b, d.Holds R reflected (f (cut g e b))) := by
  have hv := ExpansionValidity.control_valid cmp hg he
  have hstate : Valid (state cmp package g e b) := ActualBlockGeometry.stage_valid _ _ hg e hv.2 b
  let G := ColumnRepresentation.toDiagram (state cmp package g e b) hstate
  have hsize : G.size = width g e b := state_length cmp package g e b
  have hrep : ReflectionTransport.Representation lt D R G f :=
    (ColumnRepresentation.holds_iff_representation lt D R _ hstate f).mp hF
  have hcontrol := hTemplates e (ExpansionValidity.control_mem cmp he)
  rw [shift_cut] at hcontrol
  obtain ⟨reflected, hrep', hfixed, hbelow, hneeds⟩ :=
    reflection G (cut g e b) e.row (f (shift g e b e.root)) beta f (needs cmp package g e b)
      (by rw [hsize]; exact cut_lt hv.2 b) hrep hBeta
      (by rwa [hsize]) hcontrol
      (by rw [hsize]; exact needs_valid cmp package hg e hv.2 b)
      (needs_admissible cmp package rowLt lt D R laws hPackage e hv.2 hv.1 b f hF)
      (needs_hold cmp package rowLt lt D R hWeak hLower hPackage hg e he b f beta hF hTemplates)
  refine ⟨reflected,
    (ColumnRepresentation.holds_iff_representation lt D R _ hstate reflected).mpr hrep',
    hfixed, ?_, hneeds⟩
  rwa [hsize] at hbelow

theorem weaken_entry
    (lt : Label → Label → Prop) (R : Row → Label → Label → Label → Prop)
    (hWeak : ∀ {k small large p c}, lt small large → R k large p c → R k small p c)
    (f : Nat → Label) (N j : Nat)
    (hOrdered : ∀ i k, i < k → k < N → lt (f i) (f k))
    (a s : Entry Row) (h : ActualBlockGeometry.Weakened a s) (hs : s.root < N)
    (hR : R s.row (f s.root) (f s.parent) (f j)) :
    R a.row (f a.root) (f a.parent) (f j) := by
  rw [h.1, h.2.1]
  by_cases heq : a.root = s.root
  · rwa [heq]
  · exact hWeak (hOrdered _ _ (by have := h.2.2; omega) hs) hR

/-- Splicing the actual reflected stage supplies the entire next invariant.
The proof classifies every edge of the real output, including normalization's
new small roots. No hypothetical next-graph representation is assumed. -/
theorem splice_actual_stage
    (lt : Label → Label → Prop) (D : Label → Prop)
    (R : Row → Label → Label → Label → Prop)
    (hTrans : ∀ {a b c}, lt a b → lt b c → lt a c)
    (hWeak : ∀ {k small large p c}, lt small large → R k large p c → R k small p c)
    {g : Graph Row} (hg : Valid g) (e : Entry Row)
    (he : e.parent < g.length - 1) (b : Nat)
    (f reflected : Nat → Label) (beta : Label)
    (hF : ColumnRepresentation.Holds lt D R (state cmp package g e b) f)
    (hRef : ColumnRepresentation.Holds lt D R (state cmp package g e b) reflected)
    (hFixed : ∀ i, i < cut g e b → reflected i = f i)
    (hBelow : ReflectionTransport.Bounded lt (width g e b) reflected (f (cut g e b)))
    (hBound : ReflectionTransport.Bounded lt (width g e b) f beta)
    (hCutBeta : lt (f (cut g e b)) beta)
    (hFacts : Facts R g e b f) (hTemplates : Templates R g e b f beta)
    (hNeeds : ∀ d ∈ needs cmp package g e b, d.Holds R reflected (f (cut g e b))) :
    let next := ReflectionTransport.spliceLabel (width g e b) (cut g e b) f reflected
    ColumnRepresentation.Holds lt D R (state cmp package g e (b + 1)) next ∧
      ReflectionTransport.Bounded lt (width g e (b + 1)) next beta ∧
      Facts R g e (b + 1) next ∧ Templates R g e (b + 1) next beta := by
  let next := ReflectionTransport.spliceLabel (width g e b) (cut g e b) f reflected
  change ColumnRepresentation.Holds lt D R (state cmp package g e (b + 1)) next ∧ _
  have hcut := cut_lt he b
  have hOrderF : ∀ i j, i < j → j < width g e b → lt (f i) (f j) := by
    intro i j hij hj
    exact hF.ordered i j hij (by rwa [state_length])
  have hOrderRef : ∀ i j, i < j → j < width g e b → lt (reflected i) (reflected j) := by
    intro i j hij hj
    exact hRef.ordered i j hij (by rwa [state_length])
  have hOrder : ∀ i j, i < j → j < width g e (b + 1) → lt (next i) (next j) := by
    rw [width_succ he]
    exact ReflectionTransport.spliceLabel_ordered lt hTrans f reflected hcut hOrderF hOrderRef hBelow
  have hBoundNext : ReflectionTransport.Bounded lt (width g e (b + 1)) next beta := by
    rw [width_succ he]
    exact ReflectionTransport.spliceLabel_bounded lt hTrans f reflected beta hCutBeta hBound hBelow
  have hReuse : ∀ i, i < g.length - 1 → next (shift g e (b + 1) i) = f (shift g e b i) := by
    intro i hi
    have h := ReflectionTransport.spliceLabel_move (n := width g e b) (cut := cut g e b)
      f reflected (Nat.le_of_lt hcut) (shift_lt hi b) hFixed
    rw [shift_succ he] at h
    exact h
  have hFactsNext : Facts R g e (b + 1) next := by
    intro j hj a ha
    have hv := hg j a ha
    rw [hReuse a.root (by omega), hReuse a.parent (by omega), hReuse j hj]
    exact hFacts j hj a ha
  have hTemplatesNext : Templates R g e (b + 1) next beta := by
    intro a ha
    have hv : a.root ≤ a.parent ∧ a.parent < g.length - 1 := by
      rw [List.getLast?_eq_getElem?] at ha
      exact hg _ a ha
    rw [hReuse a.root (by omega), hReuse a.parent hv.2]
    exact hTemplates a ha
  refine ⟨⟨?_, ?_, ?_⟩, hBoundNext, hFactsNext, hTemplatesNext⟩
  · intro i hi
    rw [state_length, width_succ he] at hi
    by_cases hold : i < width g e b
    · change D (ReflectionTransport.spliceLabel _ _ f reflected i)
      rw [ReflectionTransport.spliceLabel_old f reflected hold]
      exact hRef.domain i (by rwa [state_length])
    · change D (ReflectionTransport.spliceLabel _ _ f reflected i)
      simp only [ReflectionTransport.spliceLabel, if_neg hold]
      apply hF.domain
      rw [state_length]
      omega
  · intro i j hij hj
    exact hOrder i j hij (by rwa [state_length] at hj)
  · intro j a ha
    have horigin := ActualBlockGeometry.stage_step_origin cmp package g e b j ha
    rcases horigin with hold | ⟨i, hi, hj, horigin⟩
    · have hValidOld := ActualBlockGeometry.stage_valid cmp package hg e he b
      have hv := hValidOld j a hold
      have hj' := ColumnRepresentation.index_lt_of_entry_mem hold
      change j < (state cmp package g e b).length at hj'
      rw [state_length] at hj'
      change R a.row (ReflectionTransport.spliceLabel _ _ f reflected a.root)
        (ReflectionTransport.spliceLabel _ _ f reflected a.parent)
        (ReflectionTransport.spliceLabel _ _ f reflected j)
      rw [ReflectionTransport.spliceLabel_old f reflected (by omega),
        ReflectionTransport.spliceLabel_old f reflected (by omega),
        ReflectionTransport.spliceLabel_old f reflected hj']
      exact hRef.relations j a hold
    · rcases horigin with ⟨s, hs, hw⟩ | ⟨hi0, s, hs, hw⟩
      · have hsource : e.parent + i < g.length - 1 := by omega
        have hv := hg (e.parent + i) s hs
        have hchild : shift g e (b + 1) (e.parent + i) = j := by
          unfold shift move
          rw [if_neg (by omega)]
          simp only [Nat.add_mul, Nat.one_mul]
          omega
        have hRaw := hFactsNext (e.parent + i) hsource s hs
        rw [hchild] at hRaw
        apply weaken_entry lt R hWeak next (width g e (b + 1)) j hOrder a
          (moveEntry e.parent (g.length - 1 - e.parent) (b + 1) s) hw
          (shift_lt (by omega) (b + 1)) hRaw
      · subst i
        change j = width g e b + 0 at hj
        simp only [Nat.add_zero] at hj
        subst j
        have hs' : s ∈ seam cmp package g e b := hs
        have hv := seam_valid cmp package hg e he b s hs'
        have hRaw := hNeeds (endpoint s) (List.mem_map.mpr ⟨s, hs', rfl⟩)
        have hRawNext : R s.row (next s.root) (next s.parent) (next (width g e b)) := by
          change R s.row (ReflectionTransport.spliceLabel _ _ f reflected s.root)
            (ReflectionTransport.spliceLabel _ _ f reflected s.parent)
            (ReflectionTransport.spliceLabel _ _ f reflected (width g e b))
          rw [ReflectionTransport.spliceLabel_old f reflected (by omega),
            ReflectionTransport.spliceLabel_old f reflected hv.2,
            ReflectionTransport.spliceLabel_first]
          exact hRaw
        apply weaken_entry lt R hWeak next (width g e (b + 1)) (width g e b)
          hOrder a s hw ?_ hRawNext
        rw [width_succ he]
        omega

theorem holds_take
    (lt : Label → Label → Prop) (D : Label → Prop)
    (R : Row → Label → Label → Label → Prop)
    {g : Graph Row} {f : Nat → Label}
    (hF : ColumnRepresentation.Holds lt D R g f) (n : Nat) :
    ColumnRepresentation.Holds lt D R (g.take n) f := by
  constructor
  · intro i hi
    exact hF.domain i (by simp only [List.length_take] at hi; omega)
  · intro i j hij hj
    exact hF.ordered i j hij (by simp only [List.length_take] at hj; omega)
  · intro j a ha
    rw [List.getElem?_take] at ha
    split at ha
    · exact hF.relations j a ha
    · simp at ha

/-- Arbitrarily many actual blocks, proved by natural-number induction.
Neither the number of blocks nor the row heights are bounded in the theorem. -/
theorem all_stages
    (rowLt : Row → Row → Prop)
    (lt : Label → Label → Prop) (D : Label → Prop)
    (R : Row → Label → Label → Label → Prop)
    (hTrans : ∀ {a b c}, lt a b → lt b c → lt a c)
    (hStrict : ∀ {k index a b}, R k index a b → lt a b)
    (hWeak : ∀ {k small large p c}, lt small large → R k large p c → R k small p c)
    (hLower : ReflectionTransport.LowerRows rowLt lt R)
    (hPackage : ∀ high b low, low ∈ package high b → rowLt low high)
    (laws : ColumnRepresentation.RowCompareSound cmp rowLt)
    (reflection : ReflectionTransport.FiniteReflection rowLt lt D R)
    {g : Graph Row} (hg : Valid g) (e : Entry Row)
    (he : Columns.control cmp (g.getLast?.getD []) = some e)
    (initial : Nat → Label) (hInitial : ColumnRepresentation.Holds lt D R g initial) :
    ∀ n, ∃ f : Nat → Label,
      ColumnRepresentation.Holds lt D R (state cmp package g e n) f ∧
      ReflectionTransport.Bounded lt (width g e n) f (initial (g.length - 1)) ∧
      Facts R g e n f ∧ Templates R g e n f (initial (g.length - 1)) := by
  have hv := ExpansionValidity.control_valid cmp hg he
  have hx : g.length - 1 < g.length := by omega
  have hBeta := hInitial.domain (g.length - 1) hx
  intro n
  induction n with
  | zero =>
    refine ⟨initial, ?_, ?_, ?_, ?_⟩
    · simpa [state, ActualBlockGeometry.stage] using holds_take lt D R hInitial (g.length - 1)
    · intro i hi
      have hi' : i < g.length - 1 := by simpa [width] using hi
      exact hInitial.ordered i (g.length - 1) hi' hx
    · intro j hj a ha
      simpa [shift, move] using hInitial.relations j a ha
    · intro a ha
      rw [List.getLast?_eq_getElem?] at ha
      simpa [shift, move] using hInitial.relations (g.length - 1) a ha
  | succ n ih =>
    obtain ⟨f, hF, hBound, hFacts, hTemplates⟩ := ih
    obtain ⟨reflected, hRef, hFixed, hBelow, hNeeds⟩ :=
      reflect_actual_stage cmp package rowLt lt D R hWeak hLower hPackage laws reflection hg e he n f (initial (g.length - 1))
        hBeta hF hBound hTemplates
    have hControl := hTemplates e (ExpansionValidity.control_mem cmp he)
    rw [shift_cut] at hControl
    exact ⟨_, splice_actual_stage cmp package lt D R hTrans hWeak hg e hv.2 n f reflected _
      hF hRef hFixed hBelow hBound (hStrict hControl) hFacts hTemplates hNeeds⟩

/-- The entire actual fundamental-sequence output has a representation below
the old last label, for every index. Empty outputs cause no exceptional premise. -/
theorem fs_bounded
    (rowLt : Row → Row → Prop)
    (lt : Label → Label → Prop) (D : Label → Prop)
    (R : Row → Label → Label → Label → Prop)
    (hTrans : ∀ {a b c}, lt a b → lt b c → lt a c)
    (hStrict : ∀ {k index a b}, R k index a b → lt a b)
    (hWeak : ∀ {k small large p c}, lt small large → R k large p c → R k small p c)
    (hLower : ReflectionTransport.LowerRows rowLt lt R)
    (hPackage : ∀ high b low, low ∈ package high b → rowLt low high)
    (laws : ColumnRepresentation.RowCompareSound cmp rowLt)
    (reflection : ReflectionTransport.FiniteReflection rowLt lt D R)
    {g : Graph Row} (hg : Valid g) (hn : g ≠ [])
    (initial : Nat → Label) (hInitial : ColumnRepresentation.Holds lt D R g initial) (n : Nat) :
    ∃ f : Nat → Label,
      ColumnRepresentation.Holds lt D R (expand cmp package g n) f ∧
      ReflectionTransport.Bounded lt (expand cmp package g n).length f (initial (g.length - 1)) := by
  cases he : Columns.control cmp (g.getLast?.getD []) with
  | none =>
    have hfs : expand cmp package g n = g.take (g.length - 1) := by simp [expand, he]
    rw [hfs]
    refine ⟨initial, holds_take lt D R hInitial _, ?_⟩
    intro i hi
    have hpos : 0 < g.length := by cases g <;> simp_all
    have hi' : i < g.length - 1 := by
      simpa only [List.length_take, Nat.min_eq_left (Nat.sub_le g.length 1)] using hi
    exact hInitial.ordered i (g.length - 1) hi' (by omega)
  | some e =>
    obtain ⟨f, hF, hBound, _, _⟩ := all_stages cmp package rowLt lt D R hTrans hStrict hWeak hLower hPackage laws reflection
      hg e he initial hInitial n
    have hfs : expand cmp package g n = state cmp package g e n := ActualBlockGeometry.expand_eq_stage _ _ _ he n
    rw [hfs]
    exact ⟨f, hF, by rwa [state_length]⟩

#check fs_bounded
#print axioms needs_hold
#print axioms reflect_actual_stage
#print axioms splice_actual_stage
#print axioms all_stages
#print axioms fs_bounded

end OrdinalFormal.GeneratedStagedReflection
