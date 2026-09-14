import OrdinalFormal.Columns
import OrdinalFormal.ReflectionTransport

/-!
# Executable columns to finite semantic diagrams

This module connects the data representations, not the still-uninstantiated
truth/reflection semantics. In particular no concrete well-ordering theorem
is postulated. Normalization is proved semantically sound even without laws
for the comparison function: sorting and deduplication only remove/reorder
entries, while inserted roots are weaker than an existing root.
-/

namespace OrdinalFormal.ColumnRepresentation

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

universe u v


variable {Row : Type u} {Label : Type v}

def entryAtom (child : Nat) (e : Columns.Entry Row) : ReflectionTransport.Atom Row :=
  ⟨e.row, e.root, e.parent, child⟩

def atoms (g : Columns.Graph Row) : List (ReflectionTransport.Atom Row) :=
  (List.range g.length).flatMap fun j =>
    (g[j]?.getD []).map (entryAtom j)

theorem mem_atoms_iff (g : Columns.Graph Row) (a : ReflectionTransport.Atom Row) :
    a ∈ atoms g ↔ ∃ j, j < g.length ∧ ∃ e,
      e ∈ g[j]?.getD [] ∧ entryAtom j e = a := by
  simp [atoms, List.mem_flatMap, List.mem_map]

theorem index_lt_of_entry_mem {g : Columns.Graph Row} {j : Nat} {e : Columns.Entry Row}
    (h : e ∈ g[j]?.getD []) : j < g.length := by
  by_cases hj : j < g.length
  · exact hj
  have hn : ¬ j < g.length := hj
  have hNone : g[j]? = none := by
    apply List.getElem?_eq_none_iff.mpr
    omega
  simp [hNone] at h

def toDiagram (g : Columns.Graph Row) (hg : Columns.Valid g) : ReflectionTransport.Diagram Row where
  size := g.length
  atoms := atoms g
  valid := by
    intro a ha
    obtain ⟨j, hj, e, he, rfl⟩ := (mem_atoms_iff g a).mp ha
    exact ⟨(hg j e he).1, (hg j e he).2, hj⟩

@[simp] theorem toDiagram_size (g : Columns.Graph Row) (hg : Columns.Valid g) :
    (toDiagram g hg).size = g.length := rfl

@[simp] theorem toDiagram_atoms (g : Columns.Graph Row) (hg : Columns.Valid g) :
    (toDiagram g hg).atoms = atoms g := rfl

/-- The same representation assertion directly on the executable column list. -/
structure Holds (lt : Label → Label → Prop) (D : Label → Prop)
    (R : Row → Label → Label → Label → Prop)
    (g : Columns.Graph Row) (f : Nat → Label) : Prop where
  domain : ∀ i, i < g.length → D (f i)
  ordered : ∀ i j, i < j → j < g.length → lt (f i) (f j)
  relations : ∀ j e, e ∈ g[j]?.getD [] →
    R e.row (f e.root) (f e.parent) (f j)

theorem holds_iff_representation
    (lt : Label → Label → Prop) (D : Label → Prop)
    (R : Row → Label → Label → Label → Prop)
    (g : Columns.Graph Row) (hg : Columns.Valid g) (f : Nat → Label) :
    Holds lt D R g f ↔ ReflectionTransport.Representation lt D R (toDiagram g hg) f := by
  constructor
  · intro h
    refine ⟨h.domain, h.ordered, ?_⟩
    intro a ha
    obtain ⟨j, _, e, he, rfl⟩ := (mem_atoms_iff g a).mp ha
    exact h.relations j e he
  · intro h
    refine ⟨h.domain, h.ordered, ?_⟩
    intro j e he
    have ha : entryAtom j e ∈ atoms g :=
      (mem_atoms_iff g _).mpr ⟨j, index_lt_of_entry_mem he, e, he, rfl⟩
    exact h.relations (entryAtom j e) ha

theorem mem_dedupSorted_subset (cmp : Row → Row → Ordering)
    {c : Columns.Column Row} {e : Columns.Entry Row} (h : e ∈ Columns.dedupSorted cmp c) : e ∈ c := by
  induction c with
  | nil => simp [Columns.dedupSorted] at h
  | cons a tail ih =>
      cases hr : Columns.dedupSorted cmp tail with
      | nil =>
          have heq : e = a := by simpa [Columns.dedupSorted, hr] using h
          subst e
          exact List.mem_cons_self
      | cons b rest =>
          simp only [Columns.dedupSorted, hr] at h
          split at h
          · exact List.mem_cons_of_mem a (ih (by simpa [hr] using h))
          · rcases List.mem_cons.mp h with heq | hm
            · exact List.mem_cons.mpr (Or.inl heq)
            · exact List.mem_cons_of_mem a (ih (by simpa [hr] using hm))

/-- Every normalized entry comes from a genuine input entry by lowering
only its root. No comparator correctness hypothesis is required for soundness. -/
theorem mem_insertDescending (cmp : Row → Row → Ordering)
    (a e : Columns.Entry Row) (c : Columns.Column Row) :
    a ∈ Columns.insertDescending cmp e c ↔ a = e ∨ a ∈ c := by
  induction c with
  | nil => simp [Columns.insertDescending]
  | cons b tail ih =>
      simp only [Columns.insertDescending]
      split
      · simp only [List.mem_cons]
      · simp only [List.mem_cons, ih]
        exact or_left_comm

theorem mem_sortDescending (cmp : Row → Row → Ordering)
    (e : Columns.Entry Row) (c : Columns.Column Row) :
    e ∈ Columns.sortDescending cmp c ↔ e ∈ c := by
  induction c with
  | nil => simp [Columns.sortDescending]
  | cons a tail ih => simp only [Columns.sortDescending, mem_insertDescending, ih,
      List.mem_cons]

theorem mem_normalizeColumn_source (cmp : Row → Row → Ordering)
    {c : Columns.Column Row} {e : Columns.Entry Row} (h : e ∈ Columns.normalizeColumn cmp c) :
    ∃ s ∈ c, e.row = s.row ∧ e.parent = s.parent ∧ e.root ≤ s.root := by
  have hSorted := mem_dedupSorted_subset cmp h
  have hFlat := (mem_sortDescending cmp e _).mp hSorted
  obtain ⟨s, hOriginal, hMap⟩ := List.mem_flatMap.mp hFlat
  obtain ⟨q, hRange, hEq⟩ := List.mem_map.mp hMap
  rw [← hEq]
  refine ⟨s, hOriginal, rfl, rfl, ?_⟩
  change q ≤ s.root
  have := List.mem_range.mp hRange
  omega

@[simp] theorem normalizeColumn_nil (cmp : Row → Row → Ordering) :
    Columns.normalizeColumn cmp ([] : Columns.Column Row) = [] := by
  simp [Columns.normalizeColumn, Columns.sortDescending, Columns.dedupSorted]

theorem normalize_lookup (cmp : Row → Row → Ordering) (g : Columns.Graph Row) (j : Nat) :
    (Columns.normalize cmp g)[j]?.getD [] = Columns.normalizeColumn cmp (g[j]?.getD []) := by
  simp only [Columns.normalize, List.getElem?_map]
  cases h : g[j]? <;> simp

theorem normalize_valid (cmp : Row → Row → Ordering)
    {g : Columns.Graph Row} (hg : Columns.Valid g) : Columns.Valid (Columns.normalize cmp g) := by
  intro j e he
  rw [normalize_lookup] at he
  obtain ⟨s, hs, _, hParent, hRoot⟩ := mem_normalizeColumn_source cmp he
  have hv := hg j s hs
  rw [hParent]
  exact ⟨Nat.le_trans hRoot hv.1, hv.2⟩

theorem normalize_rootWeakeningGeometry (cmp : Row → Row → Ordering)
    (g : Columns.Graph Row) (hg : Columns.Valid g) :
    ReflectionTransport.RootWeakeningGeometry (toDiagram g hg)
      (toDiagram (Columns.normalize cmp g) (normalize_valid cmp hg)) := by
  refine ⟨by simp [Columns.normalize], ?_⟩
  intro a ha
  obtain ⟨j, _, e, he, rfl⟩ := (mem_atoms_iff (Columns.normalize cmp g) a).mp ha
  rw [normalize_lookup] at he
  obtain ⟨s, hs, hRow, hParent, hRoot⟩ := mem_normalizeColumn_source cmp he
  refine ⟨entryAtom j s, ?_, hRow, hParent, rfl, hRoot⟩
  exact (mem_atoms_iff g _).mpr ⟨j, index_lt_of_entry_mem hs, s, hs, rfl⟩

theorem holds_normalize
    (lt : Label → Label → Prop) (D : Label → Prop)
    (R : Row → Label → Label → Label → Prop)
    (hWeak : ∀ {k small large p c}, lt small large →
      R k large p c → R k small p c)
    (cmp : Row → Row → Ordering) (g : Columns.Graph Row) (hg : Columns.Valid g)
    (f : Nat → Label) (h : Holds lt D R g f) :
    Holds lt D R (Columns.normalize cmp g) f := by
  apply (holds_iff_representation lt D R _ (normalize_valid cmp hg) f).mpr
  exact ReflectionTransport.representation_rootWeakening lt D R hWeak
    (normalize_rootWeakeningGeometry cmp g hg) f
    ((holds_iff_representation lt D R g hg f).mp h)

/-- The concrete closed-form shift at block b+1 is exactly the semantic
one-block movement applied to the coordinates at block b. -/
theorem move_succ (x cut b i : Nat) (hCut : cut ≤ x) :
    ReflectionTransport.moveColumn (x + b * (x - cut)) (cut + b * (x - cut))
      (Columns.move cut (x - cut) b i) = Columns.move cut (x - cut) (b + 1) i := by
  by_cases hi : i < cut
  · have hSmall : i < cut + b * (x - cut) := by omega
    simp [Columns.move, hi, ReflectionTransport.moveColumn, hSmall]
  · have hNot : ¬i + b * (x - cut) < cut + b * (x - cut) := by omega
    simp only [Columns.move, if_neg hi, ReflectionTransport.moveColumn, if_neg hNot, Nat.add_mul, Nat.one_mul]
    omega

theorem moveEntry_atom_succ (x cut b j : Nat) (hCut : cut ≤ x) (e : Columns.Entry Row) :
    ReflectionTransport.moveAtom (x + b * (x - cut)) (cut + b * (x - cut))
      (entryAtom (Columns.move cut (x - cut) b j) (Columns.moveEntry cut (x - cut) b e)) =
    entryAtom (Columns.move cut (x - cut) (b + 1) j)
      (Columns.moveEntry cut (x - cut) (b + 1) e) := by
  simp only [ReflectionTransport.moveAtom, entryAtom, Columns.moveEntry]
  rw [move_succ x cut b e.root hCut, move_succ x cut b e.parent hCut,
    move_succ x cut b j hCut]

@[simp] theorem block_length (cmp : Row → Row → Ordering) (package : Columns.Package Row)
    (g : Columns.Graph Row) (e : Columns.Entry Row) (b : Nat) :
    (Columns.block cmp package g e b).length = g.length - 1 - e.parent := by
  simp [Columns.block]

/-- Exactly the comparator soundness needed to decode a generated ordinary
seam. This must be proved on the relevant row domain, not assumed for arbitrary
noncanonical LRD row encodings. -/
structure RowCompareSound (cmp : Row → Row → Ordering)
    (rowLt : Row → Row → Prop) : Prop where
  eq_sound : ∀ {a b}, cmp a b = .eq → a = b
  lt_sound : ∀ {a b}, cmp a b = .lt → rowLt a b

theorem natRowCompareSound : RowCompareSound (compare : Nat → Nat → Ordering) Nat.lt :=
  ⟨Nat.compare_eq_eq.mp, Nat.compare_eq_lt.mp⟩

theorem ordinarySeam_guard (cmp : Row → Row → Ordering)
    (rowLt : Row → Row → Prop) (laws : RowCompareSound cmp rowLt)
    (last : Columns.Column Row) (e : Columns.Entry Row) (len b : Nat)
    {d : Columns.Entry Row} (hd : d ∈ Columns.ordinarySeam cmp last e len b) :
    rowLt d.row e.row ∨
      (d.row = e.row ∧ d.root < Columns.move e.parent len b e.root) := by
  obtain ⟨s, _, hMap⟩ := List.mem_flatMap.mp hd
  obtain ⟨q, hFilter, rfl⟩ := List.mem_map.mp hMap
  have hGuard := (List.mem_filter.mp hFilter).2
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hGuard
  rcases hGuard with hLow | ⟨hEq, hRoot⟩
  · exact Or.inl (laws.lt_sound hLow)
  · exact Or.inr ⟨laws.eq_sound hEq, hRoot⟩

theorem ordinarySeam_nat_guard (last : Columns.Column Nat)
    (e : Columns.Entry Nat) (len b : Nat) {d : Columns.Entry Nat}
    (hd : d ∈ Columns.ordinarySeam compare last e len b) :
    d.row < e.row ∨
      (d.row = e.row ∧ d.root < Columns.move e.parent len b e.root) :=
  ordinarySeam_guard compare Nat.lt natRowCompareSound last e len b hd

#print axioms holds_iff_representation
#print axioms normalize_valid
#print axioms holds_normalize
#print axioms moveEntry_atom_succ
#print axioms ordinarySeam_nat_guard

end OrdinalFormal.ColumnRepresentation
