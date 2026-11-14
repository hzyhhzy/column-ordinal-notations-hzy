import BTnSSBMS.RowGeometry
import BTnSSBMS.Encoder

/-!
Numerical parent transport across a finite ancestry-preserving view. This
is a local transport theorem for the actual search, not an assumption that
the full recursive encoder preserves the view. Its preservation across
forest entry/exit remains a separate obligation.
-/
namespace BTnSSBMS.Parents

theorem label_zero (d : Nat) (context : ParentContext) (coordinates : List Nat)
    (positive : 0 < d) :
    (label d context coordinates).parents[0]?.join =
      search context 0 (coordinates[0]?.getD 0) context.length := by
  cases d with
  | zero => omega
  | succ d => simp only [label, rows, List.getElem?_cons_zero, Option.join_some]

theorem label_parent_bound (d : Nat) (context : ParentContext) (coordinates : List Nat)
    (row p : Nat) (found : (label d context coordinates).parents[row]?.join = some p) :
    p < context.length := by
  obtain ⟨cursor, hit⟩ := rows_found context coordinates 0 d context.length row p found
  exact (search_bounds context row (coordinates[row]?.getD 0) cursor p
    (by simpa only [Nat.zero_add] using hit)).2

def point (visible : List Nat) (position : Nat) : Nat := visible[position]?.getD 0

/-- The numerical part of a scoped source-to-target entering state.
Every listed item is finite; no standardness or ordinal rank is hidden. -/
structure NumericalView (d : Nat) (source target : ParentContext) (visible : List Nat) : Prop where
  length : visible.length = source.length
  bounded : ∀ p, p < source.length → point visible p < target.length
  lift : ∀ row, row < d → ∀ p q, p < source.length → q < source.length →
    Ancestor source row p q → Ancestor target row (point visible p) (point visible q)
  frontier : source ≠ [] → point visible (source.length - 1) + 1 = target.length
  increasing : ∀ p q, p < q → q < source.length → point visible p < point visible q

def representedValue (target : ParentContext) (visible : List Nat) (a : ParentLabel) (row : Nat) : Nat :=
  ((a.parents[row]?.join).map fun p => reading target row (point visible p) + 1).getD 0

/-- Matching represented numerical values is sufficient: the actual
target search computes exactly the represented source parents. -/
theorem label_parent_transport {d rows : Nat} {source target : ParentContext} {visible : List Nat}
    (sourceCoherent : Coherent d source) (sourceValid : ContextValid source)
    (targetCoherent : Coherent rows target) (targetValid : ContextValid target)
    (room : d ≤ rows) (view : NumericalView d source target visible)
    (coordinates targetCoordinates : List Nat)
    (values : ∀ row, row < d → targetCoordinates[row]?.getD 0 =
      representedValue target visible (label d source coordinates) row)
    (row : Nat) (inside : row < d) :
    (label rows target targetCoordinates).parents[row]?.join =
      ((label d source coordinates).parents[row]?.join).map (point visible) := by
  induction row with
  | zero =>
    rw [label_zero rows target targetCoordinates (by omega), values 0 inside]
    cases selected : (label d source coordinates).parents[0]?.join with
    | none => simp only [representedValue, selected, Option.map_none, Option.getD_none, search_zero]
    | some root =>
      have rootBound := label_parent_bound d source coordinates 0 root selected
      have frontierBound : source.length - 1 < source.length := by omega
      have sourceNonempty : source ≠ [] := by intro empty; simp [empty] at rootBound
      have path := label_zero_parent_frontier sourceCoherent sourceValid (by omega) coordinates selected
      have targetPath := view.lift 0 inside root (source.length - 1) rootBound frontierBound path
      have result := search_ancestor_successor targetCoherent targetValid (by omega : 0 < rows)
        (view.bounded _ frontierBound) targetPath
      rw [view.frontier sourceNonempty] at result
      simpa only [representedValue, selected, Option.map_some, Option.getD_some] using result
  | succ row ih =>
    rw [label_next rows target targetCoordinates row (by omega), values (row + 1) inside]
    cases selected : (label d source coordinates).parents[row + 1]?.join with
    | none => simp only [representedValue, selected, Option.map_none, Option.getD_none, search_zero]
    | some root =>
      obtain ⟨previous, lower, ancestry⟩ :=
        label_higher_parent_frontier sourceCoherent sourceValid coordinates inside selected
      have rootBound := label_parent_bound d source coordinates (row + 1) root selected
      have previousBound := label_parent_bound d source coordinates row previous lower
      have targetPath := view.lift (row + 1) inside root previous rootBound previousBound ancestry
      have result := search_ancestor_successor targetCoherent targetValid (by omega : row + 1 < rows)
        (view.bounded _ previousBound) targetPath
      rw [ih (by omega), lower]
      simpa only [representedValue, selected, Option.map_some, Option.getD_some] using result

theorem empty_numerical_view (d : Nat) : NumericalView d [] [] [] := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · intro p impossible; simp at impossible
  · intro row room p q impossible; simp at impossible
  · intro impossible; exact False.elim (impossible rfl)
  · intro p q earlier impossible; simp at impossible

end BTnSSBMS.Parents

namespace BTnSSBMS.Encoder

theorem matrix_lookup (state : State d) (position : Nat) :
    (matrix state)[position]? = (state[position]?).map Column.values := by
  simp only [matrix, List.getElem?_map]

theorem row_numerical_reading (d : Nat) (u : Nat → Nat) (height tag j : Nat) (inside : j < d) :
    (row d u height tag)[j]?.getD 0 = u j := by
  have bound : j < ((List.range d).map u).length := by simpa using inside
  simp only [row, List.getElem?_append_left bound, List.getElem?_map,
    List.getElem?_range, inside, Option.map_some, Option.getD_some]

theorem representative_eq_point {d : Nat} {source target : ParentContext} {visible : List Nat}
    (view : Parents.NumericalView d source target visible) (coordinates : List Nat) (row : Nat) :
    representative visible (Parents.label d source coordinates) row =
      ((Parents.label d source coordinates).parents[row]?.join).map (Parents.point visible) := by
  cases selected : (Parents.label d source coordinates).parents[row]?.join with
  | none => simp only [representative, selected, Option.bind_none, Option.map_none]
  | some p =>
    have sourceBound := Parents.label_parent_bound d source coordinates row p selected
    have bound : p < visible.length := by rw [view.length]; exact sourceBound
    simp only [representative, selected, Option.bind_some, Option.map_some,
      Parents.point, List.getElem?_eq_getElem bound, Option.getD_some]

theorem vector_eq_represented {d : Nat} {source : ParentContext} {visible : List Nat} {state : State d}
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (coordinates : List Nat) (row : Nat) :
    vector state visible (Parents.label d source coordinates) row =
      Parents.representedValue (BMS.parentTable (d + 2) (matrix state)) visible
        (Parents.label d source coordinates) row := by
  rw [vector, representative_eq_point view]
  cases selected : (Parents.label d source coordinates).parents[row]?.join with
  | none => simp only [selected, Option.map_none, Option.bind_none, Parents.representedValue, Option.getD_none]
  | some p =>
    have sourceBound := Parents.label_parent_bound d source coordinates row p selected
    have bound : Parents.point visible p < state.length := by
      have bound := view.bounded p sourceBound
      simpa only [BMS.parentTable_length, matrix, List.length_map] using bound
    simp only [selected, Option.map_some, Option.bind_some, List.getElem?_eq_getElem bound,
      Parents.representedValue, Option.getD_some, BMS.parentTable_reading,
      matrix_lookup]

/-- The first d parents of an actual emitted head are correct whenever
the scoped entering state realizes the numerical view. Frame heights and
tags do not need to satisfy any separate condition for these lower rows. -/
theorem emitted_head_numerical_parents {d : Nat} {source : ParentContext} {visible : List Nat}
    (state : State d) (sourceCoherent : Parents.Coherent d source)
    (sourceValid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (coordinates : List Nat) (height tag row : Nat) (inside : row < d) :
    (Parents.label (d + 2) (BMS.parentTable (d + 2) (matrix state))
      (Encoder.row d (vector state visible (Parents.label d source coordinates)) height tag)).parents[row]?.join =
      representative visible (Parents.label d source coordinates) row := by
  rw [representative_eq_point view]
  apply Parents.label_parent_transport sourceCoherent sourceValid
    (BMS.parentTable_coherent (d + 2) (matrix state)) (BMS.parentTable_valid (d + 2) (matrix state))
    (by omega) view coordinates _ _ row inside
  intro j room
  rw [row_numerical_reading d _ height tag j room, vector_eq_represented view]

end BTnSSBMS.Encoder
