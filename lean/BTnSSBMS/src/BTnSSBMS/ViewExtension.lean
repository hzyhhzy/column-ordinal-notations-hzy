import BTnSSBMS.NumericalTransport

/-!
Preserving numerical views when source edges are stretched through target
paths. The one-head encoder case is instantiated with actual emitted values
and actual recomputed BMS parent tables below. Forest restoration is not
assumed to follow from this one-head lemma.
-/
namespace BTnSSBMS.Parents

theorem point_append_old (visible : List Nat) (position value : Nat) (inside : position < visible.length) :
    point (visible ++ [value]) position = point visible position := by
  simp only [point, List.getElem?_append_left inside]

theorem point_append_last (visible : List Nat) (value : Nat) :
    point (visible ++ [value]) visible.length = value := by
  simp only [point, List.getElem?_concat_length, Option.getD_some]

/-- One source vertex may be represented by the end of a finite target
path; no direct-edge requirement is imposed on its final representative. -/
theorem NumericalView.append_stretched {d : Nat} {source target next : ParentContext}
    {visible : List Nat} (view : NumericalView d source target visible)
    (a : ParentLabel) (valid : ContextValid (source ++ [a]))
    (extended : target <+: next) (position : Nat) (inside : position < next.length)
    (frontier : position + 1 = next.length)
    (fresh : target.length ≤ position)
    (edges : ∀ row, row < d → ∀ p, a.parents[row]?.join = some p →
      Ancestor next row (point visible p) position) :
    NumericalView d (source ++ [a]) next (visible ++ [position]) := by
  refine ⟨by simp only [List.length_append, List.length_cons, List.length_nil, view.length], ?_, ?_, ?_, ?_⟩
  · intro p bound
    by_cases old : p < source.length
    · rw [point_append_old visible p position (by rw [view.length]; exact old)]
      have oldBound := view.bounded p old
      have longer := extended.length_le
      omega
    · have same : p = source.length := by simp only [List.length_append, List.length_cons, List.length_nil] at bound; omega
      subst p
      rw [← view.length, point_append_last]
      exact inside
  · intro row room p q pBound qBound path
    induction path with
    | refl => exact .refl _
    | @up middle endpoint edge previous ih =>
      have earlier := parent_earlier valid edge
      have middleBound : middle < source.length := by
        simp only [List.length_append, List.length_cons, List.length_nil] at qBound
        omega
      have toMiddle := ih (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      apply toMiddle.trans
      rw [point_append_old visible middle position (by rw [view.length]; exact middleBound)]
      by_cases old : endpoint < source.length
      · rw [point_append_old visible endpoint position (by rw [view.length]; exact old)]
        have original : parent source row endpoint = some middle :=
          (parent_prefix_eq (List.prefix_append _ _) row endpoint old).trans edge
        exact (view.lift row room middle endpoint middleBound old (.up original (.refl _))).prefix extended
      · have atEnd : endpoint = source.length := by
          simp only [List.length_append, List.length_cons, List.length_nil] at qBound
          omega
        subst endpoint
        have selected : a.parents[row]?.join = some middle := by
          simpa only [parent, List.getElem?_concat_length, Option.bind_some] using edge
        rw [← view.length, point_append_last]
        exact edges row room middle selected
  · intro _
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_sub_cancel,
      ← view.length, point_append_last, frontier]
  · intro p q earlier qBound
    have pBound : p < source.length := by
      simp only [List.length_append, List.length_cons, List.length_nil] at qBound
      omega
    rw [point_append_old visible p position (by rw [view.length]; exact pBound)]
    by_cases old : q < source.length
    · rw [point_append_old visible q position (by rw [view.length]; exact old)]
      exact view.increasing p q earlier old
    · have same : q = source.length := by
        simp only [List.length_append, List.length_cons, List.length_nil] at qBound
        omega
      subst q
      rw [← view.length, point_append_last]
      have bounded := view.bounded p pBound
      omega

theorem NumericalView.append {d : Nat} {source target : ParentContext} {visible : List Nat}
    (view : NumericalView d source target visible) (a b : ParentLabel)
    (valid : ContextValid (source ++ [a]))
    (parents : ∀ row, row < d → b.parents[row]?.join = (a.parents[row]?.join).map (point visible)) :
    NumericalView d (source ++ [a]) (target ++ [b]) (visible ++ [target.length]) := by
  apply view.append_stretched a valid (List.prefix_append _ _) target.length
    (by simp) (by simp) (Nat.le_refl _)
  intro row room p selected
  apply Ancestor.up ?_ (.refl _)
  simp only [parent, List.getElem?_concat_length, Option.bind_some, parents row room,
    selected, Option.map_some]

end BTnSSBMS.Parents

namespace BTnSSBMS.BMS

theorem parentTableAux_append (d : Nat) (context : ParentContext) (left right : Matrix) :
    parentTableAux d context (left ++ right) = parentTableAux d (parentTableAux d context left) right := by
  induction left generalizing context with
  | nil => rfl
  | cons a left ih => simpa only [List.cons_append, parentTableAux] using ih (context ++ [Parents.label d context a])

theorem parentTable_append (d : Nat) (left right : Matrix) :
    parentTable d (left ++ right) = parentTableAux d (parentTable d left) right :=
  parentTableAux_append d [] left right

theorem parentTable_snoc (d : Nat) (m : Matrix) (col : List Nat) :
    parentTable d (m ++ [col]) = parentTable d m ++ [Parents.label d (parentTable d m) col] := by
  rw [parentTable_append]
  rfl

end BTnSSBMS.BMS

namespace BTnSSBMS.Encoder

theorem matrix_emit (state : State d) (u : Nat → Nat) (height tag : Nat) (frame : List Binding) :
    matrix (emit state u height tag frame) = matrix state ++ [row d u height tag] := by
  simp only [matrix, emit, List.map_append, List.map_cons, List.map_nil]

/-- Numerical views are actually preserved by emitting a represented
source head. This applies to the reused-P case and the fresh-D entry. -/
theorem emit_numerical_view {d : Nat} {source : ParentContext} {visible : List Nat}
    (state : State d) (sourceCoherent : Parents.Coherent d source)
    (sourceValid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (coordinates : List Nat) (height tag : Nat) (frame : List Binding) :
    Parents.NumericalView d (source ++ [Parents.label d source coordinates])
      (BMS.parentTable (d + 2) (matrix
        (emit state (vector state visible (Parents.label d source coordinates)) height tag frame)))
      (visible ++ [state.length]) := by
  rw [matrix_emit, BMS.parentTable_snoc]
  have length : (BMS.parentTable (d + 2) (matrix state)).length = state.length := by
    simp only [BMS.parentTable_length, matrix, List.length_map]
  rw [← length]
  apply view.append _ _ (Parents.context_valid_append_label d source sourceValid coordinates)
  intro row room
  rw [emitted_head_numerical_parents state sourceCoherent sourceValid view coordinates height tag row room,
    representative_eq_point view]

end BTnSSBMS.Encoder
