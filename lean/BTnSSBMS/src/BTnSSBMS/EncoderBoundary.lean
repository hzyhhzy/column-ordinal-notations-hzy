import BTnSSBMS.EncoderHeadOrder

/-!
Actual row-zero fences for lexicographic exits. A forest may finish before
the other forest, but its next slot or closing column must remain below
the first still-internal column. These results use computed parent search
and the maintained numerical view, not a presumed output order theorem.
-/
namespace BTnSSBMS.Parents

theorem label_above_fence {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context)
    (positive : 0 < d) {root : Nat} (inside : root < context.length)
    (fence : Ancestor context 0 root (context.length - 1))
    (a : List Nat) (above : reading context 0 root < a[0]?.getD 0) :
    ∃ p, (label d context a).parents[0]?.join = some p ∧
      Ancestor context 0 root p := by
  obtain ⟨p, after, found⟩ := search_zero_exists_above context (a[0]?.getD 0)
    context.length root (Nat.le_refl _) inside above
  have selected : (label d context a).parents[0]?.join = some p := by
    rw [label_zero d context a positive]
    exact found
  exact ⟨p, selected, fence.between valid
    (label_zero_parent_frontier coherent valid positive a selected) after⟩

theorem fence_append_label {d : Nat} {context : ParentContext}
    (coherent : Coherent d context) (valid : ContextValid context)
    (positive : 0 < d) {root : Nat} (inside : root < context.length)
    (fence : Ancestor context 0 root (context.length - 1))
    (a : List Nat) (above : reading context 0 root < a[0]?.getD 0) :
    Ancestor (context ++ [label d context a]) 0 root context.length := by
  obtain ⟨p, selected, path⟩ := label_above_fence coherent valid positive inside fence a above
  exact .up ((append_label_parent d context a 0).trans selected)
    (path.prefix (List.prefix_append _ _))

end BTnSSBMS.Parents

namespace BTnSSBMS.Encoder

theorem vector_above_fence {d : Nat} {source : ParentContext} {visible : List Nat}
    (state : State d) (positive : 0 < d)
    (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    {root : Nat} (inside : root < source.length)
    (fence : Parents.Ancestor source 0 root (source.length - 1))
    (a : List Nat) (above : Parents.reading source 0 root < a[0]?.getD 0) :
    Parents.reading (BMS.parentTable (d + 2) (matrix state)) 0 (Parents.point visible root) <
      vector state visible (Parents.label d source a) 0 := by
  obtain ⟨p, selected, path⟩ := Parents.label_above_fence coherent valid positive inside fence a above
  have pBound := Parents.label_parent_bound d source a 0 p selected
  have lifted := view.lift 0 positive root p inside pBound path
  have lower := lifted.reading_le (BMS.parentTable_coherent (d + 2) (matrix state))
  rw [vector_eq_represented view, Parents.representedValue, selected]
  simp only [Option.map_some, Option.getD_some]
  omega

/-- The first actual output after an unfinished forest stays strictly
above its owner's represented height, regardless of its complete key. -/
theorem encode_cons_above_fence {d : Nat} {source : ParentContext} {visible : List Nat}
    (state : State d) (positive : 0 < d)
    (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    {root : Nat} (inside : root < source.length)
    (fence : Parents.Ancestor source 0 root (source.length - 1))
    (a : List Nat) (hs : Forests (List Nat)) (tail : NumericalExpr)
    (above : Parents.reading source 0 root < a[0]?.getD 0) :
    ∃ head rest,
      matrix (encode d (Parents.annotate d source (.cons a hs tail)) visible state) =
        matrix state ++ head :: rest ∧
      Parents.reading (BMS.parentTable (d + 2) (matrix state)) 0 (Parents.point visible root) <
        head[0]?.getD 0 := by
  obtain ⟨height, tag, rest, _, shape⟩ := encode_cons_first_row d (Parents.label d source a)
    (Parents.annotateForests d (source ++ [Parents.label d source a]) hs)
    (Parents.annotate d (source ++ [Parents.label d source a]) tail) visible state
  refine ⟨row d (vector state visible (Parents.label d source a)) height tag, rest, shape, ?_⟩
  rw [row_numerical_reading d _ height tag 0 positive]
  exact vector_above_fence state positive coherent valid view inside fence a above

end BTnSSBMS.Encoder

namespace BTnSSBMS

/-- A strict decision made at real columns, rather than merely by one
matrix ending. It survives arbitrary material appended on either side. -/
def MatrixFirstLt (left right : Matrix) : Prop :=
  ∃ stem a b xs ys,
    left = stem ++ a :: xs ∧ right = stem ++ b :: ys ∧
      listCompare Ord.compare a b = .lt

theorem MatrixFirstLt.compare {left right : Matrix} (strict : MatrixFirstLt left right) :
    matrixCompare left right = .lt := by
  obtain ⟨stem, a, b, xs, ys, rfl, rfl, first⟩ := strict
  simp only [matrixCompare, listCompare_common_prefix (listCompare Ord.compare) columnCompare_self,
    listCompare, first]

theorem MatrixFirstLt.append {left right : Matrix} (strict : MatrixFirstLt left right)
    (xs ys : Matrix) : MatrixFirstLt (left ++ xs) (right ++ ys) := by
  obtain ⟨stem, a, b, leftTail, rightTail, rfl, rfl, first⟩ := strict
  exact ⟨stem, a, b, leftTail ++ xs, rightTail ++ ys,
    by simp only [List.append_assoc, List.cons_append],
    by simp only [List.append_assoc, List.cons_append], first⟩

theorem MatrixFirstLt.prepend {left right : Matrix} (strict : MatrixFirstLt left right)
    (stem : Matrix) : MatrixFirstLt (stem ++ left) (stem ++ right) := by
  obtain ⟨common, a, b, xs, ys, rfl, rfl, first⟩ := strict
  exact ⟨stem ++ common, a, b, xs, ys,
    by simp only [List.append_assoc], by simp only [List.append_assoc], first⟩

theorem columnCompare_lt_of_zero {a b : List Nat} (widthA : 0 < a.length)
    (widthB : 0 < b.length) (strict : a[0]?.getD 0 < b[0]?.getD 0) :
    listCompare Ord.compare a b = .lt :=
  columnCompare_lt_at a b 0 widthA widthB (by intro i room; omega) strict

end BTnSSBMS
