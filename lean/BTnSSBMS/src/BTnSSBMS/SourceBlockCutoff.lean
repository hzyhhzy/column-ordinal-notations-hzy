import BTnSSBMS.SourceBlocks
import BTnSSBMS.EntryBlockClosure

/-!
The first source column outside a zero-block also exits the encoded
zero-block. The bound is obtained from actual parent search and the
numerical view; it is not an assumed inverse-ancestry property.
-/
namespace BTnSSBMS.Encoder

def sourceRootValue (source : ParentContext) (visible : List Nat) (state : State d) (root : Nat) : Nat :=
  ((Parents.parent source 0 root).map fun p =>
    Parents.reading (BMS.parentTable (d + 2) (matrix state)) 0 (Parents.point visible p) + 1).getD 0

theorem vector_le_sourceRootValue {d : Nat} {source : ParentContext} {visible : List Nat}
    (state : State d) (positive : 0 < d) (coherent : Parents.Coherent d source)
    (valid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    {root : Nat} (inside : root < source.length)
    (fence : Parents.Ancestor source 0 root (source.length - 1))
    (a : List Nat) (low : a[0]?.getD 0 ≤ Parents.reading source 0 root) :
    vector state visible (Parents.label d source a) 0 ≤ sourceRootValue source visible state root := by
  rw [vector_eq_represented view, Parents.representedValue]
  cases selected : (Parents.label d source a).parents[0]?.join with
  | none => simp only [Option.map_none, Option.getD_none, Nat.zero_le]
  | some q =>
    have qBound := Parents.label_parent_bound d source a 0 q selected
    have qPath := Parents.label_zero_parent_frontier coherent valid positive a selected
    have qLower : Parents.reading source 0 q < a[0]?.getD 0 := by
      obtain ⟨label, lookup, less⟩ := Parents.search_smaller source 0 (a[0]?.getD 0) source.length q
        ((Parents.label_zero d source a positive).symm.trans selected)
      simpa only [Parents.reading, lookup, Option.getD_some] using less
    have qToRoot : Parents.Ancestor source 0 q root := by
      rcases qPath.comparable fence with forward | backward
      · exact forward
      · have impossible := backward.reading_le coherent
        omega
    have different : q ≠ root := by intro same; subst q; omega
    obtain ⟨p, rootParent, qToParent⟩ := (Parents.Ancestor.iff_parent different).mp qToRoot
    have pBound : p < source.length := by
      have earlier := Parents.parent_earlier valid rootParent
      omega
    have lifted := view.lift 0 positive q p qBound pBound qToParent
    have value := lifted.reading_le (BMS.parentTable_coherent (d + 2) (matrix state))
    simp only [sourceRootValue, rootParent, Option.map_some, Option.getD_some]
    omega

theorem sourceRootValue_extends {d : Nat} {source target : ParentContext} {visible positions : List Nat}
    {state next : State d} {root : Nat} (sourcePrefix : source <+: target)
    (visiblePrefix : visible <+: positions) (statePrefix : state <+: next)
    (valid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (inside : root < source.length) :
    sourceRootValue source visible state root = sourceRootValue target positions next root := by
  simp only [sourceRootValue]
  rw [← Parents.parent_prefix_eq sourcePrefix 0 root inside]
  cases selected : Parents.parent source 0 root with
  | none => rfl
  | some p =>
    have pBound : p < source.length := by
      have earlier := Parents.parent_earlier valid selected
      omega
    simp only [Option.map_some, Option.getD_some]
    rw [← Parents.point_prefix visiblePrefix p (by rw [view.length]; exact pBound),
      ← Parents.reading_prefix (table_prefix statePrefix) 0 (Parents.point visible p) (view.bounded p pBound)]

/-- Stop at the source zero-block boundary for any represented root
at least as high as the source root's reconstructed first output. -/
theorem encode_takeAbove_block_of_le (d : Nat) (e : NumericalExpr) (floor : Nat)
    (source : ParentContext) (visible : List Nat) (state : State d) (root targetRoot : Nat)
    (positive : 0 < d) (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (separated : Source.ForestSeparated e) (rootInside : root < source.length)
    (targetInside : targetRoot < state.length)
    (sourceValue : Parents.reading source 0 root = floor)
    (fence : Parents.Ancestor source 0 root (source.length - 1))
    (targetValue : sourceRootValue source visible state root ≤
      Parents.reading (BMS.parentTable (d + 2) (matrix state)) 0 targetRoot) :
    BMS.block (matrix (encode d (Parents.annotate d source e) visible state)) targetRoot =
      BMS.block (matrix (encode d (Parents.annotate d source (Source.takeAbove floor e)) visible state))
        targetRoot := by
  cases e with
  | nil => rfl
  | cons a hs tail =>
    let headed := headState d (Parents.label d source a)
      (Parents.annotateForests d (source ++ [Parents.label d source a]) hs) visible state
    have statePrefix : state <+: headed := encode_extends ..
    have nextView := headState_view state positive coherent valid view a hs separated.1
    by_cases high : floor < a[0]?.getD 0
    · simp only [Source.takeAbove, high, ↓reduceIte, Parents.annotate, encode_split_head]
      apply encode_takeAbove_block_of_le d tail floor (source ++ [Parents.label d source a])
        (visible ++ [headed.length - 1]) headed root targetRoot positive
        (Parents.coherent_append_label coherent a) (Parents.context_valid_append_label d source valid a)
        nextView separated.2
      · simp only [List.length_append, List.length_cons, List.length_nil]; omega
      · have longer := statePrefix.length_le; omega
      · rw [← Parents.reading_prefix (List.prefix_append _ _) 0 root rootInside]; exact sourceValue
      · simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_sub_cancel]
        exact Parents.fence_append_label coherent valid positive rootInside fence a (by rwa [sourceValue])
      · rw [← Parents.reading_prefix (table_prefix statePrefix) 0 targetRoot (by rwa [table_length]),
          ← sourceRootValue_extends (List.prefix_append _ _) (List.prefix_append _ _)
            statePrefix valid view rootInside]
        exact targetValue
    · simp only [Source.takeAbove, high, ↓reduceIte, Parents.annotate, encode]
      obtain ⟨height, tag, rest, _, shape⟩ := encode_cons_first_row d (Parents.label d source a)
        (Parents.annotateForests d (source ++ [Parents.label d source a]) hs)
        (Parents.annotate d (source ++ [Parents.label d source a]) tail) visible state
      change BMS.block (matrix (encode d (.cons (Parents.label d source a)
        (Parents.annotateForests d (source ++ [Parents.label d source a]) hs) _) visible state)) targetRoot = _
      rw [shape]
      apply BMS.block_append_of_exit (matrix state) _ targetRoot
        (by simpa only [matrix, List.length_map] using targetInside)
      intro col remaining same
      cases same
      rw [row_numerical_reading d _ height tag 0 positive]
      have low := vector_le_sourceRootValue state positive coherent valid view rootInside fence a
        (by rw [sourceValue]; omega)
      simpa only [BMS.parentTable_reading] using Nat.le_trans low targetValue

/-- The first-output specialization, retaining the original exact-value
interface used by the ordinary-row block transport. -/
theorem encode_takeAbove_block (d : Nat) (e : NumericalExpr) (floor : Nat)
    (source : ParentContext) (visible : List Nat) (state : State d) (root targetRoot : Nat)
    (positive : 0 < d) (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (separated : Source.ForestSeparated e) (rootInside : root < source.length)
    (targetInside : targetRoot < state.length)
    (sourceValue : Parents.reading source 0 root = floor)
    (fence : Parents.Ancestor source 0 root (source.length - 1))
    (targetValue : Parents.reading (BMS.parentTable (d + 2) (matrix state)) 0 targetRoot =
      sourceRootValue source visible state root) :
    BMS.block (matrix (encode d (Parents.annotate d source e) visible state)) targetRoot =
      BMS.block (matrix (encode d (Parents.annotate d source (Source.takeAbove floor e)) visible state))
        targetRoot :=
  encode_takeAbove_block_of_le d e floor source visible state root targetRoot positive coherent valid view
    separated rootInside targetInside sourceValue fence (Nat.le_of_eq targetValue.symm)

end BTnSSBMS.Encoder
