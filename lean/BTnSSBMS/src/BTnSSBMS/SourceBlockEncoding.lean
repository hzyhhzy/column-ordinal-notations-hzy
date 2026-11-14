import BTnSSBMS.SourceBlockCutoff
import BTnSSBMS.CompleteBlockTransport

/-!
Encoding a complete source zero-block gives exactly the complete target
zero-block, with the unchanged entering state removed. Attachments are
encoded in full, even when they contain arbitrarily nested forests.
-/
namespace BTnSSBMS.BMS

theorem block_eq_drop_of_frontier (rows : Nat) (m : Matrix) (root : Nat)
    (positive : 0 < rows) (inside : root < m.length)
    (fence : Parents.Ancestor (parentTable rows m) 0 root (m.length - 1)) :
    block m root = m.drop root := by
  have offset : root + (m.length - 1 - root) = m.length - 1 := by omega
  have lower := (block_length_iff_ancestor rows m positive root (m.length - 1 - root)
    (by omega)).mpr (by simpa only [offset] using fence)
  have upper := (block_prefix m root).length_le
  have size : (block m root).length = (m.drop root).length := by
    simp only [List.length_drop] at upper ⊢
    omega
  rw [block_eq_take, size, List.take_length]

end BTnSSBMS.BMS

namespace BTnSSBMS.Encoder

theorem headState_first_reading (d : Nat) (a : ParentLabel) (hs : Forests ParentLabel)
    (visible : List Nat) (state : State d) (j : Nat) (room : j < d) :
    Parents.reading (BMS.parentTable (d + 2) (matrix (headState d a hs visible state)))
      j state.length = vector state visible a j := by
  obtain ⟨height, tag, rest, _, shape⟩ := encode_cons_first_row d a hs .nil visible state
  have length : (matrix state).length = state.length := by simp only [matrix, List.length_map]
  simp only [BMS.parentTable_reading, headState]
  rw [shape, ← length, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  simp only [List.getElem?_cons_zero, Option.getD_some, row_numerical_reading d _ height tag j room]

theorem sourceRootValue_new_head {d : Nat} {source : ParentContext} {visible : List Nat}
    (state : State d)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (a : List Nat) (hs : Forests (List Nat)) :
    let headed := headState d (Parents.label d source a)
      (Parents.annotateForests d (source ++ [Parents.label d source a]) hs) visible state
    sourceRootValue (source ++ [Parents.label d source a]) (visible ++ [headed.length - 1])
      headed source.length = vector state visible (Parents.label d source a) 0 := by
  dsimp only
  rw [sourceRootValue, Parents.append_label_parent, vector_eq_represented view, Parents.representedValue]
  cases selected : (Parents.label d source a).parents[0]?.join with
  | none => rfl
  | some p =>
    have inside := Parents.label_parent_bound d source a 0 p selected
    have extended : state <+: headState d (Parents.label d source a)
        (Parents.annotateForests d (source ++ [Parents.label d source a]) hs) visible state := encode_extends ..
    simp only [Option.map_some, Option.getD_some]
    rw [Parents.point_append_old visible p _ (by rw [view.length]; exact inside),
      ← Parents.reading_prefix (table_prefix extended) 0
        (Parents.point visible p) (view.bounded p inside)]

theorem encode_high_tail_fence {d : Nat} {source : ParentContext} {visible : List Nat}
    (state : State d) (positive : 0 < d) (coherent : Parents.Coherent d source)
    (valid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (a : List Nat) (hs : Forests (List Nat)) (tail : NumericalExpr)
    (separated : Source.ForestSeparated (.cons a hs tail))
    (above : ∀ col ∈ Source.labels tail, a[0]?.getD 0 < col[0]?.getD 0) :
    let result := encode d (Parents.annotate d source (.cons a hs tail)) visible state
    Parents.Ancestor (BMS.parentTable (d + 2) (matrix result)) 0 state.length (result.length - 1) := by
  let headed := headState d (Parents.label d source a)
    (Parents.annotateForests d (source ++ [Parents.label d source a]) hs) visible state
  let positions := visible ++ [headed.length - 1]
  let result := encode d (Parents.annotate d (source ++ [Parents.label d source a]) tail) positions headed
  have nextView := headState_view state positive coherent valid view a hs separated.1
  have fiber := headState_fiber state positive coherent valid view a hs separated.1
  obtain ⟨finalVisible, extended, finalView⟩ := encode_numerical_view d tail
    (source ++ [Parents.label d source a]) positions headed positive
    (Parents.coherent_append_label coherent a) (Parents.context_valid_append_label d source valid a)
    nextView separated.2
  have laterFence := forest_output_fence result (Source.labels tail) positive
    (Parents.coherent_append_label coherent a) (Parents.context_valid_append_label d source valid a)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    nextView.length extended (by
      intro col member
      simpa only [List.length_append, List.length_cons, List.length_nil, Nat.add_sub_cancel,
        Parents.reading_append_label] using above col member) finalView
  have atRoot : Parents.point positions ((source ++ [Parents.label d source a]).length - 1) =
      headed.length - 1 := by
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_sub_cancel,
      ← view.length, positions, Parents.point_append_last]
  rw [atRoot] at laterFence
  have firstToLast := ((fiber.connected 0 positive).prefix (table_prefix (encode_extends ..))).trans laterFence
  simpa only [Parents.annotate, encode_split_head] using firstToLast

/-- A generic exact source/target block equation. It uses only the
actual entering numerical view and forest separation, not BN or SB. -/
theorem encode_rootBlock (d : Nat) (source : ParentContext) (visible : List Nat) (state : State d)
    (positive : 0 < d) (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (a : List Nat) (hs : Forests (List Nat)) (tail : NumericalExpr)
    (separated : Source.ForestSeparated (.cons a hs tail)) :
    BMS.block (matrix (encode d (Parents.annotate d source (.cons a hs tail)) visible state)) state.length =
      (matrix (encode d (Parents.annotate d source (Source.rootBlock (.cons a hs tail))) visible state)).drop
        state.length := by
  let headed := headState d (Parents.label d source a)
    (Parents.annotateForests d (source ++ [Parents.label d source a]) hs) visible state
  have fiber := headState_fiber state positive coherent valid view a hs separated.1
  have nextView := headState_view state positive coherent valid view a hs separated.1
  have cutoff := encode_takeAbove_block d tail (a[0]?.getD 0)
    (source ++ [Parents.label d source a]) (visible ++ [headed.length - 1]) headed source.length state.length
    positive (Parents.coherent_append_label coherent a) (Parents.context_valid_append_label d source valid a)
    nextView separated.2 (by simp) fiber.firstBound (Parents.reading_append_label d source a 0)
    (by simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_sub_cancel]; exact .refl _)
    ((headState_first_reading d _ _ visible state 0 positive).trans (sourceRootValue_new_head state view a hs).symm)
  have blockSame : BMS.block (matrix (encode d (Parents.annotate d source (.cons a hs tail)) visible state))
      state.length = BMS.block
        (matrix (encode d (Parents.annotate d source (Source.rootBlock (.cons a hs tail))) visible state))
        state.length := by
    simpa only [Source.rootBlock, Parents.annotate, encode_split_head] using cutoff
  rw [blockSame]
  let shortened := Source.takeAbove (a[0]?.getD 0) tail
  let result := encode d (Parents.annotate d source (.cons a hs shortened)) visible state
  have wholeFence := encode_high_tail_fence state positive coherent valid view a hs shortened
    ⟨separated.1, Source.takeAbove_separated separated.2⟩ (Source.takeAbove_high _ tail)
  have initial : headed <+: result := by
    dsimp only [result]
    simp only [Parents.annotate, encode_split_head]
    exact encode_extends ..
  have bound : state.length < (matrix result).length := by
    have first := fiber.firstBound
    change state.length < headed.length at first
    have longer := initial.length_le
    simp only [matrix, List.length_map]
    omega
  apply BMS.block_eq_drop_of_frontier (d + 2) (matrix result) state.length (by omega) bound
  simpa only [matrix, List.length_map] using wholeFence

/-- The complete target block at any actual source entry is the exact
encoding of that source's complete block, not of its remaining tail. -/
theorem standard_entry_source_block {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {entry : Entry d}
    (member : entry ∈ entries d e [] [] [] [] []) :
    BMS.block (fromSource d e) entry.state.length =
      (matrix (encode d (Parents.annotate d entry.source (Source.rootBlock entry.remaining))
        entry.visible entry.state)).drop entry.state.length := by
  rw [standard_entry_block_closed positive standard member]
  have sound := standard_entries_sound positive standard entry member
  exact encode_rootBlock d entry.source entry.visible entry.state positive sound.coherent sound.valid
    sound.view entry.coordinates entry.attachments entry.tail sound.legal.separated

end BTnSSBMS.Encoder
