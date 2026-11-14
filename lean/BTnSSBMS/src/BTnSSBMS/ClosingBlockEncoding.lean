import BTnSSBMS.DescendantBlocks

/-!
The complete block at a restored representative is not in general the
block at the first output of its source column. This file identifies the
actual closing block, removing the definition and attachment outputs but
retaining the closing column and the entire encoded source-block tail.
-/
namespace BTnSSBMS.Encoder

theorem encode_high_tail_closing_fence {d : Nat} {source : ParentContext} {visible : List Nat}
    (state : State d) (positive : 0 < d) (coherent : Parents.Coherent d source)
    (valid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (a : List Nat) (hs : Forests (List Nat)) (tail : NumericalExpr)
    (separated : Source.ForestSeparated (.cons a hs tail))
    (above : ∀ col ∈ Source.labels tail, a[0]?.getD 0 < col[0]?.getD 0) :
    let headed := headState d (Parents.label d source a)
      (Parents.annotateForests d (source ++ [Parents.label d source a]) hs) visible state
    let result := encode d (Parents.annotate d source (.cons a hs tail)) visible state
    Parents.Ancestor (BMS.parentTable (d + 2) (matrix result)) 0 (headed.length - 1) (result.length - 1) := by
  let headed := headState d (Parents.label d source a)
    (Parents.annotateForests d (source ++ [Parents.label d source a]) hs) visible state
  let positions := visible ++ [headed.length - 1]
  let result := encode d (Parents.annotate d (source ++ [Parents.label d source a]) tail) positions headed
  have nextView := headState_view state positive coherent valid view a hs separated.1
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
  simpa only [Parents.annotate, encode_split_head] using laterFence

/-- The local representative's complete block is the complete source-block
encoding with everything strictly before the representative removed. -/
theorem encode_closing_rootBlock (d : Nat) (source : ParentContext) (visible : List Nat) (state : State d)
    (positive : 0 < d) (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
    (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
    (a : List Nat) (hs : Forests (List Nat)) (tail : NumericalExpr)
    (separated : Source.ForestSeparated (.cons a hs tail)) :
    let headed := headState d (Parents.label d source a)
      (Parents.annotateForests d (source ++ [Parents.label d source a]) hs) visible state
    BMS.block (matrix (encode d (Parents.annotate d source (.cons a hs tail)) visible state))
        (headed.length - 1) =
      (matrix (encode d (Parents.annotate d source (Source.rootBlock (.cons a hs tail))) visible state)).drop
        (headed.length - 1) := by
  let headed := headState d (Parents.label d source a)
    (Parents.annotateForests d (source ++ [Parents.label d source a]) hs) visible state
  have fiber := headState_fiber state positive coherent valid view a hs separated.1
  have nextView := headState_view state positive coherent valid view a hs separated.1
  have cutoff := encode_takeAbove_block_of_le d tail (a[0]?.getD 0)
    (source ++ [Parents.label d source a]) (visible ++ [headed.length - 1]) headed source.length
    (headed.length - 1) positive (Parents.coherent_append_label coherent a)
    (Parents.context_valid_append_label d source valid a) nextView separated.2
    (by simp) fiber.representativeBound (Parents.reading_append_label d source a 0)
    (by simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_sub_cancel]; exact .refl _)
    (by
      rw [sourceRootValue_new_head state view a hs]
      exact Nat.le_trans (Nat.le_of_eq (headState_first_reading d _ _ visible state 0 positive).symm)
        ((fiber.connected 0 positive).reading_le (BMS.parentTable_coherent _ _)))
  have blockSame : BMS.block (matrix (encode d (Parents.annotate d source (.cons a hs tail)) visible state))
      (headed.length - 1) = BMS.block
        (matrix (encode d (Parents.annotate d source (Source.rootBlock (.cons a hs tail))) visible state))
        (headed.length - 1) := by
    simpa only [Source.rootBlock, Parents.annotate, encode_split_head] using cutoff
  dsimp only
  rw [blockSame]
  let shortened := Source.takeAbove (a[0]?.getD 0) tail
  let result := encode d (Parents.annotate d source (.cons a hs shortened)) visible state
  have wholeFence := encode_high_tail_closing_fence state positive coherent valid view a hs shortened
    ⟨separated.1, Source.takeAbove_separated separated.2⟩ (Source.takeAbove_high _ tail)
  have initial : headed <+: result := by
    dsimp only [result]
    simp only [Parents.annotate, encode_split_head]
    exact encode_extends ..
  have bound : headed.length - 1 < (matrix result).length := by
    have nonempty := headState_nonempty d (Parents.label d source a)
      (Parents.annotateForests d (source ++ [Parents.label d source a]) hs) visible state
    change 0 < headed.length at nonempty
    have longer := initial.length_le
    simp only [matrix, List.length_map]
    omega
  apply BMS.block_eq_drop_of_frontier (d + 2) (matrix result) (headed.length - 1) (by omega) bound
  simpa only [matrix, List.length_map] using wholeFence

def Entry.headed (entry : Entry d) : State d :=
  headState d (Parents.label d entry.source entry.coordinates)
    (Parents.annotateForests d (entry.source ++ [Parents.label d entry.source entry.coordinates]) entry.attachments)
    entry.visible entry.state

def Entry.closing (entry : Entry d) : Nat := entry.headed.length - 1

theorem Entry.headed_prefix_result (entry : Entry d) : entry.headed <+: entry.result := by
  simp only [Entry.result, Entry.remaining, Parents.annotate, encode_split_head]
  exact encode_extends ..

theorem Entry.closing_inside (entry : Entry d) : entry.closing < entry.result.length := by
  have nonempty := headState_nonempty d (Parents.label d entry.source entry.coordinates)
    (Parents.annotateForests d (entry.source ++ [Parents.label d entry.source entry.coordinates]) entry.attachments)
    entry.visible entry.state
  change 0 < entry.headed.length at nonempty
  have longer := entry.headed_prefix_result.length_le
  dsimp only [Entry.closing]
  omega

/-- No later sibling forest or enclosing exit extends an actual closing
block beyond its local execution. The boundary follows from ancestry,
not from treating this representative as another first-output entry. -/
theorem standard_entry_closing_block_closed {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {entry : Entry d}
    (member : entry ∈ entries d e [] [] [] [] []) :
    BMS.block (fromSource d e) entry.closing = BMS.block (matrix entry.result) entry.closing := by
  have sound := standard_entries_sound positive standard entry member
  have fiber := headState_fiber entry.state positive sound.coherent sound.valid sound.view
    entry.coordinates entry.attachments sound.legal.2.2.2.1.separated
  have resultPrefix := (entries_execution d e [] [] [] [] [] entry member).resultPrefix
  have headPrefix := entry.headed_prefix_result.trans resultPrefix
  have matrixPrefix : matrix entry.result <+: fromSource d e := by
    obtain ⟨extra, shape⟩ := matrix_extension resultPrefix
    exact ⟨extra, shape.symm⟩
  have path : Parents.Ancestor (BMS.parentTable (d + 2) (fromSource d e)) 0
      entry.state.length entry.closing :=
    (fiber.connected 0 positive).prefix (table_prefix headPrefix)
  exact BMS.block_restrict_descendant (rows := d + 2) (by omega) matrixPrefix
    (by simpa only [matrix, List.length_map] using entry.closing_inside) path
    (by simpa only [matrix, List.length_map] using standard_entry_block_bound positive standard member)

/-- Exact complete-block formula at every restored representative in
the entire standard source domain, including newly defined closing P's. -/
theorem standard_entry_closing_source_block {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {entry : Entry d}
    (member : entry ∈ entries d e [] [] [] [] []) :
    BMS.block (fromSource d e) entry.closing =
      (matrix (encode d (Parents.annotate d entry.source (Source.rootBlock entry.remaining))
        entry.visible entry.state)).drop entry.closing := by
  rw [standard_entry_closing_block_closed positive standard member]
  have sound := standard_entries_sound positive standard entry member
  exact encode_closing_rootBlock d entry.source entry.visible entry.state positive sound.coherent sound.valid
    sound.view entry.coordinates entry.attachments entry.tail sound.legal.separated

end BTnSSBMS.Encoder
