import BTnSSBMS.BlockCutoff
import BTnSSBMS.EntryActivation

/-!
No complete row-zero block rooted at a real source entry can leave that
entry's lexical execution. Forest exits are actual later slots or the
owner's close, not arbitrary delimiters imposed on the output afterwards.
This is a boundary theorem, not BN or SB.
-/
namespace BTnSSBMS.Encoder

mutual
  theorem entries_blocks_closed (d : Nat) (e : NumericalExpr) (source : ParentContext)
      (visible owners : List Nat) (materials : List (Forests (List Nat))) (state : State d)
      (positive : 0 < d) (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
      (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix state)) visible)
      (separated : Source.ForestSeparated e)
      (floor : Option (Nat × Nat)) (fence : OrderFence source visible state floor)
      (above : AboveFloor floor e) (exit : Matrix) (low : ExitBelow (floor.map Prod.snd) exit) :
      ∀ entry ∈ entries d e source visible owners materials state,
        BMS.block (matrix (encode d (Parents.annotate d source e) visible state) ++ exit) entry.state.length =
          BMS.block (matrix entry.result) entry.state.length := by
    cases e with
    | nil => intro entry member; simp only [entries, List.not_mem_nil] at member
    | cons coordinates hs tail =>
      let a := Parents.label d source coordinates
      let annotated := Parents.annotateForests d (source ++ [a]) hs
      let key := Keys.ofColumn d visible.length a annotated
      let frame := frameAt state (representative visible a (d - 1))
      let below := smaller frame key
      let c := (base below).height
      let u := vector state visible a
      let headed := headState d a annotated visible state
      let guarded := emit (emit state u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 []
      have rootAbove : ∀ s t, floor = some (s, t) → s < coordinates[0]?.getD 0 :=
        fun s t eq => above s t eq coordinates (by simp only [Source.labels, List.mem_cons, true_or])
      have innerClosed : ∀ entry ∈ (match equal frame key with
          | some _ => []
          | none => forestEntries d hs source coordinates visible owners materials hs u c below guarded),
          BMS.block (matrix (encode d (Parents.annotate d source (.cons coordinates hs tail)) visible state) ++ exit)
            entry.state.length = BMS.block (matrix entry.result) entry.state.length := by
        cases found : equal frame key with
        | some bound => intro entry member; simp only [List.not_mem_nil] at member
        | none =>
          obtain ⟨extra, shape, extraLow⟩ := encode_cons_close_extension d a annotated
            (Parents.annotate d (source ++ [a]) tail) visible state positive found exit
          have result := forestEntries_blocks_closed d hs source coordinates visible owners materials hs
            state guarded u (state.length + 1) c below positive coherent valid view
            (initial_numerical_gate state coherent valid view coordinates c) separated.1 extra extraLow
          intro entry member
          change BMS.block (matrix (encode d (.cons a annotated _) visible state) ++ exit) entry.state.length = _
          rw [shape]
          exact result entry member
      have nextFence := fence.after_head state positive coherent valid view coordinates hs rootAbove
      have nextView := headState_view state positive coherent valid view coordinates hs separated.1
      have tailClosed := entries_blocks_closed d tail (source ++ [a]) (visible ++ [headed.length - 1])
        owners (materials ++ [hs]) headed positive (Parents.coherent_append_label coherent coordinates)
        (Parents.context_valid_append_label d source valid coordinates) nextView separated.2 floor nextFence
        (fun s t eq col member => above s t eq col (by simp only [Source.labels, List.mem_cons]; exact Or.inr member))
        exit low
      intro entry member
      simp only [entries, List.mem_cons, List.mem_append] at member
      rcases member with rfl | inner | later
      · exact head_block_closed d source visible state positive coherent valid view coordinates hs tail
          floor fence rootAbove exit low
      · exact innerClosed entry inner
      · simpa only [Parents.annotate, encode_split_head] using tailClosed entry later

  theorem forestEntries_blocks_closed (d : Nat) (hs : Forests (List Nat)) (source : ParentContext)
      (coordinates visible owners : List Nat) (materials : List (Forests (List Nat)))
      (ownerMaterial : Forests (List Nat)) (original state : State d) (u : Nat → Nat)
      (gate c : Nat) (below : List Binding) (positive : 0 < d)
      (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
      (view : Parents.NumericalView d source (BMS.parentTable (d + 2) (matrix original)) visible)
      (scope : NumericalGate d source coordinates visible original state u gate)
      (separated : Source.ForestsAbove (coordinates[0]?.getD 0) hs)
      (exit : Matrix) (low : ExitBelow (some (u 0 + 1)) exit) :
      ∀ entry ∈ forestEntries d hs source coordinates visible owners materials ownerMaterial u c below state,
        BMS.block (matrix (encodeForests d
          (Parents.annotateForests d (source ++ [Parents.label d source coordinates]) hs)
          visible u c below state) ++ exit) entry.state.length =
            BMS.block (matrix entry.result) entry.state.length := by
    cases hs with
    | nil => intro entry member; simp only [forestEntries, List.not_mem_nil] at member
    | cons h hs =>
      let context := source ++ [Parents.label d source coordinates]
      let positions := visible ++ [state.length]
      let slot := emit state (fun j => u j + 2) (c + 2) 0 below
      let next := encode d (Parents.annotate d context h) positions slot
      have contextCoherent := Parents.coherent_append_label coherent coordinates
      have contextValid := Parents.context_valid_append_label d source valid coordinates
      have slotView := scope.slot_view valid view (c + 2) below
      have slotFence : OrderFence context positions slot
          (some (coordinates[0]?.getD 0, u 0 + 2)) := by
        refine ⟨source.length, by simp only [context, List.length_append, List.length_cons, List.length_nil]; omega,
          ?_, ?_, ?_⟩
        · exact Parents.reading_append_label d source coordinates 0
        · simp only [context, List.length_append, List.length_cons, List.length_nil, Nat.add_sub_cancel]
          exact .refl _
        · dsimp only [positions, slot]
          rw [← view.length, Parents.point_append_last]
          exact emitted_numerical_value state (fun j => u j + 2) (c + 2) 0 below 0 positive
      have aboveH : AboveFloor (some (coordinates[0]?.getD 0, u 0 + 2)) h := by
        intro s t eq col member
        have same := Option.some.inj eq
        cases same
        exact separated.1 col member
      obtain ⟨extra, shape, extraLow⟩ := encodeForests_extension_low d
        (Parents.annotateForests d context hs) visible u c below next positive exit
        (low.mono (by omega : u 0 + 1 ≤ u 0 + 2))
      have innerClosed := entries_blocks_closed d h context positions (owners ++ [source.length])
        (materials ++ [ownerMaterial]) slot positive contextCoherent contextValid slotView separated.2.1
        (some (coordinates[0]?.getD 0, u 0 + 2)) slotFence aboveH extra extraLow
      obtain ⟨finalVisible, extended, forestView⟩ := encode_numerical_view d h context positions slot
        positive contextCoherent contextValid slotView separated.2.1
      have nextScope := scope.after_forest positive coherent valid view.length (c + 2) below
        (Source.labels h) (encode_extends d _ _ _) extended separated.1 forestView
      have laterClosed := forestEntries_blocks_closed d hs source coordinates visible owners materials ownerMaterial
        original next u gate c below positive coherent valid view nextScope separated.2.2 exit low
      intro entry member
      simp only [forestEntries, List.mem_append] at member
      rcases member with inner | later
      · change BMS.block (matrix (encodeForests d (Parents.annotateForests d context hs)
            visible u c below next) ++ exit) entry.state.length = _
        rw [shape]
        exact innerClosed entry inner
      · exact laterClosed entry later
end

theorem source_entry_block_closed (d : Nat) (e : NumericalExpr) (positive : 0 < d)
    (separated : Source.ForestSeparated e) {entry : Entry d}
    (member : entry ∈ entries d e [] [] [] [] []) :
    BMS.block (fromSource d e) entry.state.length = BMS.block (matrix entry.result) entry.state.length := by
  have result := entries_blocks_closed d e [] [] [] [] [] positive (Parents.empty_coherent d)
    Parents.empty_context_valid (Parents.empty_numerical_view d) separated none True.intro
    (by intro s t equal; cases equal) [] True.intro entry member
  simpa only [List.append_nil, fromSource] using result

theorem standard_entry_block_closed {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {entry : Entry d}
    (member : entry ∈ entries d e [] [] [] [] []) :
    BMS.block (fromSource d e) entry.state.length = BMS.block (matrix entry.result) entry.state.length :=
  source_entry_block_closed d e positive (Source.standard_finiteLegal positive standard).separated member

theorem standard_entry_block_bound {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {entry : Entry d}
    (member : entry ∈ entries d e [] [] [] [] []) :
    entry.state.length + (BMS.block (fromSource d e) entry.state.length).length ≤ entry.result.length := by
  rw [standard_entry_block_closed positive standard member]
  have bound := (BMS.block_prefix (matrix entry.result) entry.state.length).length_le
  have stateBound := entry.state_prefix_result.length_le
  simp only [List.length_drop, matrix, List.length_map] at bound ⊢
  omega

/-- A later visible source head at or below the old root's zeroth value
is already outside that root's target block. This supplies a real cutoff
for source outer-block truncation, not merely a lexical scope cutoff. -/
theorem standard_entry_block_ends_before {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {earlier later : Entry d}
    (oldMember : earlier ∈ entries d e [] [] [] [] [])
    (newMember : later ∈ entries d e [] [] [] [] []) {root : Nat}
    (origin : earlier.OriginAt later.source later.visible later.owners later.materials later.state root)
    (insideRoot : root < later.source.length)
    (low : later.coordinates[0]?.getD 0 ≤ earlier.coordinates[0]?.getD 0) :
    earlier.state.length + (BMS.block (fromSource d e) earlier.state.length).length ≤ later.state.length := by
  have sound := standard_entries_sound positive standard later newMember
  have representedBound := sound.view.bounded root insideRoot
  rw [table_length] at representedBound
  have representativeAfter := origin.beforeRepresentative
  have before : earlier.state.length < later.state.length := by omega
  have finalBound := (entries_execution d e [] [] [] [] [] later newMember).resultPrefix.length_le
  have nonempty := later.first_lt_result
  have inside : later.state.length < (fromSource d e).length := by
    simpa only [fromSource, matrix, List.length_map] using Nat.lt_of_lt_of_le nonempty finalBound
  apply Nat.le_of_not_gt
  intro reaches
  have lengthBound : later.state.length - earlier.state.length <
      (BMS.block (fromSource d e) earlier.state.length).length := by omega
  have path := (BMS.block_length_iff_ancestor (d + 2) (fromSource d e) (by omega)
    earlier.state.length (later.state.length - earlier.state.length) (by omega)).mp lengthBound
  have restored : earlier.state.length + (later.state.length - earlier.state.length) = later.state.length := by omega
  rw [restored] at path
  have sourcePath := standard_entry_ancestor_reflect positive standard oldMember newMember origin insideRoot positive path
  have strict := sourcePath.reading_lt (Parents.coherent_append_label sound.coherent later.coordinates) (by omega)
  rw [Parents.reading_append_label,
    ← Parents.reading_prefix (List.prefix_append _ _) 0 root insideRoot] at strict
  have rootValue : Parents.reading later.source 0 root = earlier.coordinates[0]?.getD 0 := by
    simp only [Parents.reading, ← origin.labelEq, Parents.label]
  rw [rootValue] at strict
  omega

end BTnSSBMS.Encoder
