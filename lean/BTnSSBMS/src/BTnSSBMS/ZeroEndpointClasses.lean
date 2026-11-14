import BTnSSBMS.ClosingEntryOrigins

/-!
Every tag-zero output is a restored representative or an actual forest
slot. The exhaustive alternatives come from the frozen execution, with
all recursive output and subsequent enclosing exits included. No block
inequality is assumed in deriving this endpoint classification.
-/
namespace BTnSSBMS.Encoder

theorem Readout.emit_cases {state : State d} {u : Nat → Nat} {height tag : Nat}
    {frame : List Binding} {position value label : Nat}
    (output : Readout (emit state u height tag frame) position value label) :
    Readout state position value label ∨ position = state.length ∧ label = tag := by
  by_cases inside : position < state.length
  · obtain ⟨col, lookup, key, label⟩ := output
    exact .inl ⟨col, by simpa only [emit, List.getElem?_append_left inside] using lookup, key, label⟩
  · have bound := readout_bound output
    rw [emit_length] at bound
    have same : position = state.length := by omega
    subst position
    exact .inr ⟨rfl, readout_tag_unique output (readout_emit ..)⟩

theorem readout_zero_emit_nonzero {state : State d} {u : Nat → Nat} {height tag : Nat}
    {frame : List Binding} {position value : Nat} (nonzero : tag ≠ 0)
    (output : Readout (emit state u height tag frame) position value 0) :
    Readout state position value 0 := by
  rcases output.emit_cases with old | ⟨_, same⟩
  · exact old
  · exact False.elim (nonzero same.symm)

mutual
  theorem encode_zero_classes (d : Nat) (e : ParentExpr) (visible : List Nat) (state : State d)
      (position height : Nat) (output : Readout (encode d e visible state) position height 0) :
      Readout state position height 0 ∨ SelfLatest (encode d e visible state) position ∨
        position ∈ slotPositions d e visible state := by
    cases e with
    | nil => exact .inl output
    | cons a hs tail =>
      let key := Keys.ofColumn d visible.length a hs
      let frame := frameAt state (representative visible a (d - 1))
      let below := smaller frame key
      let u := vector state visible a
      simp only [encode] at output
      split at output
      next bound found =>
        simp only [encode, slotPositions, found]
        let updated := below ++ [{bound with latest := some state.length}]
        let next := emit state u bound.height 0 updated
        rcases encode_zero_classes d tail (visible ++ [state.length]) next position height output with
            old | self | slot
        · rcases old.emit_cases with earlier | ⟨same, _⟩
          · exact .inl earlier
          · subst position
            exact .inr (.inl ((selfLatest_emit state u bound.height 0 updated
              {bound with latest := some state.length} (List.mem_append_right _ (by simp)) rfl).extends
                (encode_extends ..)))
        · exact .inr (.inl self)
        · exact .inr (.inr slot)
      next fresh =>
        simp only [encode, slotPositions, fresh]
        let c := (base below).height
        let guarded := emit (emit state u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 []
        let forests := encodeForests d hs visible u c below guarded
        let saved := below ++ [⟨key, c + 2, some forests.length, some state.length⟩]
        let closed := emit forests (fun j => u j + 1) (c + 2) 0 saved
        let result := encode d tail (visible ++ [forests.length]) closed
        have forestPrefix : forests <+: result := (emit_extends ..).trans (encode_extends ..)
        rcases encode_zero_classes d tail (visible ++ [forests.length]) closed position height output with
            old | self | slot
        · rcases old.emit_cases with inForests | ⟨same, _⟩
          · rcases encodeForests_zero_classes d hs visible u c below guarded position height inForests with
                earlier | self | slot
            · exact .inl (readout_zero_emit_nonzero (by decide : 1 ≠ 0)
                (readout_zero_emit_nonzero (by decide : 2 ≠ 0) earlier))
            · exact .inr (.inl (self.extends forestPrefix))
            · exact .inr (.inr (List.mem_append_left _ slot))
          · subst position
            exact .inr (.inl ((selfLatest_emit forests (fun j => u j + 1) (c + 2) 0 saved
              ⟨key, c + 2, some forests.length, some state.length⟩
              (List.mem_append_right _ (by simp)) rfl).extends (encode_extends ..)))
        · exact .inr (.inl self)
        · exact .inr (.inr (List.mem_append_right _ slot))

  theorem encodeForests_zero_classes (d : Nat) (hs : Forests ParentLabel) (visible : List Nat)
      (u : Nat → Nat) (c : Nat) (below : List Binding) (state : State d)
      (position height : Nat)
      (output : Readout (encodeForests d hs visible u c below state) position height 0) :
      Readout state position height 0 ∨ SelfLatest (encodeForests d hs visible u c below state) position ∨
        position ∈ forestSlotPositions d hs visible u c below state := by
    cases hs with
    | nil => exact .inl output
    | cons h hs =>
      let withSlot := emit state (fun j => u j + 2) (c + 2) 0 below
      let withForest := encode d h (visible ++ [state.length]) withSlot
      simp only [encodeForests, forestSlotPositions]
      rcases encodeForests_zero_classes d hs visible u c below withForest position height output with
          inForest | self | slot
      · rcases encode_zero_classes d h (visible ++ [state.length]) withSlot position height inForest with
            old | self | slot
        · rcases old.emit_cases with earlier | ⟨same, _⟩
          · exact .inl earlier
          · exact .inr (.inr (List.mem_cons.mpr (.inl same)))
        · exact .inr (.inl (self.extends (encodeForests_extends ..)))
        · exact .inr (.inr (List.mem_cons.mpr (.inr (List.mem_append_left _ slot))))
      · exact .inr (.inl self)
      · exact .inr (.inr (List.mem_cons.mpr (.inr (List.mem_append_right _ slot))))
end

theorem source_zero_entry_or_slot (d : Nat) (e : NumericalExpr) {position height : Nat}
    (output : Readout (encode d (Parents.annotate d [] e) [] []) position height 0) :
    (∃ entry ∈ entries d e [] [] [] [] [], entry.closing = position) ∨
      position ∈ slotPositions d (Parents.annotate d [] e) [] [] := by
  rcases encode_zero_classes d (Parents.annotate d [] e) [] [] position height output with old | self | slot
  · have impossible := readout_bound old
    simp at impossible
  · exact .inl ((source_selfLatest_iff_closing_entry d e position).mp self)
  · exact .inr slot

/-- All tag-zero strict key-ancestor pairs have a closing representative
on the left and either a closing representative or a slot on the right.
This identifies the actual endpoints; it does not assert their SB inequality. -/
theorem standard_zero_key_pair_classes {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {a b heightA heightB : Nat}
    (left : Readout (encode d (Parents.annotate d [] e) [] []) a heightA 0)
    (right : Readout (encode d (Parents.annotate d [] e) [] []) b heightB 0)
    (different : a ≠ b)
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (fromSource d e)) d a b) :
    ∃ earlier ∈ entries d e [] [] [] [] [], earlier.closing = a ∧
      ((∃ later ∈ entries d e [] [] [] [] [], later.closing = b) ∨
        b ∈ slotPositions d (Parents.annotate d [] e) [] []) := by
  obtain ⟨entry, member, same⟩ := standard_zero_strict_key_ancestor_entry positive standard left different path
  exact ⟨entry, member, same, source_zero_entry_or_slot d e right⟩

end BTnSSBMS.Encoder
