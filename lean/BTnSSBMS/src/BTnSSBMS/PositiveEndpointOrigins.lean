import BTnSSBMS.ZeroEndpointClasses

/-!
Every positive-tag column is either the actual definition column of a
fresh source entry or its immediately following guard. Freshness here is
the real failed lookup in that entry's saved environment, not a numerical
heuristic or a condition imposed on the target after encoding.
-/
namespace BTnSSBMS.Encoder

def Entry.Fresh (entry : Entry d) : Prop :=
  equal (frameAt entry.state
    (representative entry.visible (Parents.label d entry.source entry.coordinates) (d - 1)))
    (Keys.ofColumn d entry.visible.length (Parents.label d entry.source entry.coordinates)
      (Parents.annotateForests d (entry.source ++ [Parents.label d entry.source entry.coordinates]) entry.attachments)) = none

theorem readout_positive_emit_zero {state : State d} {u : Nat → Nat} {height : Nat}
    {frame : List Binding} {position value tag : Nat} (positive : 0 < tag)
    (output : Readout (emit state u height 0 frame) position value tag) :
    Readout state position value tag := by
  rcases output.emit_cases with old | ⟨_, same⟩
  · exact old
  · omega

mutual
  theorem entries_positive_origins (d : Nat) (e : NumericalExpr) (source : ParentContext)
      (visible owners : List Nat) (materials : List (Forests (List Nat))) (state : State d)
      (position height tag : Nat) (positive : 0 < tag)
      (output : Readout (encode d (Parents.annotate d source e) visible state) position height tag) :
      Readout state position height tag ∨
        ∃ entry ∈ entries d e source visible owners materials state, entry.Fresh ∧
          ((tag = 1 ∧ position = entry.state.length) ∨ (tag = 2 ∧ position = entry.state.length + 1)) := by
    cases e with
    | nil => exact .inl output
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
      let forests := encodeForests d annotated visible u c below guarded
      have tailOutput : Readout
          (encode d (Parents.annotate d (source ++ [a]) tail) (visible ++ [headed.length - 1]) headed)
          position height tag := by
        simpa only [Parents.annotate, encode_split_head] using output
      rcases entries_positive_origins d tail (source ++ [a]) (visible ++ [headed.length - 1])
          owners (materials ++ [hs]) headed position height tag positive tailOutput with
          atHead | ⟨entry, member, freshEntry, shape⟩
      · cases found : equal frame key with
        | some bound =>
          dsimp only [frame, key] at found
          have atEmit : Readout (emit state u bound.height 0
              (below ++ [{bound with latest := some state.length}])) position height tag := by
            simpa only [headed, headState, encode, found] using atHead
          exact .inl (readout_positive_emit_zero positive atEmit)
        | none =>
          dsimp only [frame, key] at found
          have atEmit : Readout (emit forests (fun j => u j + 1) (c + 2) 0
              (below ++ [⟨key, c + 2, some forests.length, some state.length⟩])) position height tag := by
            simpa only [headed, headState, encode, found] using atHead
          have inForests := readout_positive_emit_zero positive atEmit
          rcases forestEntries_positive_origins d hs source coordinates visible owners materials hs
              u c below guarded position height tag positive inForests with
              old | ⟨entry, member, freshEntry, shape⟩
          · rcases old.emit_cases with atDefinition | ⟨atGuard, guardTag⟩
            · rcases atDefinition.emit_cases with earlier | ⟨atDefinition, definitionTag⟩
              · exact .inl earlier
              · exact .inr ⟨⟨source, coordinates, hs, tail, visible, owners, materials, state⟩,
                  List.mem_cons_self, found, .inl ⟨definitionTag, atDefinition⟩⟩
            · refine .inr ⟨⟨source, coordinates, hs, tail, visible, owners, materials, state⟩,
                List.mem_cons_self, found, .inr ⟨guardTag, ?_⟩⟩
              simpa only [emit_length] using atGuard
          · refine .inr ⟨entry, ?_, freshEntry, shape⟩
            dsimp only [a, annotated] at found
            simp only [entries, found, List.mem_cons, List.mem_append]
            exact .inr (.inl member)
      · refine .inr ⟨entry, ?_, freshEntry, shape⟩
        simp only [entries, List.mem_cons, List.mem_append]
        exact .inr (.inr member)

  theorem forestEntries_positive_origins (d : Nat) (hs : Forests (List Nat)) (source : ParentContext)
      (coordinates visible owners : List Nat) (materials : List (Forests (List Nat)))
      (ownerMaterial : Forests (List Nat)) (u : Nat → Nat) (c : Nat) (below : List Binding)
      (state : State d) (position height tag : Nat) (positive : 0 < tag)
      (output : Readout
        (encodeForests d (Parents.annotateForests d (source ++ [Parents.label d source coordinates]) hs)
          visible u c below state) position height tag) :
      Readout state position height tag ∨
        ∃ entry ∈ forestEntries d hs source coordinates visible owners materials ownerMaterial u c below state,
          entry.Fresh ∧ ((tag = 1 ∧ position = entry.state.length) ∨
            (tag = 2 ∧ position = entry.state.length + 1)) := by
    cases hs with
    | nil => exact .inl output
    | cons h hs =>
      let a := Parents.label d source coordinates
      let withSlot := emit state (fun j => u j + 2) (c + 2) 0 below
      let withForest := encode d (Parents.annotate d (source ++ [a]) h) (visible ++ [state.length]) withSlot
      rcases forestEntries_positive_origins d hs source coordinates visible owners materials ownerMaterial
          u c below withForest position height tag positive output with
          inForest | ⟨entry, member, freshEntry, shape⟩
      · rcases entries_positive_origins d h (source ++ [a]) (visible ++ [state.length])
            (owners ++ [source.length]) (materials ++ [ownerMaterial]) withSlot
            position height tag positive inForest with old | ⟨entry, member, freshEntry, shape⟩
        · exact .inl (readout_positive_emit_zero positive old)
        · refine .inr ⟨entry, ?_, freshEntry, shape⟩
          simp only [forestEntries, List.mem_append]
          exact .inl member
      · refine .inr ⟨entry, ?_, freshEntry, shape⟩
        simp only [forestEntries, List.mem_append]
        exact .inr member
end

theorem source_positive_entry (d : Nat) (e : NumericalExpr) {position height tag : Nat}
    (positive : 0 < tag) (output : Readout (encode d (Parents.annotate d [] e) [] []) position height tag) :
    ∃ entry ∈ entries d e [] [] [] [] [], entry.Fresh ∧
      ((tag = 1 ∧ position = entry.state.length) ∨ (tag = 2 ∧ position = entry.state.length + 1)) := by
  rcases entries_positive_origins d e [] [] [] [] [] position height tag positive output with old | found
  · have impossible := readout_bound old
    simp at impossible
  · exact found

theorem source_definition_entry (d : Nat) (e : NumericalExpr) {position height : Nat}
    (output : Readout (encode d (Parents.annotate d [] e) [] []) position height 1) :
    ∃ entry ∈ entries d e [] [] [] [] [], entry.Fresh ∧ position = entry.state.length := by
  obtain ⟨entry, member, fresh, left | right⟩ := source_positive_entry d e (by decide) output
  · exact ⟨entry, member, fresh, left.2⟩
  · have impossible := right.1
    cases impossible

theorem source_guard_entry (d : Nat) (e : NumericalExpr) {position height : Nat}
    (output : Readout (encode d (Parents.annotate d [] e) [] []) position height 2) :
    ∃ entry ∈ entries d e [] [] [] [] [], entry.Fresh ∧ position = entry.state.length + 1 := by
  obtain ⟨entry, member, fresh, left | right⟩ := source_positive_entry d e (by decide) output
  · have impossible := left.1
    cases impossible
  · exact ⟨entry, member, fresh, right.2⟩

end BTnSSBMS.Encoder
