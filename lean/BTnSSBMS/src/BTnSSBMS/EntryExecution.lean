import BTnSSBMS.EntrySoundness

/-!
Each snapshot is an actual subexecution: its state and complete lexical
result occur as prefixes of the enclosing execution. Scope prefixes are
relative to that enclosing call, not to every earlier chronological
entry; unrelated sibling forests must not be identified.
-/
namespace BTnSSBMS.Encoder

structure Entry.InRun (source : ParentContext) (visible owners : List Nat)
    (materials : List (Forests (List Nat))) (state result : State d) (entry : Entry d) : Prop where
  sourcePrefix : source <+: entry.source
  visiblePrefix : visible <+: entry.visible
  ownersPrefix : owners <+: entry.owners
  materialPrefix : materials <+: entry.materials
  statePrefix : state <+: entry.state
  resultPrefix : entry.result <+: result

theorem Entry.InRun.enclose {d : Nat} {source innerSource : ParentContext}
    {visible innerVisible owners innerOwners : List Nat}
    {materials innerMaterials : List (Forests (List Nat))}
    {state innerState result innerResult : State d} {entry : Entry d}
    (run : Entry.InRun innerSource innerVisible innerOwners innerMaterials innerState innerResult entry)
    (sourcePrefix : source <+: innerSource) (visiblePrefix : visible <+: innerVisible)
    (ownersPrefix : owners <+: innerOwners) (materialPrefix : materials <+: innerMaterials)
    (statePrefix : state <+: innerState) (resultPrefix : innerResult <+: result) :
    Entry.InRun source visible owners materials state result entry :=
  ⟨sourcePrefix.trans run.sourcePrefix, visiblePrefix.trans run.visiblePrefix,
    ownersPrefix.trans run.ownersPrefix, materialPrefix.trans run.materialPrefix,
    statePrefix.trans run.statePrefix, run.resultPrefix.trans resultPrefix⟩

theorem Entry.state_prefix_result (entry : Entry d) : entry.state <+: entry.result :=
  encode_extends d (Parents.annotate d entry.source entry.remaining) entry.visible entry.state

mutual
  theorem entries_execution (d : Nat) (e : NumericalExpr) (source : ParentContext)
      (visible owners : List Nat) (materials : List (Forests (List Nat))) (state : State d) :
      ∀ entry ∈ entries d e source visible owners materials state,
        Entry.InRun source visible owners materials state
          (encode d (Parents.annotate d source e) visible state) entry := by
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
      let result := encode d (Parents.annotate d source (.cons coordinates hs tail)) visible state
      have headPrefix : headed <+: result := by
        simp only [result, Parents.annotate, encode_split_head]
        exact encode_extends ..
      have innerRun : ∀ entry ∈ (match equal frame key with
          | some _ => []
          | none => forestEntries d hs source coordinates visible owners materials hs u c below guarded),
          Entry.InRun source visible owners materials state result entry := by
        cases found : equal frame key with
        | some bound => intro entry member; simp only [List.not_mem_nil] at member
        | none =>
          intro entry member
          have run := forestEntries_execution d hs source coordinates visible owners materials hs u c below guarded entry member
          have forestPrefix : encodeForests d annotated visible u c below guarded <+: headed := by
            dsimp only [frame, key] at found
            simp only [headed, headState, encode, found]
            exact emit_extends ..
          exact run.enclose (List.prefix_refl _) (List.prefix_refl _) (List.prefix_refl _) (List.prefix_refl _)
            ((emit_extends ..).trans (emit_extends ..)) (forestPrefix.trans headPrefix)
      intro entry member
      simp only [entries, List.mem_cons, List.mem_append] at member
      rcases member with rfl | inner | later
      · exact ⟨List.prefix_refl _, List.prefix_refl _, List.prefix_refl _, List.prefix_refl _,
          List.prefix_refl _, List.prefix_refl _⟩
      · exact innerRun entry inner
      · have run := entries_execution d tail (source ++ [a]) (visible ++ [headed.length - 1]) owners
          (materials ++ [hs]) headed entry later
        have resultSame : encode d (Parents.annotate d (source ++ [a]) tail)
            (visible ++ [headed.length - 1]) headed = result := by
          simp only [result, Parents.annotate, encode_split_head]
          rfl
        exact run.enclose (List.prefix_append _ _) (List.prefix_append _ _) (List.prefix_refl _)
          (List.prefix_append _ _) (encode_extends ..) (resultSame ▸ List.prefix_refl _)

  theorem forestEntries_execution (d : Nat) (hs : Forests (List Nat)) (source : ParentContext)
      (coordinates visible owners : List Nat) (materials : List (Forests (List Nat)))
      (ownerMaterial : Forests (List Nat)) (u : Nat → Nat) (c : Nat) (below : List Binding)
      (state : State d) :
      ∀ entry ∈ forestEntries d hs source coordinates visible owners materials ownerMaterial u c below state,
        Entry.InRun source visible owners materials state
          (encodeForests d (Parents.annotateForests d (source ++ [Parents.label d source coordinates]) hs)
            visible u c below state) entry := by
    cases hs with
    | nil => intro entry member; simp only [forestEntries, List.not_mem_nil] at member
    | cons h hs =>
      let a := Parents.label d source coordinates
      let withSlot := emit state (fun j => u j + 2) (c + 2) 0 below
      let withForest := encode d (Parents.annotate d (source ++ [a]) h) (visible ++ [state.length]) withSlot
      intro entry member
      simp only [forestEntries, List.mem_append] at member
      rcases member with inner | later
      · have run := entries_execution d h (source ++ [a]) (visible ++ [state.length]) (owners ++ [source.length])
          (materials ++ [ownerMaterial]) withSlot entry inner
        exact run.enclose (List.prefix_append _ _) (List.prefix_append _ _) (List.prefix_append _ _)
          (List.prefix_append _ _) (emit_extends ..) (encodeForests_extends ..)
      · have run := forestEntries_execution d hs source coordinates visible owners materials ownerMaterial
          u c below withForest entry later
        exact run.enclose (List.prefix_refl _) (List.prefix_refl _) (List.prefix_refl _) (List.prefix_refl _)
          ((emit_extends ..).trans (encode_extends ..)) (List.prefix_refl _)
end

/-- Chronology gives a state prefix, but not a lexical-context prefix:
the latter needs a separate same-scope or visible-origin argument. -/
theorem entry_states_ordered {d : Nat} {e : NumericalExpr} {source : ParentContext}
    {visible owners : List Nat} {materials : List (Forests (List Nat))} {state : State d}
    {earlier later : Entry d}
    (oldMember : earlier ∈ entries d e source visible owners materials state)
    (newMember : later ∈ entries d e source visible owners materials state)
    (before : earlier.state.length ≤ later.state.length) : earlier.state <+: later.state := by
  have oldRun := entries_execution d e source visible owners materials state earlier oldMember
  have newRun := entries_execution d e source visible owners materials state later newMember
  exact List.prefix_of_prefix_length_le (earlier.state_prefix_result.trans oldRun.resultPrefix)
    (later.state_prefix_result.trans newRun.resultPrefix) before

theorem standard_intermediate_pair_entries {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {a b j : Nat}
    (rowPositive : 0 < j) (room : j < d) (before : a < b) (inside : b < (fromSource d e).length)
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (fromSource d e)) (j - 1) a b)
    (same : Parents.parent (BMS.parentTable (d + 2) (fromSource d e)) j a =
      Parents.parent (BMS.parentTable (d + 2) (fromSource d e)) j b) :
    ∃ earlier later, earlier ∈ entries d e [] [] [] [] [] ∧ later ∈ entries d e [] [] [] [] [] ∧
      earlier.Sound ∧ later.Sound ∧ earlier.state.length = a ∧ later.state.length = b ∧
      earlier.state <+: later.state := by
  have heads := standard_intermediate_pair_heads positive standard rowPositive room before inside path same
  obtain ⟨earlier, oldMember, oldPosition, oldSound⟩ := standard_head_entry positive standard heads.1
  obtain ⟨later, newMember, newPosition, newSound⟩ := standard_head_entry positive standard heads.2
  exact ⟨earlier, later, oldMember, newMember, oldSound, newSound, oldPosition, newPosition,
    entry_states_ordered oldMember newMember (by omega)⟩

end BTnSSBMS.Encoder
