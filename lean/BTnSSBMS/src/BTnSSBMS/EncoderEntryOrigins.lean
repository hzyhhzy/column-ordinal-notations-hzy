import BTnSSBMS.EntryOrigins

/-!
All visible origins are produced by the actual recursive trace. Forests
install the original owner's snapshot at each slot and restore the outer
scope on exit. No assumption identifies chronological and lexical order.
-/
namespace BTnSSBMS.Encoder

mutual
  theorem entries_origins (d : Nat) (e : NumericalExpr) (source : ParentContext)
      (visible owners : List Nat) (materials : List (Forests (List Nat))) (state : State d)
      (history : List (Entry d)) (known : VisibleEntries d source visible owners materials state history)
      (included : ∀ entry ∈ entries d e source visible owners materials state, entry ∈ history) :
      ∀ entry ∈ entries d e source visible owners materials state,
        VisibleEntries d entry.source entry.visible entry.owners entry.materials entry.state history := by
    cases e with
    | nil => intro entry member; simp only [entries, List.not_mem_nil] at member
    | cons coordinates hs tail =>
      let current : Entry d := ⟨source, coordinates, hs, tail, visible, owners, materials, state⟩
      let a := Parents.label d source coordinates
      let annotated := Parents.annotateForests d (source ++ [a]) hs
      let key := Keys.ofColumn d visible.length a annotated
      let frame := frameAt state (representative visible a (d - 1))
      let below := smaller frame key
      let c := (base below).height
      let u := vector state visible a
      let headed := headState d a annotated visible state
      let guarded := emit (emit state u (c + 1) 1 []) (fun j => u j + 1) (c + 2) 2 []
      have currentMember : current ∈ history := included current (List.mem_cons_self)
      have headPrefix : state <+: headed := encode_extends ..
      have headedKnown : VisibleEntries d (source ++ [a]) (visible ++ [headed.length - 1]) owners
          (materials ++ [hs]) headed history :=
        (known.extends headPrefix).append_entry current currentMember rfl rfl rfl
          (List.prefix_refl _) (List.prefix_refl _) headPrefix (headed.length - 1)
          (headState_first_before_last d a annotated visible state)
      have tailIncluded : ∀ entry ∈ entries d tail (source ++ [a]) (visible ++ [headed.length - 1])
          owners (materials ++ [hs]) headed, entry ∈ history := by
        intro entry member
        apply included entry
        simp only [entries, List.mem_cons, List.mem_append]
        exact .inr (.inr member)
      have tailOrigins := entries_origins d tail (source ++ [a]) (visible ++ [headed.length - 1])
        owners (materials ++ [hs]) headed history headedKnown tailIncluded
      have innerOrigins : ∀ entry ∈ (match equal frame key with
          | some _ => []
          | none => forestEntries d hs source coordinates visible owners materials hs u c below guarded),
          VisibleEntries d entry.source entry.visible entry.owners entry.materials entry.state history := by
        cases found : equal frame key with
        | some bound => intro entry member; simp only [List.not_mem_nil] at member
        | none =>
          have guardPrefix : state <+: guarded := (emit_extends ..).trans (emit_extends ..)
          apply forestEntries_origins d hs current u c below guarded history (known.extends guardPrefix)
            currentMember guardPrefix
          intro entry member
          apply included entry
          dsimp only [frame, key, a, annotated] at found
          simp only [entries, found, List.mem_cons, List.mem_append]
          exact .inr (.inl member)
      intro entry member
      simp only [entries, List.mem_cons, List.mem_append] at member
      rcases member with rfl | inner | later
      · exact known
      · exact innerOrigins entry inner
      · exact tailOrigins entry later

  theorem forestEntries_origins (d : Nat) (hs : Forests (List Nat)) (owner : Entry d)
      (u : Nat → Nat) (c : Nat) (below : List Binding) (state : State d) (history : List (Entry d))
      (known : VisibleEntries d owner.source owner.visible owner.owners owner.materials state history)
      (ownerMember : owner ∈ history) (ownerPrefix : owner.state <+: state)
      (included : ∀ entry ∈ forestEntries d hs owner.source owner.coordinates owner.visible owner.owners
        owner.materials owner.attachments u c below state, entry ∈ history) :
      ∀ entry ∈ forestEntries d hs owner.source owner.coordinates owner.visible owner.owners
          owner.materials owner.attachments u c below state,
        VisibleEntries d entry.source entry.visible entry.owners entry.materials entry.state history := by
    cases hs with
    | nil => intro entry member; simp only [forestEntries, List.not_mem_nil] at member
    | cons h hs =>
      let a := Parents.label d owner.source owner.coordinates
      let withSlot := emit state (fun j => u j + 2) (c + 2) 0 below
      let withForest := encode d (Parents.annotate d (owner.source ++ [a]) h)
        (owner.visible ++ [state.length]) withSlot
      have slotKnown : VisibleEntries d (owner.source ++ [a]) (owner.visible ++ [state.length])
          (owner.owners ++ [owner.source.length]) (owner.materials ++ [owner.attachments]) withSlot history :=
        (known.extends (emit_extends ..)).append_entry owner ownerMember rfl rfl rfl
          (List.prefix_append _ _) (List.prefix_append _ _) (ownerPrefix.trans (emit_extends ..))
          state.length ownerPrefix.length_le
      have innerIncluded : ∀ entry ∈ entries d h (owner.source ++ [a]) (owner.visible ++ [state.length])
          (owner.owners ++ [owner.source.length]) (owner.materials ++ [owner.attachments]) withSlot,
          entry ∈ history := by
        intro entry member
        exact included entry (List.mem_append_left _ member)
      have innerOrigins := entries_origins d h (owner.source ++ [a]) (owner.visible ++ [state.length])
        (owner.owners ++ [owner.source.length]) (owner.materials ++ [owner.attachments]) withSlot history
        slotKnown innerIncluded
      have forestPrefix : state <+: withForest := (emit_extends ..).trans (encode_extends ..)
      have tailIncluded : ∀ entry ∈ forestEntries d hs owner.source owner.coordinates owner.visible owner.owners
          owner.materials owner.attachments u c below withForest, entry ∈ history := by
        intro entry member
        exact included entry (List.mem_append_right _ member)
      have tailOrigins := forestEntries_origins d hs owner u c below withForest history
        (known.extends forestPrefix) ownerMember (ownerPrefix.trans forestPrefix) tailIncluded
      intro entry member
      simp only [forestEntries, List.mem_append] at member
      rcases member with inner | later
      · exact innerOrigins entry inner
      · exact tailOrigins entry later
end

/-- The origin of every visible position is an actual earlier entry,
including open owners represented by slots. This is true of all finite
inputs and does not rely on a well-ordering assertion. -/
theorem source_entries_origins (d : Nat) (e : NumericalExpr) :
    ∀ entry ∈ entries d e [] [] [] [] [],
      VisibleEntries d entry.source entry.visible entry.owners entry.materials entry.state
        (entries d e [] [] [] [] []) :=
  entries_origins d e [] [] [] [] [] (entries d e [] [] [] [] [])
    (empty_visibleEntries d [] _) (fun _ member => member)

theorem standard_visible_entry_origin {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {later : Entry d}
    (laterMember : later ∈ entries d e [] [] [] [] []) {i : Nat} (inside : i < later.source.length) :
    ∃ earlier, earlier ∈ entries d e [] [] [] [] [] ∧ earlier.Sound ∧
      earlier.OriginAt later.source later.visible later.owners later.materials later.state i := by
  obtain ⟨earlier, member, origin⟩ := (source_entries_origins d e later laterMember).origins i inside
  exact ⟨earlier, member, standard_entries_sound positive standard earlier member, origin⟩

end BTnSSBMS.Encoder
