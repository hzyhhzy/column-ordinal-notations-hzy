import BTnSSBMS.ClosingFrameExtension

/-!
A visible non-owner is represented by its original entry's closing
column, not merely by some point after that entry's first output.
Open owners are explicitly excluded: their current representatives are
forest slots. The proof follows the complete actual execution trace.
-/
namespace BTnSSBMS.Encoder

structure VisibleClosingOrigins (d : Nat) (source : ParentContext) (visible owners : List Nat)
    (materials : List (Forests (List Nat))) (state : State d) (history : List (Entry d)) : Prop
    extends VisibleEntries d source visible owners materials state history where
  closed : ∀ i, i < source.length → i ∉ owners → ∃ entry ∈ history,
    entry.OriginAt source visible owners materials state i ∧ entry.closing = Parents.point visible i

theorem empty_visibleClosingOrigins (d : Nat) (state : State d) (history : List (Entry d)) :
    VisibleClosingOrigins d [] [] [] [] state history :=
  ⟨empty_visibleEntries d state history, by intro i inside; simp at inside⟩

theorem VisibleClosingOrigins.extends {d : Nat} {source : ParentContext} {visible owners : List Nat}
    {materials : List (Forests (List Nat))} {state next : State d} {history : List (Entry d)}
    (known : VisibleClosingOrigins d source visible owners materials state history) (initial : state <+: next) :
    VisibleClosingOrigins d source visible owners materials next history := by
  refine ⟨known.toVisibleEntries.extends initial, ?_⟩
  intro i inside free
  obtain ⟨entry, member, origin, closes⟩ := known.closed i inside free
  exact ⟨entry, member, origin.extends initial, closes⟩

theorem VisibleClosingOrigins.append_entry {d : Nat} {source : ParentContext}
    {visible owners nextOwners : List Nat} {materials : List (Forests (List Nat))}
    {state : State d} {history : List (Entry d)}
    (known : VisibleClosingOrigins d source visible owners materials state history) (entry : Entry d)
    (member : entry ∈ history) (sourceEq : entry.source = source) (visibleEq : entry.visible = visible)
    (materialEq : entry.materials = materials) (ownersPrefix : entry.owners <+: nextOwners)
    (retainedOwners : owners <+: nextOwners) (statePrefix : entry.state <+: state)
    (point : Nat) (beforePoint : entry.state.length ≤ point)
    (closes : source.length ∉ nextOwners → point = entry.closing) :
    VisibleClosingOrigins d (source ++ [Parents.label d source entry.coordinates]) (visible ++ [point])
      nextOwners (materials ++ [entry.attachments]) state history := by
  have allOrigins := known.toVisibleEntries.append_entry entry member sourceEq visibleEq materialEq
    ownersPrefix retainedOwners statePrefix point beforePoint
  refine ⟨allOrigins, ?_⟩
  intro i inside free
  by_cases old : i < source.length
  · have oldFree : i ∉ owners := fun found => free (retainedOwners.subset found)
    obtain ⟨prior, found, origin, closed⟩ := known.closed i old oldFree
    refine ⟨prior, found, origin.append old known.visibleLength known.materialLength _ _ point retainedOwners, ?_⟩
    simpa only [Parents.point_append_old visible i point (by rw [known.visibleLength]; exact old)] using closed
  · have last : i = source.length := by
      simp only [List.length_append, List.length_cons, List.length_nil] at inside
      omega
    subst i
    refine ⟨entry, member, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ownersPrefix, ?_, ?_, statePrefix, ?_⟩
      · simpa only [List.take_left] using sourceEq
      · simpa only [← known.visibleLength, List.take_left] using visibleEq
      · simpa only [← known.materialLength, List.take_left] using materialEq
      · simp only [List.getElem?_concat_length, Option.getD_some, sourceEq]
      · simp only [← known.materialLength, List.getElem?_concat_length, Option.getD_some]
      · simpa only [← known.visibleLength, Parents.point_append_last] using beforePoint
    · simpa only [← known.visibleLength, Parents.point_append_last] using (closes free).symm

mutual
  theorem entries_closingOrigins (d : Nat) (e : NumericalExpr) (source : ParentContext)
      (visible owners : List Nat) (materials : List (Forests (List Nat))) (state : State d)
      (history : List (Entry d)) (known : VisibleClosingOrigins d source visible owners materials state history)
      (included : ∀ entry ∈ entries d e source visible owners materials state, entry ∈ history) :
      ∀ entry ∈ entries d e source visible owners materials state,
        VisibleClosingOrigins d entry.source entry.visible entry.owners entry.materials entry.state history := by
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
      have headedKnown : VisibleClosingOrigins d (source ++ [a]) (visible ++ [headed.length - 1]) owners
          (materials ++ [hs]) headed history :=
        (known.extends headPrefix).append_entry current currentMember rfl rfl rfl
          (List.prefix_refl _) (List.prefix_refl _) headPrefix (headed.length - 1)
          (headState_first_before_last d a annotated visible state) (fun _ => rfl)
      have tailIncluded : ∀ entry ∈ entries d tail (source ++ [a]) (visible ++ [headed.length - 1])
          owners (materials ++ [hs]) headed, entry ∈ history := by
        intro entry member
        apply included entry
        simp only [entries, List.mem_cons, List.mem_append]
        exact .inr (.inr member)
      have tailOrigins := entries_closingOrigins d tail (source ++ [a]) (visible ++ [headed.length - 1])
        owners (materials ++ [hs]) headed history headedKnown tailIncluded
      have innerOrigins : ∀ entry ∈ (match equal frame key with
          | some _ => []
          | none => forestEntries d hs source coordinates visible owners materials hs u c below guarded),
          VisibleClosingOrigins d entry.source entry.visible entry.owners entry.materials entry.state history := by
        cases found : equal frame key with
        | some bound => intro entry member; simp only [List.not_mem_nil] at member
        | none =>
          have guardPrefix : state <+: guarded := (emit_extends ..).trans (emit_extends ..)
          apply forestEntries_closingOrigins d hs current u c below guarded history (known.extends guardPrefix)
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

  theorem forestEntries_closingOrigins (d : Nat) (hs : Forests (List Nat)) (owner : Entry d)
      (u : Nat → Nat) (c : Nat) (below : List Binding) (state : State d) (history : List (Entry d))
      (known : VisibleClosingOrigins d owner.source owner.visible owner.owners owner.materials state history)
      (ownerMember : owner ∈ history) (ownerPrefix : owner.state <+: state)
      (included : ∀ entry ∈ forestEntries d hs owner.source owner.coordinates owner.visible owner.owners
        owner.materials owner.attachments u c below state, entry ∈ history) :
      ∀ entry ∈ forestEntries d hs owner.source owner.coordinates owner.visible owner.owners
          owner.materials owner.attachments u c below state,
        VisibleClosingOrigins d entry.source entry.visible entry.owners entry.materials entry.state history := by
    cases hs with
    | nil => intro entry member; simp only [forestEntries, List.not_mem_nil] at member
    | cons h hs =>
      let a := Parents.label d owner.source owner.coordinates
      let withSlot := emit state (fun j => u j + 2) (c + 2) 0 below
      let withForest := encode d (Parents.annotate d (owner.source ++ [a]) h)
        (owner.visible ++ [state.length]) withSlot
      have slotKnown : VisibleClosingOrigins d (owner.source ++ [a]) (owner.visible ++ [state.length])
          (owner.owners ++ [owner.source.length]) (owner.materials ++ [owner.attachments]) withSlot history :=
        (known.extends (emit_extends ..)).append_entry owner ownerMember rfl rfl rfl
          (List.prefix_append _ _) (List.prefix_append _ _) (ownerPrefix.trans (emit_extends ..))
          state.length ownerPrefix.length_le (fun free => False.elim (free (by simp)))
      have innerIncluded : ∀ entry ∈ entries d h (owner.source ++ [a]) (owner.visible ++ [state.length])
          (owner.owners ++ [owner.source.length]) (owner.materials ++ [owner.attachments]) withSlot,
          entry ∈ history := by
        intro entry member
        exact included entry (List.mem_append_left _ member)
      have innerOrigins := entries_closingOrigins d h (owner.source ++ [a]) (owner.visible ++ [state.length])
        (owner.owners ++ [owner.source.length]) (owner.materials ++ [owner.attachments]) withSlot history
        slotKnown innerIncluded
      have forestPrefix : state <+: withForest := (emit_extends ..).trans (encode_extends ..)
      have tailIncluded : ∀ entry ∈ forestEntries d hs owner.source owner.coordinates owner.visible owner.owners
          owner.materials owner.attachments u c below withForest, entry ∈ history := by
        intro entry member
        exact included entry (List.mem_append_right _ member)
      have tailOrigins := forestEntries_closingOrigins d hs owner u c below withForest history
        (known.extends forestPrefix) ownerMember (ownerPrefix.trans forestPrefix) tailIncluded
      intro entry member
      simp only [forestEntries, List.mem_append] at member
      rcases member with inner | later
      · exact innerOrigins entry inner
      · exact tailOrigins entry later
end

theorem source_entries_closingOrigins (d : Nat) (e : NumericalExpr) :
    ∀ entry ∈ entries d e [] [] [] [] [],
      VisibleClosingOrigins d entry.source entry.visible entry.owners entry.materials entry.state
        (entries d e [] [] [] [] []) :=
  entries_closingOrigins d e [] [] [] [] [] (entries d e [] [] [] [] [])
    (empty_visibleClosingOrigins d [] _) (fun _ member => member)

/-- Exact closing-column source correspondence for the P/P case of a
highest-row pair. Both endpoints are the actual closing positions of
the returned entries, and the old entry is visible and not an owner in
the later entry's active source context. -/
theorem standard_closing_pair_origin {d : Nat} (positive : 0 < d) {e : NumericalExpr}
    (standard : Source.Standard d e) {later : Entry d}
    (member : later ∈ entries d e [] [] [] [] []) {position : Nat}
    (self : SelfLatest (encode d (Parents.annotate d [] e) [] []) position)
    (before : position < later.closing)
    (path : Parents.Ancestor (BMS.parentTable (d + 2) (fromSource d e)) d position later.closing) :
    ∃ root earlier, root < later.source.length ∧ root ∉ later.owners ∧
      earlier ∈ entries d e [] [] [] [] [] ∧
      earlier.OriginAt later.source later.visible later.owners later.materials later.state root ∧
      earlier.closing = position ∧ position = Parents.point later.visible root ∧
      Parents.Ancestor (later.source ++ [Parents.label d later.source later.coordinates])
        (d - 1) root later.source.length := by
  obtain ⟨root, inside, free, named, ancestry⟩ :=
    standard_closing_ancestor_source positive standard member self before path
  obtain ⟨earlier, oldMember, origin, closes⟩ :=
    (source_entries_closingOrigins d e later member).closed root inside free
  exact ⟨root, earlier, inside, free, oldMember, origin, closes.trans named.symm, named, ancestry⟩

end BTnSSBMS.Encoder
