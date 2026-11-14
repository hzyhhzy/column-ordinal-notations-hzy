import BTnSSBMS.EntryExecution

/-!
Lexical origins of all currently visible source positions. The original
entry is kept even while its owner is represented by a forest slot. In
particular its first output is not identified with that slot or with its
later closing representative. These are proof-side records only.
-/
namespace BTnSSBMS.Encoder

structure Entry.OriginAt (source : ParentContext) (visible owners : List Nat)
    (materials : List (Forests (List Nat))) (state : State d) (i : Nat) (entry : Entry d) : Prop where
  sourceEq : entry.source = source.take i
  visibleEq : entry.visible = visible.take i
  materialEq : entry.materials = materials.take i
  ownersPrefix : entry.owners <+: owners
  labelEq : Parents.label d entry.source entry.coordinates = source[i]?.getD default
  attachmentEq : entry.attachments = materials[i]?.getD .nil
  statePrefix : entry.state <+: state
  beforeRepresentative : entry.state.length ≤ Parents.point visible i

structure VisibleEntries (d : Nat) (source : ParentContext) (visible owners : List Nat)
    (materials : List (Forests (List Nat))) (state : State d) (history : List (Entry d)) : Prop where
  visibleLength : visible.length = source.length
  materialLength : materials.length = source.length
  origins : ∀ i, i < source.length → ∃ entry ∈ history,
    entry.OriginAt source visible owners materials state i

theorem empty_visibleEntries (d : Nat) (state : State d) (history : List (Entry d)) :
    VisibleEntries d [] [] [] [] state history :=
  ⟨rfl, rfl, by intro i inside; simp at inside⟩

theorem Entry.OriginAt.extends {d : Nat} {source : ParentContext} {visible owners : List Nat}
    {materials : List (Forests (List Nat))} {state next : State d} {i : Nat} {entry : Entry d}
    (origin : entry.OriginAt source visible owners materials state i) (extended : state <+: next) :
    entry.OriginAt source visible owners materials next i :=
  { origin with statePrefix := origin.statePrefix.trans extended }

theorem VisibleEntries.extends {d : Nat} {source : ParentContext} {visible owners : List Nat}
    {materials : List (Forests (List Nat))} {state next : State d} {history : List (Entry d)}
    (known : VisibleEntries d source visible owners materials state history) (extended : state <+: next) :
    VisibleEntries d source visible owners materials next history := by
  refine ⟨known.visibleLength, known.materialLength, ?_⟩
  intro i inside
  obtain ⟨entry, member, origin⟩ := known.origins i inside
  exact ⟨entry, member, origin.extends extended⟩

theorem Entry.OriginAt.append {d : Nat} {source : ParentContext} {visible owners nextOwners : List Nat}
    {materials : List (Forests (List Nat))} {state : State d} {i : Nat} {entry : Entry d}
    (origin : entry.OriginAt source visible owners materials state i) (inside : i < source.length)
    (visibleLength : visible.length = source.length) (materialLength : materials.length = source.length)
    (a : ParentLabel) (hs : Forests (List Nat)) (point : Nat) (ownersPrefix : owners <+: nextOwners) :
    entry.OriginAt (source ++ [a]) (visible ++ [point]) nextOwners (materials ++ [hs]) state i := by
  have vBound : i < visible.length := by omega
  have mBound : i < materials.length := by omega
  refine ⟨?_, ?_, ?_, origin.ownersPrefix.trans ownersPrefix, ?_, ?_, origin.statePrefix, ?_⟩
  · simpa only [List.take_append_of_le_length (by omega : i ≤ source.length)] using origin.sourceEq
  · simpa only [List.take_append_of_le_length (by omega : i ≤ visible.length)] using origin.visibleEq
  · simpa only [List.take_append_of_le_length (by omega : i ≤ materials.length)] using origin.materialEq
  · simpa only [List.getElem?_append_left inside] using origin.labelEq
  · simpa only [List.getElem?_append_left mBound] using origin.attachmentEq
  · simpa only [Parents.point_append_old visible i point vBound] using origin.beforeRepresentative

/-- Append an actual entry's source position. Its representative may be
a closing column or a slot; only the true historical prefix is used. -/
theorem VisibleEntries.append_entry {d : Nat} {source : ParentContext} {visible owners nextOwners : List Nat}
    {materials : List (Forests (List Nat))} {state : State d} {history : List (Entry d)}
    (known : VisibleEntries d source visible owners materials state history) (entry : Entry d)
    (member : entry ∈ history) (sourceEq : entry.source = source) (visibleEq : entry.visible = visible)
    (materialEq : entry.materials = materials) (ownersPrefix : entry.owners <+: nextOwners)
    (retainedOwners : owners <+: nextOwners) (statePrefix : entry.state <+: state)
    (point : Nat) (beforePoint : entry.state.length ≤ point) :
    VisibleEntries d (source ++ [Parents.label d source entry.coordinates]) (visible ++ [point])
      nextOwners (materials ++ [entry.attachments]) state history := by
  refine ⟨by simp only [List.length_append, List.length_cons, List.length_nil, known.visibleLength],
    by simp only [List.length_append, List.length_cons, List.length_nil, known.materialLength], ?_⟩
  intro i inside
  by_cases old : i < source.length
  · obtain ⟨prior, found, origin⟩ := known.origins i old
    exact ⟨prior, found, origin.append old known.visibleLength known.materialLength _ _ point retainedOwners⟩
  · have last : i = source.length := by
      simp only [List.length_append, List.length_cons, List.length_nil] at inside
      omega
    subst i
    refine ⟨entry, member, ?_, ?_, ?_, ownersPrefix, ?_, ?_, statePrefix, ?_⟩
    · simpa only [List.take_left] using sourceEq
    · simpa only [← known.visibleLength, List.take_left] using visibleEq
    · simpa only [← known.materialLength, List.take_left] using materialEq
    · simp only [List.getElem?_concat_length, Option.getD_some, sourceEq]
    · simp only [← known.materialLength, List.getElem?_concat_length, Option.getD_some]
    · simpa only [← known.visibleLength, Parents.point_append_last] using beforePoint

theorem headState_first_before_last (d : Nat) (a : ParentLabel) (hs : Forests ParentLabel)
    (visible : List Nat) (state : State d) :
    state.length ≤ (headState d a hs visible state).length - 1 := by
  simp only [headState, encode]
  split
  next bound found => simp only [emit_length]; omega
  next fresh =>
    have longer := (encodeForests_extends d hs visible (vector state visible a)
      (base (smaller (frameAt state (representative visible a (d - 1)))
        (Keys.ofColumn d visible.length a hs))).height
      (smaller (frameAt state (representative visible a (d - 1))) (Keys.ofColumn d visible.length a hs))
      (emit (emit state (vector state visible a)
        ((base (smaller (frameAt state (representative visible a (d - 1)))
          (Keys.ofColumn d visible.length a hs))).height + 1) 1 [])
        (fun j => vector state visible a j + 1)
        ((base (smaller (frameAt state (representative visible a (d - 1)))
          (Keys.ofColumn d visible.length a hs))).height + 2) 2 [])).length_le
    simp only [emit_length] at longer ⊢
    omega

end BTnSSBMS.Encoder
