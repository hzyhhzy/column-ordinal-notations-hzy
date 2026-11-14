import BTnSSBMS.EntryFibers

/-! Visible lexical origins equipped with their actual numerical fibers. -/
namespace BTnSSBMS.Encoder

structure VisibleEntryFibers (d : Nat) (source : ParentContext) (visible owners : List Nat)
    (materials : List (Forests (List Nat))) (state : State d) (history : List (Entry d)) : Prop where
  visibleLength : visible.length = source.length
  materialLength : materials.length = source.length
  zero : VisibleZero state visible
  origins : ∀ i, i < source.length → ∃ entry ∈ history,
    entry.OriginAt source visible owners materials state i ∧
      NumericalFiber state entry.state.length (Parents.point visible i)

theorem empty_visibleEntryFibers (d : Nat) (state : State d) (history : List (Entry d)) :
    VisibleEntryFibers d [] [] [] [] state history :=
  ⟨rfl, rfl, by intro p member; simp at member, by intro i inside; simp at inside⟩

theorem VisibleEntryFibers.extends {d : Nat} {source : ParentContext} {visible owners : List Nat}
    {materials : List (Forests (List Nat))} {state next : State d} {history : List (Entry d)}
    (known : VisibleEntryFibers d source visible owners materials state history) (extended : state <+: next) :
    VisibleEntryFibers d source visible owners materials next history := by
  refine ⟨known.visibleLength, known.materialLength, known.zero.extends extended, ?_⟩
  intro i inside
  obtain ⟨entry, member, origin, fiber⟩ := known.origins i inside
  exact ⟨entry, member, origin.extends extended, fiber.extends extended⟩

theorem VisibleEntryFibers.append_entry {d : Nat} {source : ParentContext}
    {visible owners nextOwners : List Nat} {materials : List (Forests (List Nat))}
    {state : State d} {history : List (Entry d)}
    (known : VisibleEntryFibers d source visible owners materials state history) (entry : Entry d)
    (member : entry ∈ history) (sourceEq : entry.source = source) (visibleEq : entry.visible = visible)
    (materialEq : entry.materials = materials) (ownersPrefix : entry.owners <+: nextOwners)
    (retainedOwners : owners <+: nextOwners) (statePrefix : entry.state <+: state)
    (point : Nat) (beforePoint : entry.state.length ≤ point) (fiber : NumericalFiber state entry.state.length point)
    (zero : ∃ height, Readout state point height 0) :
    VisibleEntryFibers d (source ++ [Parents.label d source entry.coordinates]) (visible ++ [point])
      nextOwners (materials ++ [entry.attachments]) state history := by
  refine ⟨by simp only [List.length_append, List.length_cons, List.length_nil, known.visibleLength],
    by simp only [List.length_append, List.length_cons, List.length_nil, known.materialLength], ?_, ?_⟩
  · intro p member
    rcases List.mem_append.mp member with old | added
    · exact known.zero p old
    · have same : p = point := by simpa only [List.mem_singleton] using added
      exact same ▸ zero
  intro i inside
  by_cases old : i < source.length
  · obtain ⟨prior, found, origin, priorFiber⟩ := known.origins i old
    refine ⟨prior, found, origin.append old known.visibleLength known.materialLength _ _ point retainedOwners, ?_⟩
    simpa only [Parents.point_append_old visible i point (by rw [known.visibleLength]; exact old)] using priorFiber
  · have last : i = source.length := by
      simp only [List.length_append, List.length_cons, List.length_nil] at inside
      omega
    subst i
    have origin : entry.OriginAt (source ++ [Parents.label d source entry.coordinates]) (visible ++ [point])
        nextOwners (materials ++ [entry.attachments]) state source.length := by
      refine ⟨?_, ?_, ?_, ownersPrefix, ?_, ?_, statePrefix, ?_⟩
      · simpa only [List.take_left] using sourceEq
      · simpa only [← known.visibleLength, List.take_left] using visibleEq
      · simpa only [← known.materialLength, List.take_left] using materialEq
      · simp only [List.getElem?_concat_length, Option.getD_some, sourceEq]
      · simp only [← known.materialLength, List.getElem?_concat_length, Option.getD_some]
      · simpa only [← known.visibleLength, Parents.point_append_last] using beforePoint
    exact ⟨entry, member, origin,
      by simpa only [← known.visibleLength, Parents.point_append_last] using fiber⟩

theorem headState_last_readout (d : Nat) (a : ParentLabel) (hs : Forests ParentLabel)
    (visible : List Nat) (state : State d) :
    ∃ height, Readout (headState d a hs visible state)
      ((headState d a hs visible state).length - 1) height 0 := by
  simp only [headState, encode]
  split <;> simp only [emit_length, Nat.add_sub_cancel] <;> exact ⟨_, readout_emit ..⟩

end BTnSSBMS.Encoder
