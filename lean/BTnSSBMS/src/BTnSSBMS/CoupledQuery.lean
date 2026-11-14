import BTnSSBMS.ScopedFrameCoupling

/-!
The new query is made at the parent selected by the actual relocated
source head. Its attachment is the actual recursively relocated list.
Saved keys are related in the entry context, before that head is added.
-/
namespace BTnSSBMS.Encoder

theorem MaterialQuery.relocation_comparisons {d : Nat} {source target : ParentContext}
    {coordinates visible owners moved : List Nat} {materials : List (Forests (List Nat))}
    {state : State d} {hs : Forests (List Nat)}
    (query : MaterialQuery d source coordinates visible owners materials state hs)
    (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
    (targetUnit : Parents.UnitSteps d target)
    (view : Parents.NumericalView d source target moved)
    (targetWidth : ∀ i, i < target.length → (target[i]?.getD default).coordinates.length = d)
    (positive : 0 < d) :
    let a := Parents.label d source coordinates
    let newCoordinates := Source.relocationHead d source target moved coordinates
    let newA := Parents.label d target newCoordinates
    let newHs := Source.relocateForests d (source ++ [a]) (target ++ [newA]) (moved ++ [target.length]) hs
    ∀ b ∈ frameAt state (representative visible a (d - 1)),
      Keys.compare (rekeyBinding d source target visible moved materials b).key
          (queryKey d target newCoordinates newHs) = Keys.compare b.key (queryKey d source coordinates hs) := by
  dsimp only
  let a := Parents.label d source coordinates
  let newCoordinates := Source.relocationHead d source target moved coordinates
  let newA := Parents.label d target newCoordinates
  have nextView := Source.relocation_view_append query.coherent query.valid targetCoherent targetValid view coordinates
  have nextUnit := Source.relocationHead_unitSteps query.coherent query.valid targetCoherent targetValid targetUnit view coordinates
  have nextWidth : ∀ i, i < (target ++ [newA]).length →
      ((target ++ [newA])[i]?.getD default).coordinates.length = d := by
    intro i inside
    by_cases old : i < target.length
    · simpa only [List.getElem?_append_left old] using targetWidth i old
    · have last : i = target.length := by simp only [List.length_append, List.length_cons, List.length_nil] at inside; omega
      subst i
      simpa only [List.getElem?_concat_length, Option.getD_some, newA, Parents.label] using
        Source.relocationHead_width d source target moved coordinates
  intro b member
  have compared := rekey_queried_binding_compare query.inherited query.view query.coherent query.valid
    query.unit (Parents.coherent_append_label targetCoherent newCoordinates)
    (Parents.context_valid_append_label d target targetValid newCoordinates) nextUnit nextView nextWidth
    positive query.width hs query.legal b member
  have stable := rekeyBinding_prefix query.view view query.inherited.materialContext.length
    (List.prefix_append source [a]) (List.prefix_append target [newA]) (List.prefix_refl visible)
    (List.prefix_append moved [target.length]) (List.prefix_refl materials) b (query.inherited.keys b member)
  rw [stable] at compared
  simpa only [movedQueryKey, List.length_append, List.length_cons, List.length_nil,
    Nat.add_sub_cancel, Keys.atContext_append, queryKey] using compared

/-- Both lists are read from the real encoder states at the actual
highest numerical parents. No mapped-frame execution is assumed. -/
theorem CoupledFrames.query_tests {d : Nat} {source target : ParentContext}
    {coordinates visible nextVisible owners moved : List Nat} {materials : List (Forests (List Nat))}
    {state next : State d} {hs : Forests (List Nat)}
    (related : CoupledFrames d source target moved visible nextVisible materials state next)
    (query : MaterialQuery d source coordinates visible owners materials state hs)
    (newView : Parents.NumericalView d target (BMS.parentTable (d + 2) (matrix next)) nextVisible)
    (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
    (targetUnit : Parents.UnitSteps d target) (view : Parents.NumericalView d source target moved)
    (targetWidth : ∀ i, i < target.length → (target[i]?.getD default).coordinates.length = d)
    (positive : 0 < d) :
    let a := Parents.label d source coordinates
    let newCoordinates := Source.relocationHead d source target moved coordinates
    let newA := Parents.label d target newCoordinates
    let newHs := Source.relocateForests d (source ++ [a]) (target ++ [newA]) (moved ++ [target.length]) hs
    let frame := frameAt state (representative visible a (d - 1))
    let newFrame := frameAt next (representative nextVisible newA (d - 1))
    let key := queryKey d source coordinates hs
    let newKey := queryKey d target newCoordinates newHs
    let keyOf := fun b => (rekeyBinding d source target visible moved materials b).key
    KeyFrameRel keyOf (smaller frame key) (smaller newFrame newKey) ∧
      firstHeight newFrame newKey = firstHeight frame key ∧
      (match equal frame key with
      | none => equal newFrame newKey = none
      | some old => ∃ new, equal newFrame newKey = some new ∧ KeyBindingRel keyOf old new) := by
  have frames := related.queried query.view newView view query.coherent query.valid targetCoherent targetValid positive coordinates
  have comparisons := query.relocation_comparisons targetCoherent targetValid targetUnit view targetWidth positive
  exact ⟨frames.smaller _ _ comparisons, frames.firstHeight _ _ comparisons, frames.equal_cases _ _ comparisons⟩

end BTnSSBMS.Encoder
