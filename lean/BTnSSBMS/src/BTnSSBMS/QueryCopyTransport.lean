import BTnSSBMS.QueryMaterialTransport
import BTnSSBMS.CopyKeyComparison

/-!
The saved-material query results specialized to the frozen literal copy.
Earlier material inside the copy is actually copied in its restricted
entry; earlier material in a fixed external prefix is unchanged. Lists
replaced by a hole or by donation are not covered by this ordinary-copy
result, and the new frame still has to be identified in the full encoder.
-/
namespace BTnSSBMS.Encoder

theorem MaterialQuery.rekey_same_copy {d : Nat} {source target : ParentContext}
    {coordinates visible owners moved history : List Nat} {materials : List (Forests (List Nat))}
    {state : State d} {hs : Forests (List Nat)} {root cap phase : Nat} {delta : List Nat}
    (query : MaterialQuery d source coordinates visible owners materials state hs)
    (scope : Source.ShiftView d (source ++ [Parents.label d source coordinates]) target
      moved history root cap delta phase)
    (b : Binding)
    (member : b ∈ frameAt state (representative visible (Parents.label d source coordinates) (d - 1)))
    (p : Nat) (latest : b.latest = some p) (insideCopy : root ≤ visible.idxOf p) :
    let i := visible.idxOf p
    (rekeyBinding d (source ++ [Parents.label d source coordinates]) target visible moved materials b).key =
      Keys.atContext d target (Parents.point moved i)
        (Source.copiedForests d root cap delta phase
          ((source ++ [Parents.label d source coordinates]).take (i + 1)) (history.take (i + 1))
          (materials[i]?.getD .nil)) := by
  obtain ⟨i, inside, _, named, _, _, _, legal⟩ := query.inherited.origin query.view b member p latest
  have inverse : visible.idxOf p = i := by rw [named]; exact query.view.idxOf_point inside
  rw [inverse] at insideCopy ⊢
  have restricted := scope.prefix_at i (by simp; omega) insideCopy
  have samePrefix : (source ++ [Parents.label d source coordinates]).take (i + 1) = source.take (i + 1) :=
    List.take_append_of_le_length (by omega)
  have copied := Source.relocateForests_eq_copied restricted (Parents.reading source 0 i)
    (materials[i]?.getD .nil) (by rw [samePrefix]; exact legal)
  simp only [rekeyBinding, latest, inverse, transportedMaterialKey]
  rw [copied]

theorem MaterialQuery.rekey_fixed_external {d : Nat} {source target : ParentContext}
    {coordinates visible owners moved history : List Nat} {materials : List (Forests (List Nat))}
    {state : State d} {hs : Forests (List Nat)} {root cap phase : Nat} {delta : List Nat}
    (query : MaterialQuery d source coordinates visible owners materials state hs)
    (scope : Source.ShiftView d (source ++ [Parents.label d source coordinates]) target
      moved history root cap delta phase)
    (fixedPrefix : target.take root = (source ++ [Parents.label d source coordinates]).take root)
    (fixedPositions : moved.take root = List.range root)
    (b : Binding)
    (member : b ∈ frameAt state (representative visible (Parents.label d source coordinates) (d - 1)))
    (p : Nat) (latest : b.latest = some p) (outsideCopy : visible.idxOf p < root) :
    (rekeyBinding d (source ++ [Parents.label d source coordinates]) target visible moved materials b).key = b.key := by
  obtain ⟨i, inside, _, named, _, key, _, legal⟩ := query.inherited.origin query.view b member p latest
  have inverse : visible.idxOf p = i := by rw [named]; exact query.view.idxOf_point inside
  rw [inverse] at outsideCopy
  let entry := source ++ [Parents.label d source coordinates]
  have shortPrefix : target.take (i + 1) = entry.take (i + 1) := by
    have short := congrArg (List.take (i + 1)) fixedPrefix
    simpa only [List.take_take, Nat.min_eq_left (by omega : i + 1 ≤ root)] using short
  have shortPositions : moved.take (i + 1) = List.range (i + 1) := by
    have short := congrArg (List.take (i + 1)) fixedPositions
    simpa only [List.take_take, List.take_range, Nat.min_eq_left (by omega : i + 1 ≤ root)] using short
  have point : Parents.point moved i = i := by
    rw [← Parents.point_take moved (i + 1) i (by omega), shortPositions,
      Parents.point_range (i + 1) i (by omega)]
  have label : target[i]?.getD default = entry[i]?.getD default := by
    have value := congrArg (fun context : ParentContext => context[i]?.getD default) shortPrefix
    simpa only [List.getElem?_take_of_lt (by omega : i < i + 1)] using value
  have samePrefix : entry.take (i + 1) = source.take (i + 1) :=
    List.take_append_of_le_length (by omega)
  have prefixLength : (entry.take (i + 1)).length = i + 1 := by
    simp only [entry, List.length_take, List.length_append, List.length_cons, List.length_nil]
    omega
  have identity := Source.relocateForests_same_context
    (scope.sourceCoherent.restrict (List.take_prefix ..))
    (scope.sourceValid.restrict (List.take_prefix ..))
    (query.unit.restrict scope.sourceValid (List.take_prefix ..)) (by rw [prefixLength]; omega)
    (Parents.reading source 0 i) (materials[i]?.getD .nil) (by rw [samePrefix]; exact legal)
  rw [prefixLength] at identity
  have targetKey : Keys.atContext d target i (materials[i]?.getD .nil) =
      Keys.atContext d entry i (materials[i]?.getD .nil) := by
    simp only [Keys.atContext, label, shortPrefix]
  simp only [rekeyBinding, latest, inverse, transportedMaterialKey]
  rw [point, shortPrefix, shortPositions, identity, targetKey,
    Keys.atContext_prefix d (List.prefix_append source _) inside, ← key]

/-- The current query is also the actual activation-and-shift copy,
not just the auxiliary canonical relocation. The initial frame is the
one that the original encoder really reads. -/
theorem MaterialQuery.copied_tests {d : Nat} {source target : ParentContext}
    {coordinates visible owners moved history : List Nat} {materials : List (Forests (List Nat))}
    {state : State d} {hs : Forests (List Nat)} {root cap phase : Nat} {delta : List Nat}
    (query : MaterialQuery d source coordinates visible owners materials state hs)
    (scope : Source.ShiftView d (source ++ [Parents.label d source coordinates]) target
      moved history root cap delta phase)
    (targetWidth : ∀ i, i < target.length → (target[i]?.getD default).coordinates.length = d)
    (positive : 0 < d) :
    let frame := frameAt state (representative visible (Parents.label d source coordinates) (d - 1))
    let key := Keys.ofColumn d visible.length (Parents.label d source coordinates)
      (Parents.annotateForests d (source ++ [Parents.label d source coordinates]) hs)
    let f := rekeyBinding d (source ++ [Parents.label d source coordinates]) target visible moved materials
    let newKey := Keys.atContext d target (target.length - 1)
      (Source.copiedForests d root cap delta phase (source ++ [Parents.label d source coordinates]) history hs)
    smaller (frame.map f) newKey = (smaller frame key).map f ∧
      equal (frame.map f) newKey = (equal frame key).map f := by
  have result := query.rekey_tests scope.targetCoherent scope.targetValid scope.targetUnit scope.view targetWidth positive
  dsimp only [movedQueryKey] at result
  rw [Source.relocateForests_eq_copied scope (coordinates[0]?.getD 0) hs query.legal] at result
  exact result

theorem MaterialQuery.copied_firstHeight {d : Nat} {source target : ParentContext}
    {coordinates visible owners moved history : List Nat} {materials : List (Forests (List Nat))}
    {state : State d} {hs : Forests (List Nat)} {root cap phase : Nat} {delta : List Nat}
    (query : MaterialQuery d source coordinates visible owners materials state hs)
    (scope : Source.ShiftView d (source ++ [Parents.label d source coordinates]) target
      moved history root cap delta phase)
    (targetWidth : ∀ i, i < target.length → (target[i]?.getD default).coordinates.length = d)
    (positive : 0 < d) :
    let frame := frameAt state (representative visible (Parents.label d source coordinates) (d - 1))
    let key := Keys.ofColumn d visible.length (Parents.label d source coordinates)
      (Parents.annotateForests d (source ++ [Parents.label d source coordinates]) hs)
    let f := rekeyBinding d (source ++ [Parents.label d source coordinates]) target visible moved materials
    firstHeight (frame.map f) (Keys.atContext d target (target.length - 1)
      (Source.copiedForests d root cap delta phase (source ++ [Parents.label d source coordinates]) history hs)) =
      firstHeight frame key := by
  have result := query.rekey_firstHeight scope.targetCoherent scope.targetValid scope.targetUnit scope.view targetWidth positive
  dsimp only [movedQueryKey] at result
  rw [Source.relocateForests_eq_copied scope (coordinates[0]?.getD 0) hs query.legal] at result
  exact result

end BTnSSBMS.Encoder
