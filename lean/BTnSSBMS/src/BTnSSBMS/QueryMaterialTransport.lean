import BTnSSBMS.EncoderBindingMaterials

/-!
Recompute saved keys from their actual source attachment lists after a
numerical transport. The old frame's actual equality and smaller-key
tests then commute with this recomputation. This is not yet a claim that
the entire new encoder execution produces that recomputed frame.
-/
namespace BTnSSBMS.Parents

theorem NumericalView.idxOf_point {d : Nat} {source target : ParentContext} {visible : List Nat}
    (view : NumericalView d source target visible) {i : Nat} (inside : i < source.length) :
    visible.idxOf (point visible i) = i := by
  have bound : i < visible.length := by rw [view.length]; exact inside
  have member : point visible i ∈ visible := by
    simpa only [point, List.getElem?_eq_getElem bound, Option.getD_some] using
      (List.getElem_mem bound)
  have indexBound := List.idxOf_lt_length_of_mem member
  have indexSource : visible.idxOf (point visible i) < source.length := by rw [← view.length]; exact indexBound
  have value : point visible (visible.idxOf (point visible i)) = point visible i := by
    change visible[visible.idxOf (point visible i)]?.getD 0 = point visible i
    rw [List.getElem?_eq_getElem indexBound, Option.getD_some]
    exact List.getElem_idxOf indexBound
  by_cases smaller : visible.idxOf (point visible i) < i
  · have strict := view.increasing _ i smaller inside
    omega
  · by_cases larger : i < visible.idxOf (point visible i)
    · have strict := view.increasing i _ larger indexSource
      omega
    · omega

end BTnSSBMS.Parents

namespace BTnSSBMS.Encoder

def transportedMaterialKey (d : Nat) (source target : ParentContext) (moved : List Nat)
    (materials : List (Forests (List Nat))) (i : Nat) : Key :=
  Keys.atContext d target (Parents.point moved i)
    (Source.relocateForests d (source.take (i + 1)) (target.take (Parents.point moved i + 1))
      (moved.take (i + 1)) (materials[i]?.getD .nil))

/-- Only the complete key is recomputed. Height and pointer fields here
are deliberately left unchanged; this is an environment comparison tool,
not the claimed transported encoder state. -/
def rekeyBinding (d : Nat) (source target : ParentContext) (visible moved : List Nat)
    (materials : List (Forests (List Nat))) (b : Binding) : Binding :=
  match b.latest with
  | none => b
  | some p => {b with key := transportedMaterialKey d source target moved materials (visible.idxOf p)}

def queryKey (d : Nat) (source : ParentContext) (coordinates : List Nat)
    (hs : Forests (List Nat)) : Key :=
  Keys.ofColumn d source.length (Parents.label d source coordinates)
    (Parents.annotateForests d (source ++ [Parents.label d source coordinates]) hs)

def movedQueryKey (d : Nat) (source target : ParentContext) (coordinates moved : List Nat)
    (hs : Forests (List Nat)) : Key :=
  Keys.atContext d target (target.length - 1)
    (Source.relocateForests d (source ++ [Parents.label d source coordinates]) target moved hs)

theorem rekeyBinding_height (d : Nat) (source target : ParentContext) (visible moved : List Nat)
    (materials : List (Forests (List Nat))) (b : Binding) :
    (rekeyBinding d source target visible moved materials b).height = b.height := by
  unfold rekeyBinding
  split <;> rfl

/-- All inputs are explicit finite numerical conditions and actual
material provenance. No key comparison or branch preservation is an
assumption. The source attachment may have arbitrary finite depth. -/
theorem rekey_queried_binding_compare {d : Nat} {source oldTarget target : ParentContext}
    {coordinates visible owners moved : List Nat} {materials : List (Forests (List Nat))}
    {frame : List Binding}
    (known : InheritedMaterials d source coordinates visible owners materials frame)
    (oldView : Parents.NumericalView d source oldTarget visible)
    (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
    (sourceUnit : Parents.UnitSteps d (source ++ [Parents.label d source coordinates]))
    (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
    (targetUnit : Parents.UnitSteps d target)
    (view : Parents.NumericalView d (source ++ [Parents.label d source coordinates]) target moved)
    (targetWidth : ∀ i, i < target.length → (target[i]?.getD default).coordinates.length = d)
    (positive : 0 < d) (width : coordinates.length = d) (hs : Forests (List Nat))
    (legal : Source.FiniteLegalForests d (source ++ [Parents.label d source coordinates])
      (coordinates[0]?.getD 0) hs)
    (b : Binding) (member : b ∈ frame) :
    Keys.compare
      (rekeyBinding d (source ++ [Parents.label d source coordinates]) target visible moved materials b).key
      (movedQueryKey d source target coordinates moved hs) =
      Keys.compare b.key (queryKey d source coordinates hs) := by
  cases latest : b.latest with
  | none =>
    have empty := known.keys b member
    simp only [BindingMaterial, latest] at empty
    simp only [rekeyBinding, latest]
    rw [empty]
    cases hs <;> rfl
  | some p =>
    obtain ⟨i, inside, _, named, path, key, oldWidth, oldLegal⟩ := known.origin oldView b member p latest
    have inverse : visible.idxOf p = i := by rw [named]; exact oldView.idxOf_point inside
    let entry := source ++ [Parents.label d source coordinates]
    have entryLength : entry.length = source.length + 1 := by simp only [entry, List.length_append,
      List.length_cons, List.length_nil]
    have last : entry.length - 1 = source.length := by omega
    have prefixSame : entry.take (i + 1) = source.take (i + 1) :=
      List.take_append_of_le_length (by omega)
    have entryWidth : (entry[i]?.getD default).coordinates.length = d := by
      simpa only [entry, List.getElem?_append_left inside] using oldWidth
    have entryLastWidth : (entry[entry.length - 1]?.getD default).coordinates.length = d := by
      rw [last]
      simpa only [entry, List.getElem?_concat_length, Option.getD_some, Parents.label] using width
    have entryLegal : Source.FiniteLegalForests d (entry.take (i + 1)) (Parents.reading entry 0 i)
        (materials[i]?.getD .nil) := by
      rw [prefixSame, ← Parents.reading_prefix (List.prefix_append source _) 0 i inside]
      exact oldLegal
    have currentLegal : Source.FiniteLegalForests d entry (Parents.reading entry 0 (entry.length - 1)) hs := by
      rw [last, Parents.reading_append_label]
      exact legal
    have targetLast : target.length - 1 < target.length := by
      have frontier := view.frontier (by simp)
      omega
    have compared := Source.relocated_ancestor_key_compare (source := entry)
      (Parents.coherent_append_label sourceCoherent coordinates)
      (Parents.context_valid_append_label d source sourceValid coordinates) sourceUnit
      targetCoherent targetValid targetUnit view positive (by rw [last]; exact inside) (by rw [last]; exact path)
      entryWidth entryLastWidth (targetWidth _ (view.bounded i (by simp; omega)))
      (targetWidth _ targetLast) (materials[i]?.getD .nil) hs entryLegal currentLegal
    rw [last, Keys.atContext_prefix d (List.prefix_append source _) inside,
      Keys.atContext_append, ← key] at compared
    simpa only [rekeyBinding, latest, inverse, transportedMaterialKey, movedQueryKey, queryKey] using compared

private theorem filter_map_compare (frame : List Binding) (f : Binding → Binding) (oldKey newKey : Key)
    (comparisons : ∀ b ∈ frame, Keys.compare (f b).key newKey = Keys.compare b.key oldKey) :
    smaller (frame.map f) newKey = (smaller frame oldKey).map f := by
  induction frame with
  | nil => rfl
  | cons b frame ih =>
    have head := comparisons b (by simp)
    have tail := ih (fun x member => comparisons x (by simp only [List.mem_cons]; exact Or.inr member))
    simp only [smaller, List.map_cons, List.filter_cons, head] at tail ⊢
    split <;> simp_all only [List.map_cons]

private theorem find_map_compare (frame : List Binding) (f : Binding → Binding) (oldKey newKey : Key)
    (comparisons : ∀ b ∈ frame, Keys.compare (f b).key newKey = Keys.compare b.key oldKey) :
    equal (frame.map f) newKey = (equal frame oldKey).map f := by
  induction frame with
  | nil => rfl
  | cons b frame ih =>
    have head := comparisons b (by simp)
    have tail := ih (fun x member => comparisons x (by simp only [List.mem_cons]; exact Or.inr member))
    simp only [equal, List.map_cons, List.find?_cons, head] at tail ⊢
    split
    · rfl
    · exact tail

/-- Both actual lookup operations are preserved on the explicit frame
whose keys are recomputed from the saved source payloads. Whether this
frame is produced by a whole transported encoding is a separate theorem. -/
theorem rekey_queried_frame_tests {d : Nat} {source oldTarget target : ParentContext}
    {coordinates visible owners moved : List Nat} {materials : List (Forests (List Nat))}
    {frame : List Binding}
    (known : InheritedMaterials d source coordinates visible owners materials frame)
    (oldView : Parents.NumericalView d source oldTarget visible)
    (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
    (sourceUnit : Parents.UnitSteps d (source ++ [Parents.label d source coordinates]))
    (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
    (targetUnit : Parents.UnitSteps d target)
    (view : Parents.NumericalView d (source ++ [Parents.label d source coordinates]) target moved)
    (targetWidth : ∀ i, i < target.length → (target[i]?.getD default).coordinates.length = d)
    (positive : 0 < d) (width : coordinates.length = d) (hs : Forests (List Nat))
    (legal : Source.FiniteLegalForests d (source ++ [Parents.label d source coordinates])
      (coordinates[0]?.getD 0) hs) :
    let f := rekeyBinding d (source ++ [Parents.label d source coordinates]) target visible moved materials
    let key := queryKey d source coordinates hs
    let newKey := movedQueryKey d source target coordinates moved hs
    smaller (frame.map f) newKey = (smaller frame key).map f ∧
      equal (frame.map f) newKey = (equal frame key).map f := by
  have comparisons := rekey_queried_binding_compare known oldView sourceCoherent sourceValid sourceUnit
    targetCoherent targetValid targetUnit view targetWidth positive width hs legal
  exact ⟨filter_map_compare frame _ _ _ comparisons, find_map_compare frame _ _ _ comparisons⟩

/-- This version takes the certificate proved for every actual read of
a standard source, and uses the literal key and frame of that read. -/
theorem MaterialQuery.rekey_tests {d : Nat} {source target : ParentContext}
    {coordinates visible owners moved : List Nat} {materials : List (Forests (List Nat))}
    {state : State d} {hs : Forests (List Nat)}
    (query : MaterialQuery d source coordinates visible owners materials state hs)
    (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
    (targetUnit : Parents.UnitSteps d target)
    (view : Parents.NumericalView d (source ++ [Parents.label d source coordinates]) target moved)
    (targetWidth : ∀ i, i < target.length → (target[i]?.getD default).coordinates.length = d)
    (positive : 0 < d) :
    let frame := frameAt state (representative visible (Parents.label d source coordinates) (d - 1))
    let key := Keys.ofColumn d visible.length (Parents.label d source coordinates)
      (Parents.annotateForests d (source ++ [Parents.label d source coordinates]) hs)
    let f := rekeyBinding d (source ++ [Parents.label d source coordinates]) target visible moved materials
    let newKey := movedQueryKey d source target coordinates moved hs
    smaller (frame.map f) newKey = (smaller frame key).map f ∧
      equal (frame.map f) newKey = (equal frame key).map f := by
  simpa only [queryKey, query.view.length] using rekey_queried_frame_tests query.inherited query.view
    query.coherent query.valid query.unit targetCoherent targetValid targetUnit view targetWidth
    positive query.width hs query.legal

private theorem base_height_map (frame : List Binding) (f : Binding → Binding)
    (heights : ∀ b, (f b).height = b.height) :
    (base (frame.map f)).height = (base frame).height := by
  simp only [base, List.getLast?_map]
  cases frame.getLast? with
  | none => rfl
  | some b => exact heights b

/-- The exact first key-row height, including the fresh-key gap case,
is preserved. This is stronger than only preserving new versus reused. -/
theorem MaterialQuery.rekey_firstHeight {d : Nat} {source target : ParentContext}
    {coordinates visible owners moved : List Nat} {materials : List (Forests (List Nat))}
    {state : State d} {hs : Forests (List Nat)}
    (query : MaterialQuery d source coordinates visible owners materials state hs)
    (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
    (targetUnit : Parents.UnitSteps d target)
    (view : Parents.NumericalView d (source ++ [Parents.label d source coordinates]) target moved)
    (targetWidth : ∀ i, i < target.length → (target[i]?.getD default).coordinates.length = d)
    (positive : 0 < d) :
    let frame := frameAt state (representative visible (Parents.label d source coordinates) (d - 1))
    let key := Keys.ofColumn d visible.length (Parents.label d source coordinates)
      (Parents.annotateForests d (source ++ [Parents.label d source coordinates]) hs)
    let f := rekeyBinding d (source ++ [Parents.label d source coordinates]) target visible moved materials
    firstHeight (frame.map f) (movedQueryKey d source target coordinates moved hs) = firstHeight frame key := by
  let frame := frameAt state (representative visible (Parents.label d source coordinates) (d - 1))
  let key := Keys.ofColumn d visible.length (Parents.label d source coordinates)
    (Parents.annotateForests d (source ++ [Parents.label d source coordinates]) hs)
  let f := rekeyBinding d (source ++ [Parents.label d source coordinates]) target visible moved materials
  have tests := query.rekey_tests targetCoherent targetValid targetUnit view targetWidth positive
  change smaller (frame.map f) (movedQueryKey d source target coordinates moved hs) = (smaller frame key).map f ∧
    equal (frame.map f) (movedQueryKey d source target coordinates moved hs) = (equal frame key).map f at tests
  change firstHeight (frame.map f) (movedQueryKey d source target coordinates moved hs) = firstHeight frame key
  simp only [firstHeight]
  rw [tests.2]
  cases found : equal frame key with
  | none =>
    simp only [Option.map_none, tests.1]
    exact congrArg (· + 1) (base_height_map (smaller frame key) f (fun b => rekeyBinding_height _ _ _ _ _ _ b))
  | some b => exact rekeyBinding_height _ _ _ _ _ _ b

end BTnSSBMS.Encoder
