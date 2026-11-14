import BTnSSBMS.FrameCoupling

/-! Extending a lexical source/target prefix does not change the
transported keys of already saved material. This is the persistence
needed when a real encoder appends a column or enters an owned forest. -/
namespace BTnSSBMS.Encoder

theorem transportedMaterialKey_prefix {d : Nat} {source target nextSource nextTarget : ParentContext}
    {moved nextMoved : List Nat} {materials nextMaterials : List (Forests (List Nat))}
    (view : Parents.NumericalView d source target moved)
    (sourcePrefix : source <+: nextSource) (targetPrefix : target <+: nextTarget)
    (movedPrefix : moved <+: nextMoved) (materialPrefix : materials <+: nextMaterials)
    {i : Nat} (inside : i < source.length) (materialInside : i < materials.length) :
    transportedMaterialKey d nextSource nextTarget nextMoved nextMaterials i =
      transportedMaterialKey d source target moved materials i := by
  obtain ⟨sourceExtra, rfl⟩ := sourcePrefix
  obtain ⟨targetExtra, rfl⟩ := targetPrefix
  obtain ⟨movedExtra, rfl⟩ := movedPrefix
  obtain ⟨materialExtra, rfl⟩ := materialPrefix
  have moveInside : i < moved.length := by rw [view.length]; exact inside
  have point : Parents.point (moved ++ movedExtra) i = Parents.point moved i := by
    simp only [Parents.point, List.getElem?_append_left moveInside]
  have bounded := view.bounded i inside
  simp only [transportedMaterialKey, point, List.getElem?_append_left materialInside,
    List.take_append_of_le_length (by omega : i + 1 ≤ source.length),
    List.take_append_of_le_length (by omega : i + 1 ≤ moved.length),
    List.take_append_of_le_length (by omega : Parents.point moved i + 1 ≤ target.length)]
  exact Keys.atContext_prefix d (List.prefix_append _ _) bounded _

theorem rekeyBinding_prefix {d : Nat} {source oldOutput target nextSource nextTarget : ParentContext}
    {visible moved nextVisible nextMoved : List Nat} {materials nextMaterials : List (Forests (List Nat))}
    (oldView : Parents.NumericalView d source oldOutput visible)
    (view : Parents.NumericalView d source target moved)
    (materialLength : materials.length = source.length)
    (sourcePrefix : source <+: nextSource) (targetPrefix : target <+: nextTarget)
    (visiblePrefix : visible <+: nextVisible) (movedPrefix : moved <+: nextMoved)
    (materialPrefix : materials <+: nextMaterials)
    (b : Binding) (known : BindingMaterial d source visible materials b) :
    rekeyBinding d nextSource nextTarget nextVisible nextMoved nextMaterials b =
      rekeyBinding d source target visible moved materials b := by
  cases latest : b.latest with
  | none => simp only [rekeyBinding, latest]
  | some p =>
    simp only [BindingMaterial, latest] at known
    obtain ⟨i, inside, named, _⟩ := known
    have inverse : visible.idxOf p = i := by rw [named]; exact oldView.idxOf_point inside
    have visibleInside : i < visible.length := by rw [oldView.length]; exact inside
    have member : p ∈ visible := by
      rw [named]
      simpa only [Parents.point, List.getElem?_eq_getElem visibleInside, Option.getD_some] using
        (List.getElem_mem visibleInside)
    have nextIndex : nextVisible.idxOf p = i := by
      obtain ⟨extra, rfl⟩ := visiblePrefix
      rw [List.idxOf_append, if_pos member, inverse]
    simp only [rekeyBinding, latest, nextIndex, inverse]
    have key := transportedMaterialKey_prefix view sourcePrefix targetPrefix movedPrefix materialPrefix
      inside (by rw [materialLength]; exact inside)
    rw [key]

/-- This applies to an actual saved frame, using the source attachment
provenance already proved for every visible representative. -/
theorem FrameMaterials.rekey_prefix {d : Nat} {source oldOutput target nextSource nextTarget : ParentContext}
    {visible moved nextVisible nextMoved : List Nat} {materials nextMaterials : List (Forests (List Nat))}
    {frame newFrame : List Binding} (known : FrameMaterials d source visible materials frame)
    (oldView : Parents.NumericalView d source oldOutput visible)
    (view : Parents.NumericalView d source target moved)
    (materialLength : materials.length = source.length)
    (sourcePrefix : source <+: nextSource) (targetPrefix : target <+: nextTarget)
    (visiblePrefix : visible <+: nextVisible) (movedPrefix : moved <+: nextMoved)
    (materialPrefix : materials <+: nextMaterials)
    (related : KeyFrameRel (fun b => (rekeyBinding d source target visible moved materials b).key) frame newFrame) :
    KeyFrameRel (fun b => (rekeyBinding d nextSource nextTarget nextVisible nextMoved nextMaterials b).key)
      frame newFrame := by
  apply related.congr
  intro b member
  exact congrArg Binding.key (rekeyBinding_prefix oldView view materialLength sourcePrefix targetPrefix
    visiblePrefix movedPrefix materialPrefix b (known b member))

/-- A binding just saved by either branch has its key at the newly
appended source material. The target point is the new source endpoint;
the new key is computed by relocating that actual whole attachment. -/
theorem rekeyBinding_new_latest_of_length {d : Nat} {source target oldOutput : ParentContext}
    {visible moved : List Nat} {materials : List (Forests (List Nat))}
    (oldView : Parents.NumericalView d source oldOutput visible)
    (mapLength : moved.length = source.length)
    (materialLength : materials.length = source.length)
    (a newA : ParentLabel) (hs : Forests (List Nat)) (oldPoint : Nat)
    (fresh : ∀ i, i < visible.length → Parents.point visible i < oldPoint)
    (b : Binding) (latest : b.latest = some oldPoint) :
    (rekeyBinding d (source ++ [a]) (target ++ [newA]) (visible ++ [oldPoint])
      (moved ++ [target.length]) (materials ++ [hs]) b).key =
      Keys.atContext d (target ++ [newA]) target.length
        (Source.relocateForests d (source ++ [a]) (target ++ [newA]) (moved ++ [target.length]) hs) := by
  have absent : oldPoint ∉ visible := by
    intro member
    obtain ⟨i, inside, found⟩ := List.getElem_of_mem member
    have value : Parents.point visible i = oldPoint := by
      rw [Parents.point, List.getElem?_eq_getElem inside, Option.getD_some, found]
    have strict := fresh i inside
    omega
  have inverse : (visible ++ [oldPoint]).idxOf oldPoint = source.length := by
    rw [List.idxOf_append, if_neg absent]
    simp only [List.idxOf_cons_self, Nat.zero_add, oldView.length]
  simp only [rekeyBinding, latest, inverse, transportedMaterialKey]
  rw [← mapLength, Parents.point_append_last, mapLength,
    ← materialLength, List.getElem?_concat_length, Option.getD_some, materialLength]
  have sourceLength : source.length + 1 = (source ++ [a]).length := by simp
  have targetLength : target.length + 1 = (target ++ [newA]).length := by simp
  have movedLength : source.length + 1 = (moved ++ [target.length]).length := by simp [mapLength]
  rw [sourceLength, List.take_length, targetLength, List.take_length]
  rw [← sourceLength, movedLength, List.take_length]

theorem rekeyBinding_new_latest {d : Nat} {source target oldOutput : ParentContext}
    {visible moved : List Nat} {materials : List (Forests (List Nat))}
    (oldView : Parents.NumericalView d source oldOutput visible)
    (view : Parents.NumericalView d source target moved)
    (materialLength : materials.length = source.length)
    (a newA : ParentLabel) (hs : Forests (List Nat)) (oldPoint : Nat)
    (fresh : ∀ i, i < visible.length → Parents.point visible i < oldPoint)
    (b : Binding) (latest : b.latest = some oldPoint) :
    (rekeyBinding d (source ++ [a]) (target ++ [newA]) (visible ++ [oldPoint])
      (moved ++ [target.length]) (materials ++ [hs]) b).key =
      Keys.atContext d (target ++ [newA]) target.length
        (Source.relocateForests d (source ++ [a]) (target ++ [newA]) (moved ++ [target.length]) hs) :=
  rekeyBinding_new_latest_of_length oldView view.length materialLength a newA hs oldPoint fresh b latest

end BTnSSBMS.Encoder
