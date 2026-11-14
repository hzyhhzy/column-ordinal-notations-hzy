import BTnSSBMS.MaterialStability

/-!
Saved material in a fixed prefix is unchanged even when a new root is
inserted after a longer corridor. No numerical view from the short
prefix to the longer prefix is assumed: it would fail the frontier
condition. Each old binding is checked in its own unchanged prefix.
-/
namespace BTnSSBMS.Encoder

theorem transportedMaterialKey_identity {d : Nat} {source : ParentContext}
    {materials : List (Forests (List Nat))}
    (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
    (unit : Parents.UnitSteps d source) (material : Source.MaterialContext d source materials)
    {i : Nat} (inside : i < source.length) :
    transportedMaterialKey d source source (List.range source.length) materials i =
      Keys.atContext d source i (materials[i]?.getD .nil) := by
  have prefixLength : (source.take (i + 1)).length = i + 1 := by
    simp only [List.length_take]; omega
  have identity := Source.relocateForests_same_context
    (coherent.restrict (List.take_prefix ..)) (valid.restrict (List.take_prefix ..))
    (unit.restrict valid (List.take_prefix ..)) (by rw [prefixLength]; omega)
    (Parents.reading source 0 i) (materials[i]?.getD .nil) (material.legal i inside).2
  rw [prefixLength] at identity
  simp only [transportedMaterialKey, Parents.point_range source.length i inside,
    List.take_range, Nat.min_eq_left (by omega : i + 1 ≤ source.length), identity]

theorem rekeyBinding_identity {d : Nat} {source oldOutput : ParentContext}
    {visible : List Nat} {materials : List (Forests (List Nat))}
    (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
    (unit : Parents.UnitSteps d source) (material : Source.MaterialContext d source materials)
    (oldView : Parents.NumericalView d source oldOutput visible)
    (b : Binding) (known : BindingMaterial d source visible materials b) :
    (rekeyBinding d source source visible (List.range source.length) materials b).key = b.key := by
  cases latest : b.latest with
  | none => simp only [rekeyBinding, latest]
  | some p =>
    simp only [BindingMaterial, latest] at known
    obtain ⟨i, inside, named, key⟩ := known
    have inverse : visible.idxOf p = i := by rw [named]; exact oldView.idxOf_point inside
    simp only [rekeyBinding, latest, inverse]
    exact (transportedMaterialKey_identity coherent valid unit material inside).trans key.symm

theorem rekeyBinding_fixed_prefix {d : Nat} {source oldOutput nextSource nextTarget : ParentContext}
    {visible nextVisible moved : List Nat} {materials nextMaterials : List (Forests (List Nat))}
    (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
    (unit : Parents.UnitSteps d source) (material : Source.MaterialContext d source materials)
    (oldView : Parents.NumericalView d source oldOutput visible)
    (sourcePrefix : source <+: nextSource) (targetPrefix : source <+: nextTarget)
    (visiblePrefix : visible <+: nextVisible) (positions : List.range source.length <+: moved)
    (materialPrefix : materials <+: nextMaterials)
    (b : Binding) (known : BindingMaterial d source visible materials b) :
    (rekeyBinding d nextSource nextTarget nextVisible moved nextMaterials b).key = b.key := by
  rw [rekeyBinding_prefix oldView (Parents.numericalView_identity d source) material.length
    sourcePrefix targetPrefix visiblePrefix positions materialPrefix b known]
  exact rekeyBinding_identity coherent valid unit material oldView b known

theorem KeyFrameRel.fixed (keyOf : Binding → Key) (frame : List Binding)
    (same : ∀ b ∈ frame, keyOf b = b.key) : KeyFrameRel keyOf frame frame := by
  induction frame with
  | nil => exact .nil
  | cons b frame ih =>
    exact .cons ⟨(same b (by simp)).symm, rfl⟩
      (ih (fun x member => same x (by simp only [List.mem_cons]; exact Or.inr member)))

theorem FrameMaterials.fixed_prefix {d : Nat} {source oldOutput nextSource nextTarget : ParentContext}
    {visible nextVisible moved : List Nat} {materials nextMaterials : List (Forests (List Nat))}
    {frame : List Binding} (known : FrameMaterials d source visible materials frame)
    (coherent : Parents.Coherent d source) (valid : Parents.ContextValid source)
    (unit : Parents.UnitSteps d source) (material : Source.MaterialContext d source materials)
    (oldView : Parents.NumericalView d source oldOutput visible)
    (sourcePrefix : source <+: nextSource) (targetPrefix : source <+: nextTarget)
    (visiblePrefix : visible <+: nextVisible) (positions : List.range source.length <+: moved)
    (materialPrefix : materials <+: nextMaterials) :
    KeyFrameRel (fun b => (rekeyBinding d nextSource nextTarget nextVisible moved nextMaterials b).key)
      frame frame :=
  KeyFrameRel.fixed _ frame (fun b member => rekeyBinding_fixed_prefix coherent valid unit material
    oldView sourcePrefix targetPrefix visiblePrefix positions materialPrefix b (known b member))

end BTnSSBMS.Encoder
