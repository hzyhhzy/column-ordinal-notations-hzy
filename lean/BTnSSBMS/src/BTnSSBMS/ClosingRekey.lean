import BTnSSBMS.FixedPrefixMaterials
import BTnSSBMS.ClosingQueryInsertion

/-!
Stretch a closing representative to a later highest-row descendant.
Every old saved key remains the same: earlier material is in a fixed
prefix, and the root material is transplanted along its real ancestry.
This concerns complete keys, not equality of the two source attachments.
-/
namespace BTnSSBMS.Source

theorem relocated_ancestor_key {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    (unit : Parents.UnitSteps d context) (positive : 0 < d)
    {root : Nat} (before : root < context.length - 1)
    (path : Parents.Ancestor context (d - 1) root (context.length - 1))
    (rootWidth : (context[root]?.getD default).coordinates.length = d)
    (lastWidth : (context[context.length - 1]?.getD default).coordinates.length = d)
    (hs : Forests (List Nat))
    (legal : FiniteLegalForests d (context.take (root + 1)) (Parents.reading context 0 root) hs) :
    Keys.atContext d context (context.length - 1)
      (relocateForests d (context.take (root + 1)) context
        (List.range root ++ [context.length - 1]) hs) = Keys.atContext d context root hs := by
  have view := Parents.ancestor_to_last_view coherent valid positive before path
  have prefixLength : (context.take (root + 1)).length = root + 1 := by
    simp only [List.length_take]; omega
  have input : FiniteLegalForests d (context.take (root + 1))
      (Parents.reading (context.take (root + 1)) 0 root) hs := by
    rw [Parents.reading_prefix (List.take_prefix ..) 0 root (by omega)]
    exact legal
  have moved := relocateForests_finiteLegal d hs (context.take (root + 1)) context
    (List.range root ++ [context.length - 1]) (coherent.restrict (List.take_prefix ..))
    (valid.restrict (List.take_prefix ..)) coherent valid unit view positive root (by omega)
    (by rw [prefixLength, Nat.add_sub_cancel]; exact .refl _) input
  have endpoint : Parents.point (List.range root ++ [context.length - 1]) root = context.length - 1 := by
    simpa only [List.length_range] using Parents.point_append_last (List.range root) (context.length - 1)
  rw [endpoint] at moved
  have same := ancestor_key_compare_atContext coherent valid unit positive before path rootWidth lastWidth
    hs _ legal moved
  have reflexive : ∀ xs : Forests (List Nat), xs.compare (listCompare Ord.compare) xs = .eq := by
    intro xs
    exact Ordering.eq_eq_of_eq_swap (Forests.compare_oriented (listCompare Ord.compare)
      (listCompare_oriented Ord.compare (fun a b : Nat => Std.OrientedOrd.eq_swap (a := a) (b := b))) xs xs)
  rw [reflexive] at same
  exact (Keys.compare_eq_imp _ _ same).symm

end BTnSSBMS.Source

namespace BTnSSBMS.Encoder

theorem transportedMaterialKey_stretched {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    (unit : Parents.UnitSteps d context) (positive : 0 < d)
    {root : Nat} (before : root < context.length - 1)
    (path : Parents.Ancestor context (d - 1) root (context.length - 1))
    (lastWidth : (context[context.length - 1]?.getD default).coordinates.length = d)
    {materials : List (Forests (List Nat))}
    (material : Source.MaterialContext d (context.take (root + 1)) materials)
    {i : Nat} (inside : i < (context.take (root + 1)).length) :
    transportedMaterialKey d (context.take (root + 1)) context
      (List.range root ++ [context.length - 1]) materials i =
        Keys.atContext d (context.take (root + 1)) i (materials[i]?.getD .nil) := by
  have prefixLength : (context.take (root + 1)).length = root + 1 := by
    simp only [List.length_take]; omega
  by_cases old : i < root
  · have point : Parents.point (List.range root ++ [context.length - 1]) i = i := by
      rw [Parents.point_append_old _ i _ (by simpa only [List.length_range] using old),
        Parents.point_range root i old]
    have identity := transportedMaterialKey_identity (coherent.restrict (List.take_prefix ..))
      (valid.restrict (List.take_prefix ..)) (unit.restrict valid (List.take_prefix ..)) material inside
    unfold transportedMaterialKey at identity
    rw [Parents.point_range _ i inside] at identity
    simp only [prefixLength, List.take_take, List.take_range,
      Nat.min_eq_left (by omega : i + 1 ≤ root + 1)] at identity
    have movedPrefix : (List.range root ++ [context.length - 1]).take (i + 1) = List.range (i + 1) := by
      rw [List.take_append_of_le_length (by simpa only [List.length_range] using (by omega : i + 1 ≤ root)),
        List.take_range, Nat.min_eq_left (by omega : i + 1 ≤ root)]
    simp only [transportedMaterialKey, point, List.take_take,
      Nat.min_eq_left (by omega : i + 1 ≤ root + 1), movedPrefix]
    rw [Keys.atContext_prefix d (List.take_prefix ..) inside]
    exact identity
  · have last : i = root := by omega
    subst i
    have endpoint : Parents.point (List.range root ++ [context.length - 1]) root = context.length - 1 := by
      simpa only [List.length_range] using Parents.point_append_last (List.range root) (context.length - 1)
    have oldMaterial := material.legal root (by omega)
    have atRoot : (context.take (root + 1))[root]?.getD default = context[root]?.getD default := by
      rw [List.getElem?_take_of_lt (by omega : root < root + 1)]
    have input : Source.FiniteLegalForests d (context.take (root + 1))
        (Parents.reading context 0 root) (materials[root]?.getD .nil) := by
      simpa only [List.take_take, Nat.min_self,
        Parents.reading_prefix (List.take_prefix ..) 0 root (by omega : root < (context.take (root + 1)).length)]
        using oldMaterial.2
    have key := Source.relocated_ancestor_key coherent valid unit positive before path
      (by simpa only [atRoot] using oldMaterial.1) lastWidth _ input
    have movedLength : (List.range root ++ [context.length - 1]).length = root + 1 := by simp
    have movedAll : (List.range root ++ [context.length - 1]).take (root + 1) =
        List.range root ++ [context.length - 1] := by rw [← movedLength, List.take_length]
    simp only [transportedMaterialKey, endpoint, List.take_take, Nat.min_self, movedAll]
    rw [
      show context.length - 1 + 1 = context.length by omega, List.take_length, key,
      Keys.atContext_prefix d (List.take_prefix ..) (by omega)]

theorem rekeyBinding_stretched {d : Nat} {context oldOutput : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    (unit : Parents.UnitSteps d context) (positive : 0 < d)
    {root : Nat} (before : root < context.length - 1)
    (path : Parents.Ancestor context (d - 1) root (context.length - 1))
    (lastWidth : (context[context.length - 1]?.getD default).coordinates.length = d)
    {visible : List Nat} {materials : List (Forests (List Nat))}
    (material : Source.MaterialContext d (context.take (root + 1)) materials)
    (oldView : Parents.NumericalView d (context.take (root + 1)) oldOutput visible)
    (b : Binding) (known : BindingMaterial d (context.take (root + 1)) visible materials b) :
    (rekeyBinding d (context.take (root + 1)) context visible
      (List.range root ++ [context.length - 1]) materials b).key = b.key := by
  cases latest : b.latest with
  | none => simp only [rekeyBinding, latest]
  | some p =>
    simp only [BindingMaterial, latest] at known
    obtain ⟨i, inside, named, key⟩ := known
    have inverse : visible.idxOf p = i := by rw [named]; exact oldView.idxOf_point inside
    simp only [rekeyBinding, latest, inverse]
    exact (transportedMaterialKey_stretched coherent valid unit positive before path lastWidth material inside).trans key.symm

end BTnSSBMS.Encoder
