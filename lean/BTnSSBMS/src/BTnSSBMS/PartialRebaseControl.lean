import BTnSSBMS.FixedPrefixControl

/-!
The complete real encoder, including root forests and the outer tail,
has identical key/tag output under an intermediate-row partial rebase.
All query and saved-frame entry conditions are derived from the actual
root geometry and immutable historical prefix snapshots. The result
uses the original activation copy, not a different expansion rule.
-/
namespace BTnSSBMS.Encoder

theorem partial_rebase_encode_control {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    (unit : Parents.UnitSteps d context) (position : List Nat)
    (positionUnit : Parents.UnitSteps d (context ++ [Parents.label d context position]))
    {cut root : Nat} (positive : 0 < cut) (room : cut < d) (insideRoot : root < context.length)
    (path : Parents.Ancestor (context ++ [Parents.label d context position]) (cut - 1) root context.length)
    (same : (Parents.label d context position).parents[cut]?.join = Parents.parent context cut root)
    (hs : Forests (List Nat)) (tail : NumericalExpr)
    (legal : Source.FiniteLegal d (context.take root) (.cons (context[root]?.getD default).coordinates hs tail))
    {visible nextVisible owners : List Nat} {materials : List (Forests (List Nat))}
    {state next : State d}
    (known : VisibleMaterials d (context.take root) visible owners materials state)
    (oldView : Parents.NumericalView d (context.take root) (BMS.parentTable (d + 2) (matrix state)) visible)
    (newView : Parents.NumericalView d context (BMS.parentTable (d + 2) (matrix next)) nextVisible)
    (contextWidth : ∀ i, i < context.length → (context[i]?.getD default).coordinates.length = d)
    (visiblePrefix : visible <+: nextVisible) (statePrefix : state <+: next) :
    let coordinates := (context[root]?.getD default).coordinates
    let delta := (List.range cut).map (fun j => position[j]?.getD 0 - coordinates[j]?.getD 0)
    SharedTrace state next
      (encode d (Parents.annotate d (context.take root) (.cons coordinates hs tail)) visible state)
      (encode d (Parents.annotate d context
        (Source.copied d root cut delta 1 (context.take root) (List.replicate root 0) (.cons coordinates hs tail)))
        nextVisible next) := by
  let coordinates := (context[root]?.getD default).coordinates
  let delta := (List.range cut).map (fun j => position[j]?.getD 0 - coordinates[j]?.getD 0)
  let head := Source.shift coordinates cut delta 1
  have length : (context.take root).length = root := by simp only [List.length_take]; omega
  have divided := coherent.take_succ_label insideRoot
  have forestsLegal := legal.2.2.2.1
  have tailLegal := legal.2.2.2.2
  rw [← divided] at forestsLegal tailLegal
  have scope := Source.partial_rebase_shiftView coherent valid unit position positionUnit
    positive room insideRoot path same legal.1
  have frameSame := partial_rebase_queried_frame coherent valid unit position positionUnit
    positive room insideRoot path same legal.1 oldView visiblePrefix statePrefix
  have keySame := partial_rebase_queryKey coherent valid unit position positionUnit
    positive room insideRoot path same hs legal.1 forestsLegal
  have targetWidth : ∀ i, i < (context ++ [Parents.label d context head]).length →
      ((context ++ [Parents.label d context head])[i]?.getD default).coordinates.length = d := by
    intro i inside
    by_cases old : i < context.length
    · simpa only [List.getElem?_append_left old] using contextWidth i old
    · have last : i = context.length := by
        simp only [List.length_append, List.length_cons, List.length_nil] at inside
        omega
      subst i
      simp only [List.getElem?_concat_length, Option.getD_some, Parents.label]
      exact (Source.shift_width ..).trans legal.1
  have result := prefix_rebase_encode_control d coordinates head hs tail (context.take root) context
    visible nextVisible owners materials state next (by omega)
    (coherent.restrict (List.take_prefix root context)) (valid.restrict (List.take_prefix root context))
    (unit.restrict valid (List.take_prefix root context)) (List.take_prefix root context)
    coherent valid scope.targetUnit
    (by simpa only [coordinates, head, delta, length, ← divided] using scope.view)
    oldView newView targetWidth known visiblePrefix statePrefix frameSame
    (by simpa only [coordinates, head, delta, length, ← divided] using keySame) legal
  dsimp only [coordinates, head, delta] at result
  simp only [length, ← divided] at result
  rw [Source.relocateForests_eq_copied scope _ hs forestsLegal,
    Source.relocate_eq_copied scope tail tailLegal] at result
  simpa only [Source.copied_at_root, ← divided] using result

end BTnSSBMS.Encoder
