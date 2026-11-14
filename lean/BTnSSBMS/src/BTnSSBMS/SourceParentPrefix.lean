import BTnSSBMS.SourceMarkedSpine

/-!
Removing only the appended highest-parent field recovers the numerical
annotation exactly. In particular, low-class selection in the actual FS
selects the actual numerical parent of the computed stopping column.
-/
namespace BTnSSBMS.Parents

def truncate (d : Nat) (a : ParentLabel) : ParentLabel :=
  {a with parents := a.parents.take d}

theorem truncate_extended_label (d : Nat) (context : ParentContext) (a : List Nat)
    (extra : List (Option Nat)) :
    truncate d {label d context a with parents := (label d context a).parents ++ extra} = label d context a := by
  have width := label_width d context a
  have same : ((label d context a).parents ++ extra).take d = (label d context a).parents := by
    simpa only [width] using List.take_left (l₁ := (label d context a).parents) (l₂ := extra)
  simp only [truncate, same]

theorem parent_truncate (d : Nat) (context : ParentContext) (row position : Nat) (inside : row < d) :
    parent (context.map (truncate d)) row position = parent context row position := by
  simp only [parent, List.getElem?_map]
  cases lookup : context[position]? with
  | none => rfl
  | some a => simp only [Option.map_some, Option.bind_some, truncate, List.getElem?_take_of_lt inside]

theorem Ancestor.truncate_iff {d : Nat} {context : ParentContext} {row root endpoint : Nat}
    (inside : row < d) : Ancestor (context.map (truncate d)) row root endpoint ↔ Ancestor context row root endpoint := by
  constructor
  · intro path
    induction path with
    | refl => exact .refl _
    | up edge rest ih => exact .up (by simpa only [parent_truncate d context row _ inside] using edge) ih
  · intro path
    induction path with
    | refl => exact .refl _
    | up edge rest ih => exact .up (by simpa only [parent_truncate d context row _ inside] using edge) ih

end BTnSSBMS.Parents

namespace BTnSSBMS.Source

mutual
  theorem fillTop_annotate_truncate (d : Nat) (context : ParentContext) (keyContext : KeyContext)
      (owners : List Nat) (e : NumericalExpr) :
      (fillTop d keyContext owners (Parents.annotate d context e)).map (Parents.truncate d) =
        Parents.annotate d context e := by
    cases e with
    | nil => rfl
    | cons a hs rest =>
      simp only [Parents.annotate, fillTop, Expr.map, Parents.truncate_extended_label,
        fillTopForests_annotate_truncate, fillTop_annotate_truncate]
  theorem fillTopForests_annotate_truncate (d : Nat) (context : ParentContext) (keyContext : KeyContext)
      (owners : List Nat) (hs : Forests (List Nat)) :
      (fillTopForests d keyContext owners (Parents.annotateForests d context hs)).map (Parents.truncate d) =
        Parents.annotateForests d context hs := by
    cases hs with
    | nil => rfl
    | cons h rest =>
      simp only [Parents.annotateForests, fillTopForests, Forests.map,
        fillTop_annotate_truncate, fillTopForests_annotate_truncate]
end

theorem parents_truncate (d : Nat) (e : NumericalExpr) :
    (parents d e).map (Parents.truncate d) = Parents.annotate d [] e :=
  fillTop_annotate_truncate d [] [] [] e

theorem actual_terminal_numerical_label {d depth : Nat} {e : NumericalExpr}
    {part : ParentExpr} {a : ParentLabel} {hs : Forests ParentLabel}
    (selected : (spine (parents d e))[depth]? = some part) (last : last? part = some (a, hs))
    {layer : SpineLayer} (found : layerAt d [] none [] depth e = some layer)
    {terminal : List Nat} {attached : Forests (List Nat)}
    (atLast : last? layer.term = some (terminal, attached)) :
    Parents.truncate d a = Parents.label d (outerContext d layer.context (dropLast layer.term)) terminal := by
  have numeric := annotate_layer depth e found
  rw [← parents_truncate, spine_map, List.getElem?_map, selected, Option.map_some] at numeric
  have same := Option.some.inj numeric
  have left := last_map (Parents.truncate d) part
  rw [same, last, Option.map_some] at left
  have right := last_annotate d layer.context layer.term atLast
  dsimp only at right
  rw [right] at left
  have columns := Option.some.inj left
  exact (congrArg Prod.fst columns).symm

theorem selected_low_numerical_root {d cap depth root : Nat} {e : NumericalExpr}
    {part : ParentExpr} {a : ParentLabel} {hs : Forests ParentLabel}
    (selected : (spine (parents d e))[depth]? = some part) (last : last? part = some (a, hs))
    (chosen : highestParent 0 a.parents = some (cap, root)) (room : cap < d)
    {layer : SpineLayer} (found : layerAt d [] none [] depth e = some layer)
    {terminal : List Nat} {attached : Forests (List Nat)}
    (atLast : last? layer.term = some (terminal, attached)) :
    (Parents.label d (outerContext d layer.context (dropLast layer.term)) terminal).parents[cap]?.join = some root := by
  rw [← actual_terminal_numerical_label selected last found atLast]
  simp only [Parents.truncate, List.getElem?_take_of_lt room]
  obtain ⟨_, _, atParent⟩ := highestParent_found a.parents 0 cap root chosen
  simpa only [Nat.sub_zero, Option.join_some] using congrArg Option.join atParent

end BTnSSBMS.Source
