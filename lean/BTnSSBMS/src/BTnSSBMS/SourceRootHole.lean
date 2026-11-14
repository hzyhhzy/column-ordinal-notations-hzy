import BTnSSBMS.SourceParentPrefix

/-! The actual root suffix and the whole term have the same terminal
hole geometry. Only its inherited outer-owner field may differ. -/
namespace BTnSSBMS.Source

theorem layerAt_add (d : Nat) (context : ParentContext) (owner : Option Nat) (owners : List Nat)
    (outer inner : Nat) (e : NumericalExpr) :
    (layerAt d context owner owners outer e).bind
        (fun layer => layerAt d layer.context layer.owner layer.owners inner layer.term) =
      layerAt d context owner owners (outer + inner) e := by
  induction outer generalizing context owner owners e with
  | zero => simp only [layerAt, Option.bind_some, Nat.zero_add]
  | succ outer ih =>
    simp only [Nat.succ_add, layerAt]
    cases last : last? e with
    | none => rfl
    | some c =>
      obtain ⟨a, hs⟩ := c
      simp only [Option.bind_some]
      cases child : lastForest? hs with
      | none => rfl
      | some h =>
        simp only [Option.bind_some]
        exact ih _ _ _ h

theorem holeSite_change_owner (d : Nat) (context : ParentContext) (old new : Option Nat)
    (depth : Nat) (e : NumericalExpr) :
    holeSite d context new depth e = (holeSite d context old depth e).map
      (fun site => ⟨site.context, if depth = 0 then new else site.owner, site.terminal, site.attached⟩) := by
  cases e with
  | nil => simp only [holeSite, Option.map_none]
  | cons a hs rest =>
    cases rest with
    | nil =>
      cases depth with
      | zero => simp only [holeSite, Option.map_some, if_true]
      | succ depth =>
        simp only [holeSite, show depth + 1 ≠ 0 by omega, if_false]
        cases holeSiteForests d (context ++ [Parents.label d context a]) (a[0]?.getD 0) depth hs <;> rfl
    | cons b ks tail =>
      simpa only [holeSite] using
        holeSite_change_owner d (context ++ [Parents.label d context a]) old new depth (.cons b ks tail)

theorem root_hole_from_layers {d rootDepth stopDepth index : Nat} {e : NumericalExpr}
    {rootLayer stopLayer : SpineLayer}
    (atRoot : layerAt d [] none [] rootDepth e = some rootLayer)
    (atStop : layerAt d [] none [] stopDepth e = some stopLayer)
    (earlier : rootDepth ≤ stopDepth) (inside : index < length rootLayer.term)
    {terminal : List Nat} {attached : Forests (List Nat)}
    (last : last? stopLayer.term = some (terminal, attached)) :
    holeSite d (dropContext d rootLayer.context index rootLayer.term) none (stopDepth - rootDepth)
        (drop index rootLayer.term) =
      some ⟨outerContext d stopLayer.context (dropLast stopLayer.term),
        if stopDepth - rootDepth = 0 then none else stopLayer.owner, terminal, attached⟩ := by
  have composed := layerAt_add d [] none [] rootDepth (stopDepth - rootDepth) e
  rw [atRoot, Option.bind_some, Nat.add_sub_of_le earlier, atStop] at composed
  have hole := layerAt_holeSite (stopDepth - rootDepth) rootLayer.term composed last
  rw [holeSite_change_owner d _ rootLayer.owner none, holeSite_drop d _ rootLayer.owner _ index _ inside,
    hole, Option.map_some]

end BTnSSBMS.Source
