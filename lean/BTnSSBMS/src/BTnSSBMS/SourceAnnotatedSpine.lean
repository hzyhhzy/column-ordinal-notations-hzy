import BTnSSBMS.SourceTopSelection

/-! Exact numerical-parent annotation on the frozen scoped spine and
root suffix. Annotation is performed in the computed entering context. -/
namespace BTnSSBMS.Source

theorem last_annotate (d : Nat) (context : ParentContext) (e : NumericalExpr)
    {a : List Nat} {hs : Forests (List Nat)} (found : last? e = some (a, hs)) :
    let before := outerContext d context (dropLast e)
    last? (Parents.annotate d context e) = some (Parents.label d before a,
      Parents.annotateForests d (before ++ [Parents.label d before a]) hs) := by
  cases e with
  | nil => simp [last?] at found
  | cons b ks rest =>
    cases rest with
    | nil =>
      have same : (b, ks) = (a, hs) := by simpa only [last?, Option.some.injEq] using found
      cases same
      simp only [Parents.annotate, last?, dropLast, outerContext]
    | cons c js tail =>
      simpa only [Parents.annotate, last?, dropLast, outerContext] using
        last_annotate d (context ++ [Parents.label d context b]) (.cons c js tail)
          (by simpa only [last?] using found)

theorem lastForest_annotate (d : Nat) (context : ParentContext) (hs : Forests (List Nat))
    {h : NumericalExpr} (found : lastForest? hs = some h) :
    lastForest? (Parents.annotateForests d context hs) = some (Parents.annotate d context h) := by
  cases hs with
  | nil => simp [lastForest?] at found
  | cons first rest =>
    cases rest with
    | nil =>
      have same : first = h := by simpa only [lastForest?, Option.some.injEq] using found
      subst h
      simp only [Parents.annotateForests, lastForest?]
    | cons k ks =>
      simpa only [Parents.annotateForests, lastForest?] using
        lastForest_annotate d context (.cons k ks) (by simpa only [lastForest?] using found)

theorem annotate_layer {d : Nat} {context : ParentContext} {owner : Option Nat} {owners : List Nat}
    (depth : Nat) (e : NumericalExpr) {layer : SpineLayer}
    (found : layerAt d context owner owners depth e = some layer) :
    (spine (Parents.annotate d context e))[depth]? = some (Parents.annotate d layer.context layer.term) := by
  induction depth generalizing context owner owners e layer with
  | zero =>
    have same : layer = ⟨context, owner, owners, e⟩ := by
      simpa only [layerAt, Option.some.injEq] using found.symm
    subst layer
    rfl
  | succ depth ih =>
    simp only [layerAt, Option.bind_eq_some_iff] at found
    obtain ⟨⟨a, hs⟩, last, h, child, next⟩ := found
    rw [spine_get_succ]
    have atLast := last_annotate d context e last
    dsimp only at atLast
    simp only [lastChild?, atLast, Option.bind_some,
      lastForest_annotate d _ hs child]
    exact ih h next

theorem drop_annotate (d : Nat) (context : ParentContext) (index : Nat) (e : NumericalExpr) :
    drop index (Parents.annotate d context e) =
      Parents.annotate d (dropContext d context index e) (drop index e) := by
  induction index generalizing context e with
  | zero => simp only [drop, dropContext]
  | succ index ih =>
    cases e with
    | nil => simp only [drop, dropContext, Parents.annotate]
    | cons a hs rest =>
      simpa only [Parents.annotate, drop, dropContext] using ih (context ++ [Parents.label d context a]) rest

theorem annotated_spine_prefix_length (d : Nat) (context : ParentContext) (depth : Nat) (e : NumericalExpr) :
    (((spine (Parents.annotate d context e)).take depth).map length).sum =
      (((spine e).take depth).map length).sum := by
  have erased : spine e = (spine (Parents.annotate d context e)).map (Expr.map ParentLabel.coordinates) := by
    rw [← spine_map, Parents.annotate_erase]
  rw [erased, ← List.map_take, List.map_map]
  simp only [Function.comp_def, length_map]

end BTnSSBMS.Source
