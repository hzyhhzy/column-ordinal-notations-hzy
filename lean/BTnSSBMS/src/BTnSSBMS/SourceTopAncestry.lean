import BTnSSBMS.SourceLowAssembly

/-!
The actual highest key-parent search follows the numerical ancestor chain
in the canonical numerical context. Appended key-parent fields and closed
forest scopes are removed explicitly; no source standardness is assumed.
-/
namespace BTnSSBMS.Source

mutual
  def TopAncestral (d : Nat) (context : ParentContext) : ParentExpr → Prop
    | .nil => True
    | .cons a hs rest =>
      let next := context ++ [Parents.label d context a.coordinates]
      (∀ root, a.parents[d]?.join = some root →
        Parents.Ancestor next (d - 1) root context.length) ∧
      TopAncestralForests d next hs ∧ TopAncestral d next rest
  def TopAncestralForests (d : Nat) (context : ParentContext) : Forests ParentLabel → Prop
    | .nil => True
    | .cons h hs => TopAncestral d context h ∧ TopAncestralForests d context hs
end

mutual
  theorem fillTop_annotate_ancestral (d : Nat) (positive : 0 < d)
      (context : ParentContext) (keyContext : KeyContext) (owners : List Nat)
      (projection : keyContext.map (fun entry => Parents.truncate d entry.1) = context)
      (e : NumericalExpr) :
      TopAncestral d context (fillTop d keyContext owners (Parents.annotate d context e)) := by
    cases e with
    | nil => trivial
    | cons a hs rest =>
      let numeric := Parents.label d context a
      let key := Keys.ofColumn d keyContext.length numeric (Parents.annotateForests d (context ++ [numeric]) hs)
      let top := topSearch d keyContext owners key ((numeric.parents[d - 1]?.join).map (· + 1) |>.getD 0)
      let extended : ParentLabel := {numeric with parents := numeric.parents ++ [top]}
      let next : KeyContext := keyContext ++ [(extended, key)]
      change (∀ root, (numeric.parents ++ [top])[d]?.join = some root →
        Parents.Ancestor (context ++ [numeric]) (d - 1) root context.length) ∧
        TopAncestralForests d (context ++ [numeric])
          (fillTopForests d next (owners ++ [keyContext.length])
            (Parents.annotateForests d (context ++ [numeric]) hs)) ∧
        TopAncestral d (context ++ [numeric])
          (fillTop d next owners (Parents.annotate d (context ++ [numeric]) rest))
      have nextProjection : next.map (fun entry => Parents.truncate d entry.1) = context ++ [numeric] := by
        simp only [next, List.map_append, List.map_cons, List.map_nil, projection]
        rw [show Parents.truncate d extended = numeric from Parents.truncate_extended_label d context a [top]]
      refine ⟨?_, fillTopForests_annotate_ancestral d positive _ next _ nextProjection hs,
        fillTop_annotate_ancestral d positive _ next owners nextProjection rest⟩
      intro root found
      have atTop : (numeric.parents ++ [top])[d]? = some top := by
        simpa only [show numeric.parents.length = d from Parents.label_width d context a] using
          (List.getElem?_concat_length : (numeric.parents ++ [top])[numeric.parents.length]? = some top)
      rw [atTop, Option.join_some] at found
      change topSearch d keyContext owners key
        ((numeric.parents[d - 1]?.join).map (· + 1) |>.getD 0) = some root at found
      cases input : numeric.parents[d - 1]?.join with
      | none => simp [input, topSearch] at found
      | some parent =>
        rw [input, Option.map_some, Option.getD_some] at found
        obtain ⟨_, _, _, _, _, _, path⟩ := topSearch_sound d keyContext owners key (parent + 1) root found
        have truncated := (Parents.Ancestor.truncate_iff (d := d)
          (context := keyContext.map Prod.fst) (by omega : d - 1 < d)).mpr path
        simp only [List.map_map, Function.comp_def, projection, Nat.add_sub_cancel] at truncated
        have edge : Parents.parent (context ++ [numeric]) (d - 1) context.length = some parent := by
          simp only [Parents.parent, List.getElem?_append_right (Nat.le_refl context.length),
            Nat.sub_self, List.getElem?_cons_zero, Option.bind_some, input]
        exact .up edge (truncated.prefix (List.prefix_append ..))
  theorem fillTopForests_annotate_ancestral (d : Nat) (positive : 0 < d)
      (context : ParentContext) (keyContext : KeyContext) (owners : List Nat)
      (projection : keyContext.map (fun entry => Parents.truncate d entry.1) = context)
      (hs : Forests (List Nat)) :
      TopAncestralForests d context
        (fillTopForests d keyContext owners (Parents.annotateForests d context hs)) := by
    cases hs with
    | nil => trivial
    | cons h rest =>
      exact ⟨fillTop_annotate_ancestral d positive context keyContext owners projection h,
        fillTopForests_annotate_ancestral d positive context keyContext owners projection rest⟩
end

theorem parents_topAncestral (d : Nat) (positive : 0 < d) (e : NumericalExpr) :
    TopAncestral d [] (parents d e) :=
  fillTop_annotate_ancestral d positive [] [] [] rfl e

theorem TopAncestral.last {d : Nat} {context : ParentContext} {e : ParentExpr}
    (safe : TopAncestral d context e) {a : ParentLabel} {hs : Forests ParentLabel}
    (found : last? e = some (a, hs)) :
    let before := outerContext d context (dropLast (e.map ParentLabel.coordinates))
    (∀ root, a.parents[d]?.join = some root →
      Parents.Ancestor (before ++ [Parents.label d before a.coordinates])
        (d - 1) root before.length) ∧
      TopAncestralForests d (before ++ [Parents.label d before a.coordinates]) hs := by
  cases e with
  | nil => simp [last?] at found
  | cons b ks rest =>
    cases rest with
    | nil =>
      have same : (b, ks) = (a, hs) := by simpa only [last?, Option.some.injEq] using found
      cases same
      simpa only [Expr.map, dropLast, outerContext] using ⟨safe.1, safe.2.1⟩
    | cons c js tail =>
      have result := safe.2.2.last (by simpa only [last?] using found)
      simpa only [Expr.map, dropLast, outerContext] using result

theorem TopAncestralForests.last {d : Nat} {context : ParentContext} {hs : Forests ParentLabel}
    (safe : TopAncestralForests d context hs) {h : ParentExpr}
    (found : lastForest? hs = some h) : TopAncestral d context h := by
  cases hs with
  | nil => simp [lastForest?] at found
  | cons first rest =>
    cases rest with
    | nil =>
      have same : first = h := by simpa only [lastForest?, Option.some.injEq] using found
      subst h
      exact safe.1
    | cons k ks => exact safe.2.last (by simpa only [lastForest?] using found)

theorem TopAncestral.layer {d : Nat} {context : ParentContext} {owner : Option Nat}
    {owners : List Nat} (depth : Nat) (e : ParentExpr) (safe : TopAncestral d context e)
    {part : ParentExpr} (selected : (spine e)[depth]? = some part)
    {layer : SpineLayer}
    (found : layerAt d context owner owners depth (e.map ParentLabel.coordinates) = some layer) :
    TopAncestral d layer.context part ∧ part.map ParentLabel.coordinates = layer.term := by
  induction depth generalizing context owner owners e part layer with
  | zero =>
    have samePart : e = part := by simpa only [spine, List.getElem?_cons_zero, Option.some.injEq] using selected
    have sameLayer : layer = ⟨context, owner, owners, e.map ParentLabel.coordinates⟩ := by
      simpa only [layerAt, Option.some.injEq] using found.symm
    subst part
    subst layer
    exact ⟨safe, rfl⟩
  | succ depth ih =>
    rw [spine_get_succ] at selected
    obtain ⟨h, child, below⟩ := Option.bind_eq_some_iff.mp selected
    obtain ⟨⟨a, hs⟩, last, forest⟩ := Option.bind_eq_some_iff.mp child
    have inside := (safe.last last).2.last forest
    have numericalLast := last_map ParentLabel.coordinates e
    rw [last, Option.map_some] at numericalLast
    have numericalForest := lastForest_map ParentLabel.coordinates hs
    rw [forest, Option.map_some] at numericalForest
    simp only [layerAt, numericalLast, Option.bind_some, numericalForest] at found
    exact ih h inside below found

/-- Highest-class selection in the frozen full parent table produces a
genuine numerical highest-row ancestor in the stopping column's actual
context. No ancestor hypothesis is supplied by the caller. -/
theorem selected_top_numerical_ancestor {d depth root : Nat} (positive : 0 < d)
    {e : NumericalExpr} {part : ParentExpr} {a : ParentLabel} {hs : Forests ParentLabel}
    (selected : (spine (parents d e))[depth]? = some part) (last : last? part = some (a, hs))
    (chosen : highestParent 0 a.parents = some (d, root))
    {layer : SpineLayer} (found : layerAt d [] none [] depth e = some layer)
    {terminal : List Nat} {attached : Forests (List Nat)}
    (atLast : last? layer.term = some (terminal, attached)) :
    let before := outerContext d layer.context (dropLast layer.term)
    Parents.Ancestor (before ++ [Parents.label d before terminal]) (d - 1) root before.length := by
  obtain ⟨safe, erase⟩ := (parents_topAncestral d positive e).layer depth (parents d e) selected
    (by simpa only [parents_erase] using found)
  have result := (safe.last last).1
  obtain ⟨_, _, atTop⟩ := highestParent_found a.parents 0 d root chosen
  have top : a.parents[d]?.join = some root := by
    simpa only [Nat.sub_zero, Option.join_some] using congrArg Option.join atTop
  have numericalLast := last_map ParentLabel.coordinates part
  rw [erase, last, Option.map_some, atLast] at numericalLast
  have coordinates : a.coordinates = terminal := (congrArg Prod.fst (Option.some.inj numericalLast)).symm
  simpa only [erase, coordinates] using result root top

end BTnSSBMS.Source
