import BTnSSBMS.SourceSpine

/-!
The computed stopping layer and the copy-template hole are the same
scoped site. Owner indices record genuine open forests, not columns
of a flattened traversal.
-/
namespace BTnSSBMS.Source

theorem holeSite_zero_last (d : Nat) (context : ParentContext) (owner : Option Nat)
    (e : NumericalExpr) {a : List Nat} {hs : Forests (List Nat)}
    (last : last? e = some (a, hs)) :
    holeSite d context owner 0 e = some ⟨outerContext d context (dropLast e), owner, a, hs⟩ := by
  cases e with
  | nil => simp [last?] at last
  | cons b ks rest =>
    cases rest with
    | nil =>
      have same : (b, ks) = (a, hs) := by simpa only [last?, Option.some.injEq] using last
      cases same
      simp only [holeSite, dropLast, outerContext]
    | cons c js tail =>
      simpa only [holeSite, dropLast, outerContext] using
        holeSite_zero_last d (context ++ [Parents.label d context b]) owner (.cons c js tail)
          (by simpa only [last?] using last)

theorem holeSiteForests_last (d : Nat) (context : ParentContext) (owner depth : Nat)
    (hs : Forests (List Nat)) :
    holeSiteForests d context owner depth hs =
      (lastForest? hs).bind (holeSite d context (some owner) depth) := by
  cases hs with
  | nil => simp only [holeSiteForests, lastForest?, Option.bind_none]
  | cons h rest =>
    cases rest with
    | nil => simp only [holeSiteForests, lastForest?, Option.bind_some]
    | cons k ks =>
      simpa only [holeSiteForests, lastForest?] using holeSiteForests_last d context owner depth (.cons k ks)

theorem holeSite_succ_last (d : Nat) (context : ParentContext) (owner : Option Nat)
    (depth : Nat) (e : NumericalExpr) {a : List Nat} {hs : Forests (List Nat)}
    (last : last? e = some (a, hs)) :
    holeSite d context owner (depth + 1) e =
      holeSiteForests d (outerContext d context e) (a[0]?.getD 0) depth hs := by
  cases e with
  | nil => simp [last?] at last
  | cons b ks rest =>
    cases rest with
    | nil =>
      have same : (b, ks) = (a, hs) := by simpa only [last?, Option.some.injEq] using last
      cases same
      simp only [holeSite, outerContext]
    | cons c js tail =>
      simpa only [holeSite, outerContext] using
        holeSite_succ_last d (context ++ [Parents.label d context b]) owner depth (.cons c js tail)
          (by simpa only [last?] using last)

theorem layerAt_holeSite {d : Nat} {context : ParentContext} {owner : Option Nat} {owners : List Nat}
    (depth : Nat) (e : NumericalExpr) {layer : SpineLayer}
    (found : layerAt d context owner owners depth e = some layer)
    {a : List Nat} {hs : Forests (List Nat)} (last : last? layer.term = some (a, hs)) :
    holeSite d context owner depth e =
      some ⟨outerContext d layer.context (dropLast layer.term), layer.owner, a, hs⟩ := by
  induction depth generalizing context owner owners e layer with
  | zero =>
    have same : layer = ⟨context, owner, owners, e⟩ := by
      simpa only [layerAt, Option.some.injEq] using found.symm
    subst layer
    exact holeSite_zero_last d context owner e last
  | succ depth ih =>
    simp only [layerAt, Option.bind_eq_some_iff] at found
    obtain ⟨⟨b, ks⟩, atLast, h, child, next⟩ := found
    rw [holeSite_succ_last d context owner depth e atLast, holeSiteForests_last, child, Option.bind_some,
      outerContext_last context e atLast]
    exact ih h next last

theorem holeSite_of_spine_last {d : Nat} (context : ParentContext) (owner : Option Nat) (owners : List Nat)
    {depth : Nat} {e part : NumericalExpr} (selected : (spine e)[depth]? = some part)
    {a : List Nat} {hs : Forests (List Nat)} (last : last? part = some (a, hs)) :
    ∃ layer, layerAt d context owner owners depth e = some layer ∧ layer.term = part ∧
      holeSite d context owner depth e =
        some ⟨outerContext d layer.context (dropLast part), layer.owner, a, hs⟩ := by
  obtain ⟨layer, found, same⟩ := layerAt_exists context owner owners selected
  refine ⟨layer, found, same, ?_⟩
  have result := layerAt_holeSite depth e found (by rw [same]; exact last)
  simpa only [same] using result

theorem holeSite_drop (d : Nat) (context : ParentContext) (owner : Option Nat)
    (depth index : Nat) (e : NumericalExpr) (inside : index < length e) :
    holeSite d (dropContext d context index e) owner depth (drop index e) =
      holeSite d context owner depth e := by
  induction index generalizing context e with
  | zero => simp only [dropContext, drop]
  | succ index ih =>
    cases e with
    | nil => simp [length] at inside
    | cons a hs rest =>
      have room : index < length rest := by simp only [length] at inside; omega
      cases rest with
      | nil => simp [length] at room
      | cons b ks tail =>
        simpa only [dropContext, drop, holeSite] using
          ih (context ++ [Parents.label d context a]) (.cons b ks tail) room

theorem layerAt_succ_drop (d : Nat) (context : ParentContext) (owner : Option Nat) (owners : List Nat)
    (depth index : Nat) (e : NumericalExpr) (inside : index < length e) :
    layerAt d (dropContext d context index e) owner owners (depth + 1) (drop index e) =
      layerAt d context owner owners (depth + 1) e := by
  induction index generalizing context e with
  | zero => simp only [dropContext, drop]
  | succ index ih =>
    cases e with
    | nil => simp [length] at inside
    | cons a hs rest =>
      have room : index < length rest := by simp only [length] at inside; omega
      cases rest with
      | nil => simp [length] at room
      | cons b ks tail =>
        simpa only [dropContext, drop, layerAt, dropLast, outerContext, last?] using
          ih (context ++ [Parents.label d context a]) (.cons b ks tail) room

theorem layerAt_singleton_owner {d : Nat} {context : ParentContext} {owner : Option Nat}
    {owners : List Nat} (depth : Nat) (a : List Nat) (hs : Forests (List Nat)) {layer : SpineLayer}
    (found : layerAt d context owner owners (depth + 1) (.cons a hs .nil) = some layer) :
    context.length ∈ layer.owners := by
  simp only [layerAt, last?, Option.bind_some, dropLast, outerContext, Option.bind_eq_some_iff] at found
  obtain ⟨h, _, next⟩ := found
  exact (layerAt_owners_prefix depth h next).subset (by simp)

/-- A highest-class root excluded from the open-owner indices cannot
be the last outer column of its template. The same-forest case instead
uses the strict earlier-root index; both cases refer to computed sites. -/
theorem root_tail_of_unowned {d : Nat} {context : ParentContext} {owners : List Nat}
    {a : List Nat} {hs : Forests (List Nat)} {rest : NumericalExpr} {depth : Nat} {layer : SpineLayer}
    (found : layerAt d context none owners depth (.cons a hs rest) = some layer)
    (later : context.length < (outerContext d layer.context (dropLast layer.term)).length)
    (unowned : context.length ∉ layer.owners) : rest ≠ .nil := by
  intro empty
  subst rest
  cases depth with
  | zero =>
    have same : layer = ⟨context, none, owners, .cons a hs .nil⟩ := by
      simpa only [layerAt, Option.some.injEq] using found.symm
    subst layer
    simp only [dropLast, outerContext] at later
    omega
  | succ depth => exact unowned (layerAt_singleton_owner depth a hs found)

end BTnSSBMS.Source
