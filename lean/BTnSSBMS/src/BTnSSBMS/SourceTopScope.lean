import BTnSSBMS.SourceSpineHole

/-!
Every actual highest parent excludes the whole open-owner stack.
The property below follows the frozen fillTop traversal, including
independent sibling-forest scopes. No standardness is needed.
-/
namespace BTnSSBMS.Source

mutual
  def TopUnowned (d offset : Nat) (owners : List Nat) : ParentExpr → Prop
    | .nil => True
    | .cons a hs rest =>
      (∀ root, a.parents[d]?.join = some root → root < offset ∧ root ∉ owners) ∧
      TopUnownedForests d (offset + 1) (owners ++ [offset]) hs ∧
      TopUnowned d (offset + 1) owners rest
  def TopUnownedForests (d offset : Nat) (owners : List Nat) : Forests ParentLabel → Prop
    | .nil => True
    | .cons h hs => TopUnowned d offset owners h ∧ TopUnownedForests d offset owners hs
end

mutual
  theorem fillTop_annotate_unowned (d : Nat) (context : ParentContext)
      (keyContext : KeyContext) (owners : List Nat) (e : NumericalExpr) :
      TopUnowned d keyContext.length owners (fillTop d keyContext owners (Parents.annotate d context e)) := by
    cases e with
    | nil => trivial
    | cons a hs rest =>
      let numeric := Parents.label d context a
      let key := Keys.ofColumn d keyContext.length numeric (Parents.annotateForests d (context ++ [numeric]) hs)
      let top := topSearch d keyContext owners key ((numeric.parents[d - 1]?.join).map (· + 1) |>.getD 0)
      let next : KeyContext := keyContext ++ [({numeric with parents := numeric.parents ++ [top]}, key)]
      change (∀ root, (numeric.parents ++ [top])[d]?.join = some root → root < keyContext.length ∧ root ∉ owners) ∧
        TopUnownedForests d (keyContext.length + 1) (owners ++ [keyContext.length])
          (fillTopForests d next (owners ++ [keyContext.length]) (Parents.annotateForests d (context ++ [numeric]) hs)) ∧
        TopUnowned d (keyContext.length + 1) owners
          (fillTop d next owners (Parents.annotate d (context ++ [numeric]) rest))
      have size : next.length = keyContext.length + 1 := by simp only [next, List.length_append, List.length_cons, List.length_nil]
      refine ⟨?_, ?_, ?_⟩
      · intro root found
        have selected : (numeric.parents ++ [top])[d]? = some top := by
          simpa only [show numeric.parents.length = d from Parents.label_width d context a] using
            (List.getElem?_concat_length : (numeric.parents ++ [top])[numeric.parents.length]? = some top)
        rw [selected, Option.join_some] at found
        obtain ⟨_, b, k, atRoot, unowned, _⟩ := topSearch_sound d keyContext owners _ _ root found
        refine ⟨(List.getElem?_eq_some_iff.mp atRoot).choose, ?_⟩
        simpa only [List.contains_eq_mem, decide_eq_false_iff_not] using unowned
      · rw [← size]
        exact fillTopForests_annotate_unowned d (context ++ [numeric]) next (owners ++ [keyContext.length]) hs
      · rw [← size]
        exact fillTop_annotate_unowned d (context ++ [numeric]) next owners rest
  theorem fillTopForests_annotate_unowned (d : Nat) (context : ParentContext)
      (keyContext : KeyContext) (owners : List Nat) (hs : Forests (List Nat)) :
      TopUnownedForests d keyContext.length owners
        (fillTopForests d keyContext owners (Parents.annotateForests d context hs)) := by
    cases hs with
    | nil => trivial
    | cons h rest =>
      exact ⟨fillTop_annotate_unowned d context keyContext owners h,
        fillTopForests_annotate_unowned d context keyContext owners rest⟩
end

theorem parents_unowned (d : Nat) (e : NumericalExpr) : TopUnowned d 0 [] (parents d e) :=
  fillTop_annotate_unowned d [] [] [] e

theorem length_dropLast (e : Expr α) : length (dropLast e) = length e - 1 := by
  cases e with
  | nil => simp [dropLast, length]
  | cons a hs rest =>
    cases rest with
    | nil => simp [dropLast, length]
    | cons b ks tail =>
      rw [dropLast, length, length_dropLast (.cons b ks tail)]
      simp only [length]
      omega

theorem last_length_positive (e : Expr α) {a : α} {hs : Forests α}
    (found : last? e = some (a, hs)) : 0 < length e := by
  cases e with
  | nil => simp [last?] at found
  | cons b ks rest => simp only [length]; omega

theorem TopUnowned.last {d offset : Nat} {owners : List Nat} {e : ParentExpr}
    (safe : TopUnowned d offset owners e) {a : ParentLabel} {hs : Forests ParentLabel}
    (found : last? e = some (a, hs)) :
    (∀ root, a.parents[d]?.join = some root → root < offset + length e - 1 ∧ root ∉ owners) ∧
      TopUnownedForests d (offset + length e) (owners ++ [offset + length e - 1]) hs := by
  cases e with
  | nil => simp [last?] at found
  | cons b ks rest =>
    cases rest with
    | nil =>
      have same : (b, ks) = (a, hs) := by simpa only [last?, Option.some.injEq] using found
      cases same
      simpa only [length, Nat.add_zero, Nat.add_sub_cancel] using ⟨safe.1, safe.2.1⟩
    | cons c js tail =>
      have result := safe.2.2.last (by simpa only [last?] using found)
      simpa only [length, Nat.add_assoc] using result

theorem TopUnownedForests.last {d offset : Nat} {owners : List Nat} {hs : Forests ParentLabel}
    (safe : TopUnownedForests d offset owners hs) {h : ParentExpr}
    (found : lastForest? hs = some h) : TopUnowned d offset owners h := by
  cases hs with
  | nil => simp [lastForest?] at found
  | cons first rest =>
    cases rest with
    | nil =>
      have same : first = h := by simpa only [lastForest?, Option.some.injEq] using found
      subst h
      exact safe.1
    | cons k ks => exact safe.2.last (by simpa only [lastForest?] using found)

def ownerIndices (offset : Nat) : List (Expr α) → List Nat
  | [] => []
  | e :: rest => (offset + length e - 1) :: ownerIndices (offset + length e) rest

theorem layerAt_owner_indices {d : Nat} {context : ParentContext} {owner : Option Nat}
    {owners : List Nat} (depth : Nat) (e : NumericalExpr) {layer : SpineLayer}
    (found : layerAt d context owner owners depth e = some layer) :
    layer.owners = owners ++ ownerIndices context.length ((spine e).take depth) := by
  induction depth generalizing context owner owners e layer with
  | zero =>
    have same : layer = ⟨context, owner, owners, e⟩ := by
      simpa only [layerAt, Option.some.injEq] using found.symm
    subst layer
    simp [ownerIndices]
  | succ depth ih =>
    simp only [layerAt, Option.bind_eq_some_iff] at found
    obtain ⟨⟨a, hs⟩, last, h, child, next⟩ := found
    have positive := last_length_positive e last
    have result := ih h next
    simp only [List.length_append, List.length_cons, List.length_nil, outerContext_length, length_dropLast] at result
    rw [spine_eq_child (by simp [lastChild?, last, child] : lastChild? e = some h)]
    simp only [List.take_succ_cons, ownerIndices]
    have before : context.length + (length e - 1) = context.length + length e - 1 := by omega
    have after : context.length + length e - 1 + 1 = context.length + length e := by omega
    simpa only [before, after, List.append_assoc, List.cons_append, List.nil_append] using result

theorem TopUnowned.spine {d offset : Nat} {owners : List Nat} (depth : Nat) (e : ParentExpr)
    (safe : TopUnowned d offset owners e) {part : ParentExpr}
    (found : (spine e)[depth]? = some part) :
    TopUnowned d (offset + (((spine e).take depth).map length).sum)
      (owners ++ ownerIndices offset ((spine e).take depth)) part := by
  induction depth generalizing offset owners e part with
  | zero =>
    have same : e = part := by simpa only [Source.spine, List.getElem?_cons_zero, Option.some.injEq] using found
    subst part
    simpa only [List.take_zero, List.map_nil, List.sum_nil, Nat.add_zero, ownerIndices, List.append_nil] using safe
  | succ depth ih =>
    rw [spine_get_succ] at found
    obtain ⟨h, child, below⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨⟨a, hs⟩, last, forest⟩ := Option.bind_eq_some_iff.mp child
    have inside := (safe.last last).2.last forest
    have result := ih h inside below
    rw [spine_eq_child (by simp [lastChild?, last, forest] : lastChild? e = some h)]
    simpa only [List.take_succ_cons, List.map_cons, List.sum_cons, ownerIndices,
      List.append_assoc, List.cons_append, List.nil_append, Nat.add_assoc] using result

end BTnSSBMS.Source
