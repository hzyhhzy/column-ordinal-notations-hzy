import BTnSSBMS.SourceRootHole

/-! The visible source list used by expand? reads the very same root
vector as the extracted template. In particular its difference vector
is not a replacement supplied to the copy lemma. -/
namespace BTnSSBMS.Source

theorem labels_drop_head (index : Nat) (e : Expr α) {a : α} {hs : Forests α} {rest : Expr α}
    (cut : drop index e = .cons a hs rest) : (labels e)[index]? = some a := by
  induction index generalizing e with
  | zero =>
    have same : e = .cons a hs rest := by simpa only [drop] using cut
    subst e
    simp only [labels, List.getElem?_cons_zero]
  | succ index ih =>
    cases e with
    | nil => simp [drop] at cut
    | cons b ks tail =>
      simpa only [labels, List.getElem?_cons_succ] using ih tail (by simpa only [drop] using cut)

theorem locateRoot_visible_label (sp : List (Expr α)) (root rootDepth index stopDepth : Nat)
    (found : locateRoot sp root = some (rootDepth, index)) (before : rootDepth ≤ stopDepth)
    {part : Expr α} (selected : sp[rootDepth]? = some part) :
    (((sp.take (stopDepth + 1)).flatMap labels)[root]?) = (labels part)[index]? := by
  induction sp generalizing root rootDepth index stopDepth with
  | nil => simp [locateRoot] at found
  | cons first rest ih =>
    rw [locateRoot] at found
    by_cases inside : root < length first
    · simp only [inside, if_true, Option.some.injEq] at found
      have atDepth := congrArg Prod.fst found
      have atIndex := congrArg Prod.snd found
      dsimp only at atDepth atIndex
      subst rootDepth
      subst index
      have same : first = part := by simpa only [List.getElem?_cons_zero, Option.some.injEq] using selected
      subst part
      simp only [List.take_succ_cons, List.flatMap_cons,
        List.getElem?_append_left (by rw [labels_length]; exact inside)]
    · simp only [inside, if_false, Option.map_eq_some_iff] at found
      obtain ⟨⟨below, position⟩, child, equal⟩ := found
      have atDepth := congrArg Prod.fst equal
      have atIndex := congrArg Prod.snd equal
      dsimp only at atDepth atIndex
      subst rootDepth
      subst index
      cases stopDepth with
      | zero => omega
      | succ stopDepth =>
        have result := ih (root - length first) below position stopDepth child (by omega)
          (by simpa only [List.getElem?_cons_succ] using selected)
        simp only [List.take_succ_cons, List.flatMap_cons,
          List.getElem?_append_right (by rw [labels_length]; omega : (labels first).length ≤ root), labels_length]
        exact result

theorem actual_root_coordinates {d root rootDepth index stopDepth : Nat} {e : NumericalExpr}
    (location : locateRoot (spine e) root = some (rootDepth, index)) (before : rootDepth ≤ stopDepth)
    {layer : SpineLayer} (found : layerAt d [] none [] rootDepth e = some layer)
    {a : List Nat} {hs : Forests (List Nat)} {rest : NumericalExpr}
    (cut : drop index layer.term = .cons a hs rest) :
    ((((spine e).take (stopDepth + 1)).flatMap labels)[root]?) = some a := by
  have selected := layerAt_term d [] none [] rootDepth e
  rw [found, Option.map_some] at selected
  rw [locateRoot_visible_label (spine e) root rootDepth index stopDepth location before selected.symm]
  exact labels_drop_head index layer.term cut

end BTnSSBMS.Source
