import BTnSSBMS.SourceAnnotatedSpine

/-!
Exact activation marks on the root suffix extracted by the original
spine/drop algorithm. Before the root, history is extended by zeros;
closed sibling forests remain outside that history.
-/
namespace BTnSSBMS.Source

theorem mark_drop_to_root (cap root : Nat) (history : List Nat) (index : Nat) (e : ParentExpr)
    (offset : history.length + index = root) :
    drop index (mark cap root history e) =
      mark cap root (history ++ List.replicate index 0) (drop index e) := by
  induction index generalizing history e with
  | zero => simp only [drop, List.replicate_zero, List.append_nil]
  | succ index ih =>
    cases e with
    | nil => simp only [mark, drop]
    | cons a hs rest =>
      have before : history.length < root := by omega
      simp only [mark, before, if_true, drop]
      have next := ih (history ++ [0]) rest (by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega)
      simpa only [List.replicate_succ, List.append_assoc, List.cons_append, List.nil_append] using next

theorem mark_last_before (cap root : Nat) (history : List Nat) (e : ParentExpr)
    {a : ParentLabel} {hs : Forests ParentLabel} (found : last? e = some (a, hs))
    (before : history.length + length e ≤ root) :
    last? (mark cap root history e) =
      some ((a.coordinates, 0), markForests cap root (history ++ List.replicate (length e) 0) hs) := by
  cases e with
  | nil => simp [last?] at found
  | cons b ks rest =>
    have old : history.length < root := by simp only [length] at before; omega
    cases rest with
    | nil =>
      have same : (b, ks) = (a, hs) := by simpa only [last?, Option.some.injEq] using found
      cases same
      simp only [mark, old, if_true, decide_true, Bool.and_false, Bool.false_eq_true,
        if_false, last?, length, Nat.add_zero, List.replicate_succ, List.replicate_zero]
    | cons c js tail =>
      have next := mark_last_before cap root (history ++ [0]) (.cons c js tail)
        (by simpa only [last?] using found) (by
          simp only [List.length_append, List.length_cons, List.length_nil, length] at *
          omega)
      simpa only [mark, old, if_true, last?, length, Nat.one_add, List.replicate_succ, List.replicate_zero,
        List.append_assoc, List.cons_append, List.nil_append] using next

theorem markForests_last (cap root : Nat) (history : List Nat) (hs : Forests ParentLabel)
    {h : ParentExpr} (found : lastForest? hs = some h) :
    lastForest? (markForests cap root history hs) = some (mark cap root history h) := by
  cases hs with
  | nil => simp [lastForest?] at found
  | cons first rest =>
    cases rest with
    | nil =>
      have same : first = h := by simpa only [lastForest?, Option.some.injEq] using found
      subst h
      simp only [markForests, lastForest?]
    | cons k ks =>
      simpa only [markForests, lastForest?] using
        markForests_last cap root history (.cons k ks) (by simpa only [lastForest?] using found)

theorem mark_child_before (cap root : Nat) (history : List Nat) (e : ParentExpr)
    {h : ParentExpr} (found : lastChild? e = some h) (before : history.length + length e ≤ root) :
    lastChild? (mark cap root history e) =
      some (mark cap root (history ++ List.replicate (length e) 0) h) := by
  obtain ⟨⟨a, hs⟩, last, forest⟩ := Option.bind_eq_some_iff.mp found
  simp only [lastChild?, mark_last_before cap root history e last before, Option.bind_some]
  exact markForests_last cap root _ hs forest

theorem mark_spine_before (cap root : Nat) (history : List Nat) (depth : Nat) (e : ParentExpr)
    {part : ParentExpr} (selected : (spine e)[depth]? = some part)
    (before : history.length + (((spine e).take depth).map length).sum ≤ root) :
    (spine (mark cap root history e))[depth]? =
      some (mark cap root (history ++ List.replicate ((((spine e).take depth).map length).sum) 0) part) := by
  induction depth generalizing history e part with
  | zero =>
    have same : e = part := by simpa only [spine, List.getElem?_cons_zero, Option.some.injEq] using selected
    subst part
    simp only [List.take_zero, List.map_nil, List.sum_nil, List.replicate_zero, List.append_nil]
    rfl
  | succ depth ih =>
    rw [spine_get_succ] at selected
    obtain ⟨h, child, below⟩ := Option.bind_eq_some_iff.mp selected
    have shape := spine_eq_child child
    have prefixSize : (((spine e).take (depth + 1)).map length).sum =
        length e + (((spine h).take depth).map length).sum := by
      simp only [shape, List.take_succ_cons, List.map_cons, List.sum_cons]
    rw [prefixSize] at before
    rw [spine_get_succ, mark_child_before cap root history e child (by omega), Option.bind_some]
    have result := ih (history ++ List.replicate (length e) 0) h below (by
      simp only [List.length_append, List.length_replicate]
      omega)
    simpa only [prefixSize, List.append_assoc, List.replicate_append_replicate] using result

theorem marked_annotate_layer {d : Nat} (cap root : Nat) {context : ParentContext}
    {owner : Option Nat} {owners : List Nat} (depth : Nat) (e : NumericalExpr) {layer : SpineLayer}
    (found : layerAt d context owner owners depth e = some layer)
    (before : layer.context.length ≤ root) :
    (spine (mark cap root (List.replicate context.length 0) (Parents.annotate d context e)))[depth]? =
      some (mark cap root (List.replicate layer.context.length 0) (Parents.annotate d layer.context layer.term)) := by
  have size := layerAt_context_length depth e found
  have result := mark_spine_before cap root (List.replicate context.length 0) depth
    (Parents.annotate d context e) (annotate_layer depth e found) (by
      rw [List.length_replicate, annotated_spine_prefix_length]
      omega)
  rw [annotated_spine_prefix_length, List.replicate_append_replicate, ← size] at result
  exact result

/-- The literal marked root suffix, including every nested attachment,
is the canonical root template used by the iterative-copy theorems. -/
theorem actual_marked_root_piece {d cap root depth index : Nat} {e : NumericalExpr}
    (bounded : cap ≤ d) (location : locateRoot (spine e) root = some (depth, index))
    {layer : SpineLayer} (found : layerAt d [] none [] depth e = some layer) :
    ∃ part, (spine (mark cap root [] (parents d e)))[depth]? = some part ∧
      drop index part = mark cap root (List.replicate root 0)
        (Parents.annotate d (dropContext d layer.context index layer.term) (drop index layer.term)) ∧
      (dropContext d layer.context index layer.term).length = root := by
  obtain ⟨piece, selected, inside, offset⟩ := locateRoot_sound (spine e) root depth index location
  have numeric := layerAt_term d [] none [] depth e
  rw [found, Option.map_some, selected] at numeric
  have same : layer.term = piece := Option.some.inj numeric
  have size := layerAt_context_length depth e found
  simp only [List.length_nil, Nat.zero_add] at size
  have rootIndex : layer.context.length + index = root := by omega
  have chosen := marked_annotate_layer cap root depth e found (by omega)
  simp only [List.length_nil, List.replicate_zero] at chosen
  rw [← mark_parents_eq_numeric d cap root [] bounded e] at chosen
  refine ⟨_, chosen, ?_, ?_⟩
  · rw [mark_drop_to_root cap root _ index _ (by rw [List.length_replicate]; exact rootIndex),
      List.replicate_append_replicate, rootIndex, drop_annotate]
  · rw [dropContext_length d layer.context index layer.term (by rw [same]; exact inside)]
    exact rootIndex

end BTnSSBMS.Source
