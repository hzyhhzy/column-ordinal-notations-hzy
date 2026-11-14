import BTnSSBMS.SourceLastOrder

/-! A real highest-class endpoint cannot be a leaf. This follows from
the frozen key search: no key is smaller than the empty key. -/
namespace BTnSSBMS.Source

theorem topSearch_empty (d : Nat) (context : KeyContext) (owners : List Nat) (cursor : Nat) :
    topSearch d context owners .nil cursor = none := by
  cases selected : topSearch d context owners .nil cursor with
  | none => rfl
  | some root =>
    obtain ⟨_, a, key, _, _, small, _⟩ := topSearch_sound d context owners .nil cursor root selected
    cases key <;> simp [Keys.compare, Forests.compare] at small

mutual
  def LeafNoTop (d : Nat) : ParentExpr → Prop
    | .nil => True
    | .cons a hs tail =>
      (hs = .nil → a.parents[d]?.join = none) ∧ LeafNoTopForests d hs ∧ LeafNoTop d tail
  def LeafNoTopForests (d : Nat) : Forests ParentLabel → Prop
    | .nil => True
    | .cons h hs => LeafNoTop d h ∧ LeafNoTopForests d hs
end

mutual
  theorem fillTop_annotate_leafNoTop (d : Nat) (context : ParentContext)
      (keyContext : KeyContext) (owners : List Nat) (e : NumericalExpr) :
      LeafNoTop d (fillTop d keyContext owners (Parents.annotate d context e)) := by
    cases e with
    | nil => trivial
    | cons a hs tail =>
      let numeric := Parents.label d context a
      let key := Keys.ofColumn d keyContext.length numeric (Parents.annotateForests d (context ++ [numeric]) hs)
      let top := topSearch d keyContext owners key ((numeric.parents[d - 1]?.join).map (· + 1) |>.getD 0)
      let next : KeyContext := keyContext ++ [({numeric with parents := numeric.parents ++ [top]}, key)]
      change (_ → (numeric.parents ++ [top])[d]?.join = none) ∧
        LeafNoTopForests d (fillTopForests d next (owners ++ [keyContext.length])
          (Parents.annotateForests d (context ++ [numeric]) hs)) ∧
        LeafNoTop d (fillTop d next owners (Parents.annotate d (context ++ [numeric]) tail))
      refine ⟨?_, fillTopForests_annotate_leafNoTop d _ next _ hs,
        fillTop_annotate_leafNoTop d _ next owners tail⟩
      intro empty
      have leaf : hs = .nil := by
        cases hs with
        | nil => rfl
        | cons h rest => simp [Parents.annotateForests, fillTopForests] at empty
      have topEmpty : top = none := by
        simp only [top, key, leaf, Parents.annotateForests, Keys.leaf_key, topSearch_empty]
      have atTop : (numeric.parents ++ [top])[d]? = some top := by
        simpa only [show numeric.parents.length = d from Parents.label_width d context a] using
          (List.getElem?_concat_length : (numeric.parents ++ [top])[numeric.parents.length]? = some top)
      rw [atTop, Option.join_some, topEmpty]
  theorem fillTopForests_annotate_leafNoTop (d : Nat) (context : ParentContext)
      (keyContext : KeyContext) (owners : List Nat) (hs : Forests (List Nat)) :
      LeafNoTopForests d (fillTopForests d keyContext owners (Parents.annotateForests d context hs)) := by
    cases hs with
    | nil => trivial
    | cons h rest => exact ⟨fillTop_annotate_leafNoTop d context keyContext owners h,
        fillTopForests_annotate_leafNoTop d context keyContext owners rest⟩
end

theorem LeafNoTop.last {d : Nat} {e : ParentExpr} (safe : LeafNoTop d e)
    {a : ParentLabel} {hs : Forests ParentLabel} (selected : last? e = some (a, hs)) :
    (hs = .nil → a.parents[d]?.join = none) ∧ LeafNoTopForests d hs := by
  cases e with
  | nil => simp [last?] at selected
  | cons b ks tail =>
    cases tail with
    | nil =>
      have same : (b, ks) = (a, hs) := by simpa only [last?, Option.some.injEq] using selected
      cases same
      exact ⟨safe.1, safe.2.1⟩
    | cons c js rest => exact safe.2.2.last (by simpa only [last?] using selected)

theorem LeafNoTopForests.last {d : Nat} {hs : Forests ParentLabel} (safe : LeafNoTopForests d hs)
    {h : ParentExpr} (selected : lastForest? hs = some h) : LeafNoTop d h := by
  cases hs with
  | nil => simp [lastForest?] at selected
  | cons k rest =>
    cases rest with
    | nil =>
      have same : k = h := by simpa only [lastForest?, Option.some.injEq] using selected
      subst h
      exact safe.1
    | cons u us => exact safe.2.last (by simpa only [lastForest?] using selected)

theorem LeafNoTop.spine {d : Nat} (depth : Nat) (e : ParentExpr) (safe : LeafNoTop d e)
    {part : ParentExpr} (selected : (spine e)[depth]? = some part) : LeafNoTop d part := by
  induction depth generalizing e part with
  | zero =>
    have same : e = part := by simpa only [Source.spine, List.getElem?_cons_zero, Option.some.injEq] using selected
    subst part
    exact safe
  | succ depth ih =>
    rw [spine_get_succ] at selected
    obtain ⟨h, atChild, below⟩ := Option.bind_eq_some_iff.mp selected
    obtain ⟨⟨a, hs⟩, last, child⟩ := Option.bind_eq_some_iff.mp atChild
    exact ih h ((safe.last last).2.last child) below

theorem selected_high_terminal_attached {d root depth : Nat} {e stop : NumericalExpr}
    (stopSelected : (spine e)[depth]? = some stop)
    {terminal : List Nat} {attached : Forests (List Nat)}
    (stopLast : last? stop = some (terminal, attached))
    {parentStop : ParentExpr} {parentTerminal : ParentLabel} {parentAttached : Forests ParentLabel}
    (parentSelected : (spine (parents d e))[depth]? = some parentStop)
    (parentLast : last? parentStop = some (parentTerminal, parentAttached))
    (chosen : highestParent 0 parentTerminal.parents = some (d, root)) : attached ≠ .nil := by
  have safe : LeafNoTop d (parents d e) := fillTop_annotate_leafNoTop d [] [] [] e
  have noLeaf := ((safe.spine depth (parents d e) parentSelected).last parentLast).1
  have mapped := congrArg (fun term : NumericalExpr => (spine term)[depth]?) (parents_erase d e)
  simp only [spine_map, List.getElem?_map, parentSelected, Option.map_some, stopSelected] at mapped
  have last := last_map ParentLabel.coordinates parentStop
  rw [Option.some.inj mapped, stopLast, parentLast, Option.map_some] at last
  have forests : parentAttached.map ParentLabel.coordinates = attached :=
    (congrArg Prod.snd (Option.some.inj last)).symm
  intro empty
  have parentEmpty : parentAttached = .nil := by
    cases parentAttached with
    | nil => rfl
    | cons h hs => simp [Forests.map, empty] at forests
  have absent := noLeaf parentEmpty
  have present := (highestParent_found parentTerminal.parents 0 d root chosen).2.2
  simp only [Nat.sub_zero] at present
  rw [present, Option.join_some] at absent
  cases absent

end BTnSSBMS.Source
