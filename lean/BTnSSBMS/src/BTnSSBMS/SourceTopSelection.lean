import BTnSSBMS.SourceTopScope

/-!
Highest-parent selection at the actual stopping layer, connected to the
unannotated scoped spine used by locateRoot and the copy-template lemmas.
-/
namespace BTnSSBMS.Source

theorem length_map (f : α → β) (e : Expr α) : length (e.map f) = length e := by
  cases e with
  | nil => rfl
  | cons a hs rest => simp only [Expr.map, length, length_map f rest]

theorem last_map (f : α → β) (e : Expr α) :
    last? (e.map f) = (last? e).map (fun c => (f c.1, c.2.map f)) := by
  cases e with
  | nil => simp only [Expr.map, last?, Option.map_none]
  | cons a hs rest =>
    cases rest with
    | nil => simp only [Expr.map, last?, Option.map_some]
    | cons b ks tail => simpa only [Expr.map, last?] using last_map f (.cons b ks tail)

theorem lastForest_map (f : α → β) (hs : Forests α) :
    lastForest? (hs.map f) = (lastForest? hs).map (Expr.map f) := by
  cases hs with
  | nil => simp only [Forests.map, lastForest?, Option.map_none]
  | cons h rest =>
    cases rest with
    | nil => simp only [Forests.map, lastForest?, Option.map_some]
    | cons k ks => simpa only [Forests.map, lastForest?] using lastForest_map f (.cons k ks)

mutual
  theorem innerSpine_map (f : α → β) (e : Expr α) :
      innerSpine (e.map f) = (innerSpine e).map (Expr.map f) := by
    cases e with
    | nil => simp only [Expr.map, innerSpine, List.map_nil]
    | cons a hs rest =>
      cases rest with
      | nil => simp only [Expr.map, innerSpine, forestSpine_map]
      | cons b ks tail => simpa only [Expr.map, innerSpine] using innerSpine_map f (.cons b ks tail)
  theorem forestSpine_map (f : α → β) (hs : Forests α) :
      forestSpine (hs.map f) = (forestSpine hs).map (Expr.map f) := by
    cases hs with
    | nil => simp only [Forests.map, forestSpine, List.map_nil]
    | cons h rest =>
      cases rest with
      | nil => simp only [Forests.map, forestSpine, List.map_cons, innerSpine_map]
      | cons k ks => simpa only [Forests.map, forestSpine] using forestSpine_map f (.cons k ks)
end

theorem spine_map (f : α → β) (e : Expr α) :
    spine (e.map f) = (spine e).map (Expr.map f) := by
  simp only [spine, innerSpine_map, List.map_cons]

theorem ownerIndices_map (f : α → β) (offset : Nat) (sp : List (Expr α)) :
    ownerIndices offset (sp.map (Expr.map f)) = ownerIndices offset sp := by
  induction sp generalizing offset with
  | nil => rfl
  | cons first rest ih => simp only [List.map_cons, ownerIndices, length_map, ih]

/-- No finite legality, standardness or externally certified owner list
is assumed. This uses the actual parents function and highestParent. -/
theorem selected_top_scoped {d : Nat} {e : NumericalExpr} {depth root : Nat}
    {part : ParentExpr} {a : ParentLabel} {hs : Forests ParentLabel}
    (selected : (spine (parents d e))[depth]? = some part)
    (last : last? part = some (a, hs))
    (chosen : highestParent 0 a.parents = some (d, root))
    {layer : SpineLayer} (found : layerAt d [] none [] depth e = some layer) :
    root < (outerContext d layer.context (dropLast layer.term)).length ∧ root ∉ layer.owners := by
  have state := (parents_unowned d e).spine depth (parents d e) selected
  have head := (state.last last).1
  obtain ⟨_, _, atTop⟩ := highestParent_found a.parents 0 d root chosen
  have top : a.parents[d]?.join = some root := by
    simpa only [Nat.sub_zero, atTop, Option.join_some] using
      congrArg Option.join atTop
  have safe := head root top
  have numericSpine : spine e = (spine (parents d e)).map (Expr.map ParentLabel.coordinates) := by
    rw [← spine_map, parents_erase]
  have term : layer.term = part.map ParentLabel.coordinates := by
    have numeric := layerAt_term d [] none [] depth e
    rw [found, Option.map_some, numericSpine, List.getElem?_map, selected, Option.map_some] at numeric
    exact Option.some.inj numeric
  have owners := layerAt_owner_indices depth e found
  have contextSize := layerAt_context_length depth e found
  rw [numericSpine, ← List.map_take, ownerIndices_map] at owners
  rw [numericSpine, ← List.map_take, List.map_map] at contextSize
  simp only [Function.comp_def, length_map, List.length_nil, Nat.zero_add] at contextSize
  change layer.context.length = (((spine (parents d e)).take depth).map length).sum at contextSize
  simp only [List.length_nil, List.nil_append] at owners
  rw [owners, outerContext_length, length_dropLast, term, length_map, contextSize]
  have positive := last_length_positive part last
  simp only [Nat.zero_add] at safe
  exact ⟨by omega, safe.2⟩

theorem drop_length (index : Nat) (e : Expr α) : length (drop index e) = length e - index := by
  induction index generalizing e with
  | zero => simp only [drop, Nat.sub_zero]
  | succ index ih =>
    cases e with
    | nil => simp only [drop, length, Nat.zero_sub]
    | cons a hs rest =>
      rw [drop, ih, length]
      omega

theorem ownerIndices_selected (offset : Nat) (sp : List (Expr α)) (depth : Nat) {part : Expr α}
    (selected : sp[depth]? = some part) :
    offset + ((sp.take depth).map length).sum + length part - 1 ∈ ownerIndices offset sp := by
  induction sp generalizing offset depth with
  | nil => simp at selected
  | cons first rest ih =>
    cases depth with
    | zero =>
      have same : first = part := by simpa only [List.getElem?_cons_zero, Option.some.injEq] using selected
      subst part
      simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.add_zero, ownerIndices, List.mem_cons]
      exact Or.inl trivial
    | succ depth =>
      have next : rest[depth]? = some part := by simpa only [List.getElem?_cons_succ] using selected
      have result := ih (offset + length first) depth next
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons, ownerIndices, List.mem_cons]
      exact Or.inr (by simpa only [Nat.add_assoc] using result)

theorem locateRoot_before (sp : List (Expr α)) (root rootDepth index stopDepth : Nat)
    (found : locateRoot sp root = some (rootDepth, index)) {stop : Expr α}
    (selected : sp[stopDepth]? = some stop)
    (before : root < ((sp.take stopDepth).map length).sum + length stop) : rootDepth ≤ stopDepth := by
  induction sp generalizing root rootDepth index stopDepth with
  | nil => simp [locateRoot] at found
  | cons first rest ih =>
    rw [locateRoot] at found
    by_cases inside : root < length first
    · simp only [inside, if_true, Option.some.injEq] at found
      have equal := congrArg Prod.fst found
      dsimp only at equal
      omega
    · simp only [inside, if_false, Option.map_eq_some_iff] at found
      obtain ⟨⟨below, position⟩, child, equal⟩ := found
      have atDepth := congrArg Prod.fst equal
      have atIndex := congrArg Prod.snd equal
      dsimp only at atDepth atIndex
      subst rootDepth
      subst index
      cases stopDepth with
      | zero =>
        have same : first = stop := by simpa only [List.getElem?_cons_zero, Option.some.injEq] using selected
        subst stop
        simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add] at before
        omega
      | succ stopDepth =>
        have next : rest[stopDepth]? = some stop := by simpa only [List.getElem?_cons_succ] using selected
        have bound : root - length first < ((rest.take stopDepth).map length).sum + length stop := by
          simp only [List.take_succ_cons, List.map_cons, List.sum_cons] at before
          omega
        have result := ih (root - length first) below position stopDepth child next bound
        omega

/-- The actual highest-class selection forces a genuinely nonterminal
root suffix. The open-owner exclusion and the strict earlier index are
derived above from fillTop, not assumptions about the root template. -/
theorem selected_top_root_tail {d : Nat} {e : NumericalExpr} {stopDepth root rootDepth index : Nat}
    {parentPart : ParentExpr} {terminal : ParentLabel} {attached : Forests ParentLabel}
    (selected : (spine (parents d e))[stopDepth]? = some parentPart)
    (last : last? parentPart = some (terminal, attached))
    (chosen : highestParent 0 terminal.parents = some (d, root))
    {stopLayer rootLayer : SpineLayer}
    (atStop : layerAt d [] none [] stopDepth e = some stopLayer)
    (location : locateRoot (spine e) root = some (rootDepth, index))
    (atRoot : layerAt d [] none [] rootDepth e = some rootLayer)
    {a : List Nat} {hs : Forests (List Nat)} {rest : NumericalExpr}
    (cut : drop index rootLayer.term = .cons a hs rest) : rest ≠ .nil := by
  have safe := selected_top_scoped selected last chosen atStop
  have stopLookup : (spine e)[stopDepth]? = some stopLayer.term := by
    have result := layerAt_term d [] none [] stopDepth e
    simpa only [atStop, Option.map_some] using result.symm
  have rootLookup : (spine e)[rootDepth]? = some rootLayer.term := by
    have result := layerAt_term d [] none [] rootDepth e
    simpa only [atRoot, Option.map_some] using result.symm
  obtain ⟨piece, lookup, room, offset⟩ := locateRoot_sound (spine e) root rootDepth index location
  have same : piece = rootLayer.term := Option.some.inj (lookup.symm.trans rootLookup)
  subst piece
  have stopSize := layerAt_context_length stopDepth e atStop
  simp only [List.length_nil, Nat.zero_add] at stopSize
  rw [outerContext_length, length_dropLast, stopSize] at safe
  have depthBound := locateRoot_before (spine e) root rootDepth index stopDepth location stopLookup
    (by omega : root < (((spine e).take stopDepth).map length).sum + length stopLayer.term)
  intro empty
  subst rest
  have suffixSize := drop_length index rootLayer.term
  rw [cut] at suffixSize
  simp only [length, Nat.add_zero] at suffixSize
  have finalIndex : index = length rootLayer.term - 1 := by omega
  by_cases earlier : rootDepth < stopDepth
  · have chosenInPrefix : ((spine e).take stopDepth)[rootDepth]? = some rootLayer.term := by
      rw [List.getElem?_take_of_lt earlier]
      exact rootLookup
    have member := ownerIndices_selected 0 ((spine e).take stopDepth) rootDepth chosenInPrefix
    simp only [List.take_take, Nat.min_eq_left (Nat.le_of_lt earlier), Nat.zero_add] at member
    have rootIsOwner : root ∈ ownerIndices 0 ((spine e).take stopDepth) := by
      have equal : root = (((spine e).take rootDepth).map length).sum + length rootLayer.term - 1 := by omega
      rw [equal]
      exact member
    apply safe.2
    rw [layerAt_owner_indices stopDepth e atStop]
    simpa only [List.length_nil, List.nil_append] using rootIsOwner
  · have depths : rootDepth = stopDepth := by omega
    have sameTerm : rootLayer.term = stopLayer.term := by
      rw [depths, stopLookup] at rootLookup
      exact Option.some.inj rootLookup.symm
    rw [depths] at offset
    rw [sameTerm] at finalIndex
    omega

end BTnSSBMS.Source
