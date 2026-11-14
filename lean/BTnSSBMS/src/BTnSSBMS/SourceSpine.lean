import BTnSSBMS.SourceRootSearch

/-!
The actual right-spine extraction, with its numerical context and owner
indices. Closed forests are not added to a later outer context. These
computations only describe the frozen spine and drop operations.
-/
namespace BTnSSBMS.Source

def outerContext (d : Nat) (context : ParentContext) : NumericalExpr → ParentContext
  | .nil => context
  | .cons a _ rest => outerContext d (context ++ [Parents.label d context a]) rest

theorem outerContext_length (d : Nat) (context : ParentContext) (e : NumericalExpr) :
    (outerContext d context e).length = context.length + length e := by
  cases e with
  | nil => simp [outerContext, length]
  | cons a hs rest =>
    rw [outerContext, outerContext_length d _ rest]
    simp only [List.length_append, List.length_cons, List.length_nil, length]
    omega

theorem outerContext_coordinates (d : Nat) (context : ParentContext) (e : NumericalExpr) :
    (outerContext d context e).map ParentLabel.coordinates = context.map ParentLabel.coordinates ++ labels e := by
  cases e with
  | nil => simp [outerContext, labels]
  | cons a hs rest =>
    rw [outerContext, outerContext_coordinates d _ rest]
    simp [List.map_append, Parents.label, labels, List.append_assoc]

theorem outerContext_coherent {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (e : NumericalExpr) :
    Parents.Coherent d (outerContext d context e) := by
  cases e with
  | nil => exact coherent
  | cons a hs rest => exact outerContext_coherent (Parents.coherent_append_label coherent a) rest

theorem outerContext_valid {d : Nat} {context : ParentContext}
    (valid : Parents.ContextValid context) (e : NumericalExpr) :
    Parents.ContextValid (outerContext d context e) := by
  cases e with
  | nil => exact valid
  | cons a hs rest => exact outerContext_valid (Parents.context_valid_append_label d context valid a) rest

theorem outerContext_last {d : Nat} (context : ParentContext) (e : NumericalExpr)
    {a : List Nat} {hs : Forests (List Nat)} (found : last? e = some (a, hs)) :
    outerContext d context e =
      outerContext d context (dropLast e) ++ [Parents.label d (outerContext d context (dropLast e)) a] := by
  cases e with
  | nil => simp [last?] at found
  | cons b ks rest =>
    cases rest with
    | nil =>
      have same : (b, ks) = (a, hs) := by simpa only [last?, Option.some.injEq] using found
      cases same
      simp only [outerContext, dropLast]
    | cons c js tail =>
      simpa only [outerContext, dropLast] using
        outerContext_last (context ++ [Parents.label d context b]) (.cons c js tail)
          (by simpa only [last?] using found)

theorem FiniteLegal.last_context {d : Nat} {context : ParentContext} {e : NumericalExpr}
    (legal : FiniteLegal d context e) {a : List Nat} {hs : Forests (List Nat)}
    (found : last? e = some (a, hs)) :
    FiniteLegal d (outerContext d context (Source.dropLast e)) (.cons a hs .nil) := by
  cases e with
  | nil => simp [last?] at found
  | cons b ks rest =>
    cases rest with
    | nil =>
      have same : (b, ks) = (a, hs) := by simpa only [last?, Option.some.injEq] using found
      cases same
      simpa only [Source.dropLast, outerContext] using legal
    | cons c js tail =>
      simpa only [Source.dropLast, outerContext] using
        legal.2.2.2.2.last_context (by simpa only [last?] using found)

structure SpineLayer where
  context : ParentContext
  owner : Option Nat
  owners : List Nat
  term : NumericalExpr

def layerAt (d : Nat) (context : ParentContext) (owner : Option Nat) (owners : List Nat) :
    Nat → NumericalExpr → Option SpineLayer
  | 0, e => some ⟨context, owner, owners, e⟩
  | depth + 1, e => (last? e).bind fun c => (lastForest? c.2).bind fun h =>
      let before := outerContext d context (dropLast e)
      layerAt d (before ++ [Parents.label d before c.1]) (some (c.1[0]?.getD 0))
        (owners ++ [before.length]) depth h

theorem layerAt_term (d : Nat) (context : ParentContext) (owner : Option Nat) (owners : List Nat)
    (depth : Nat) (e : NumericalExpr) :
    (layerAt d context owner owners depth e).map SpineLayer.term = (spine e)[depth]? := by
  induction depth generalizing context owner owners e with
  | zero => rfl
  | succ depth ih =>
    rw [spine_get_succ]
    simp only [layerAt, lastChild?]
    cases last : last? e with
    | none => rfl
    | some entry =>
      obtain ⟨a, hs⟩ := entry
      simp only [Option.bind_some]
      cases child : lastForest? hs with
      | none => rfl
      | some h =>
        simp only [Option.bind_some]
        exact ih _ _ _ h

theorem layerAt_exists {d : Nat} (context : ParentContext) (owner : Option Nat) (owners : List Nat)
    {depth : Nat} {e part : NumericalExpr} (selected : (spine e)[depth]? = some part) :
    ∃ layer, layerAt d context owner owners depth e = some layer ∧ layer.term = part := by
  have found := layerAt_term d context owner owners depth e
  rw [selected] at found
  cases result : layerAt d context owner owners depth e with
  | none => simp [result] at found
  | some layer =>
    exact ⟨layer, rfl, by simpa only [result, Option.map_some, Option.some.injEq] using found⟩

theorem layerAt_legal {d : Nat} {context : ParentContext} {owner : Option Nat} {owners : List Nat}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    (depth : Nat) (e : NumericalExpr) (legal : FiniteLegal d context e) (fence : FitsOwner owner e)
    {layer : SpineLayer} (found : layerAt d context owner owners depth e = some layer) :
    Parents.Coherent d layer.context ∧ Parents.ContextValid layer.context ∧
      FiniteLegal d layer.context layer.term ∧ FitsOwner layer.owner layer.term := by
  induction depth generalizing context owner owners e layer with
  | zero =>
    have same : layer = ⟨context, owner, owners, e⟩ := by
      simpa only [layerAt, Option.some.injEq] using found.symm
    subst layer
    exact ⟨coherent, valid, legal, fence⟩
  | succ depth ih =>
    simp only [layerAt, Option.bind_eq_some_iff] at found
    obtain ⟨⟨a, hs⟩, last, h, child, next⟩ := found
    have atLast := legal.last_context last
    have inside := atLast.2.2.2.1.last child
    exact ih (Parents.coherent_append_label (outerContext_coherent coherent (dropLast e)) a)
      (Parents.context_valid_append_label d _ (outerContext_valid valid (dropLast e)) a)
      h inside.2 (by intro bound equal; cases equal; exact inside.1) next

theorem layerAt_owners_prefix {d : Nat} {context : ParentContext} {owner : Option Nat} {owners : List Nat}
    (depth : Nat) (e : NumericalExpr) {layer : SpineLayer}
    (found : layerAt d context owner owners depth e = some layer) : owners <+: layer.owners := by
  induction depth generalizing context owner owners e layer with
  | zero =>
    have same : layer = ⟨context, owner, owners, e⟩ := by
      simpa only [layerAt, Option.some.injEq] using found.symm
    subst layer
    exact List.prefix_refl _
  | succ depth ih =>
    simp only [layerAt, Option.bind_eq_some_iff] at found
    obtain ⟨⟨a, hs⟩, _, h, _, next⟩ := found
    exact (List.prefix_append ..).trans (ih h next)

theorem spine_eq_child {e h : Expr α} (child : lastChild? e = some h) :
    spine e = e :: spine h := by
  simp only [spine, innerSpine_last, child, Option.map_some, Option.getD_some]

theorem layerAt_context_coordinates {d : Nat} {context : ParentContext} {owner : Option Nat}
    {owners : List Nat} (depth : Nat) (e : NumericalExpr) {layer : SpineLayer}
    (found : layerAt d context owner owners depth e = some layer) :
    layer.context.map ParentLabel.coordinates =
      context.map ParentLabel.coordinates ++ ((spine e).take depth).flatMap labels := by
  induction depth generalizing context owner owners e layer with
  | zero =>
    have same : layer = ⟨context, owner, owners, e⟩ := by
      simpa only [layerAt, Option.some.injEq] using found.symm
    subst layer
    simp
  | succ depth ih =>
    simp only [layerAt, Option.bind_eq_some_iff] at found
    obtain ⟨⟨a, hs⟩, last, h, child, next⟩ := found
    have full := outerContext_last (d := d) context e last
    have below := ih h next
    rw [← full, outerContext_coordinates] at below
    rw [spine_eq_child (by simp [lastChild?, last, child] : lastChild? e = some h)]
    simpa only [List.take_succ_cons, List.flatMap_cons, List.append_assoc] using below

def dropContext (d : Nat) (context : ParentContext) : Nat → NumericalExpr → ParentContext
  | 0, _ => context
  | _, .nil => context
  | index + 1, .cons a _ rest => dropContext d (context ++ [Parents.label d context a]) index rest

theorem dropContext_length (d : Nat) (context : ParentContext) (index : Nat) (e : NumericalExpr)
    (inside : index < length e) : (dropContext d context index e).length = context.length + index := by
  induction index generalizing context e with
  | zero => simp [dropContext]
  | succ index ih =>
    cases e with
    | nil => simp [length] at inside
    | cons a hs rest =>
      rw [dropContext, ih _ rest (by simp only [length] at inside; omega)]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

theorem drop_contexts {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    (index : Nat) (e : NumericalExpr) (legal : FiniteLegal d context e) :
    Parents.Coherent d (dropContext d context index e) ∧
      Parents.ContextValid (dropContext d context index e) ∧
      FiniteLegal d (dropContext d context index e) (drop index e) := by
  induction index generalizing context e with
  | zero => exact ⟨coherent, valid, legal⟩
  | succ index ih =>
    cases e with
    | nil => exact ⟨coherent, valid, trivial⟩
    | cons a hs rest =>
      exact ih (Parents.coherent_append_label coherent a)
        (Parents.context_valid_append_label d context valid a) rest legal.2.2.2.2

theorem drop_nonempty (index : Nat) (e : Expr α) (inside : index < length e) : drop index e ≠ .nil := by
  induction index generalizing e with
  | zero => cases e <;> simp_all [drop, length]
  | succ index ih =>
    cases e with
    | nil => simp [length] at inside
    | cons a hs rest => exact ih rest (by simp only [length] at inside; omega)

theorem labels_length (e : Expr α) : (labels e).length = length e := by
  cases e with
  | nil => rfl
  | cons a hs rest =>
    simp only [labels, length, List.length_cons, labels_length rest]
    omega

theorem layerAt_context_length {d : Nat} {context : ParentContext} {owner : Option Nat}
    {owners : List Nat} (depth : Nat) (e : NumericalExpr) {layer : SpineLayer}
    (found : layerAt d context owner owners depth e = some layer) :
    layer.context.length = context.length + (((spine e).take depth).map length).sum := by
  have equality := congrArg List.length (layerAt_context_coordinates depth e found)
  simpa only [List.length_map, List.length_append, List.length_flatMap, labels_length] using equality

theorem locateRoot_sound (sp : List (Expr α)) (root depth index : Nat)
    (found : locateRoot sp root = some (depth, index)) :
    ∃ part, sp[depth]? = some part ∧ index < length part ∧
      root = ((sp.take depth).map length).sum + index := by
  induction sp generalizing root depth index with
  | nil => simp [locateRoot] at found
  | cons first rest ih =>
    rw [locateRoot] at found
    by_cases inside : root < length first
    · simp only [inside, if_true, Option.some.injEq] at found
      have atDepth := congrArg Prod.fst found
      have atIndex := congrArg Prod.snd found
      dsimp only at atDepth atIndex
      subst depth
      subst index
      exact ⟨first, rfl, inside, by simp⟩
    · simp only [inside, if_false, Option.map_eq_some_iff] at found
      obtain ⟨⟨below, position⟩, child, equal⟩ := found
      have atDepth := congrArg Prod.fst equal
      have atIndex := congrArg Prod.snd equal
      dsimp only at atDepth atIndex
      subst depth
      subst index
      obtain ⟨part, selected, room, offset⟩ := ih (root - length first) below position child
      refine ⟨part, by simpa only [List.getElem?_cons_succ] using selected, room, ?_⟩
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
      omega

/-- The literal locateRoot / spine / drop selection yields a nonempty
finite-legal template. Its actual entering-context length is exactly
the selected absolute root index; this is not an assumed transport view. -/
theorem extracted_root_finiteLegal {d : Nat} {e : NumericalExpr}
    (legal : FiniteLegal d [] e) {root depth index : Nat}
    (found : locateRoot (spine e) root = some (depth, index)) :
    ∃ layer a hs rest,
      layerAt d [] none [] depth e = some layer ∧
      (spine e)[depth]? = some layer.term ∧
      drop index layer.term = .cons a hs rest ∧
      (dropContext d layer.context index layer.term).length = root ∧
      Parents.Coherent d (dropContext d layer.context index layer.term) ∧
      Parents.ContextValid (dropContext d layer.context index layer.term) ∧
      FiniteLegal d (dropContext d layer.context index layer.term) (.cons a hs rest) := by
  obtain ⟨part, selected, inside, offset⟩ := locateRoot_sound (spine e) root depth index found
  obtain ⟨layer, atLayer, same⟩ := layerAt_exists (d := d) [] none [] selected
  obtain ⟨coherent, valid, piece, _⟩ := layerAt_legal (d := d)
    (by simp [Parents.Coherent]) (by simp [Parents.ContextValid]) depth e legal
    (by intro bound impossible; cases impossible) atLayer
  have room : index < length layer.term := by rw [same]; exact inside
  have states := drop_contexts coherent valid index layer.term piece
  have size := dropContext_length d layer.context index layer.term room
  rw [layerAt_context_length depth e atLayer] at size
  simp only [List.length_nil, Nat.zero_add] at size
  have nonempty := drop_nonempty index layer.term room
  cases cut : drop index layer.term with
  | nil => exact False.elim (nonempty cut)
  | cons a hs rest =>
    refine ⟨layer, a, hs, rest, atLayer, ?_, cut, ?_, states.1, states.2.1, ?_⟩
    · rw [same]; exact selected
    · omega
    · simpa only [cut] using states.2.2

end BTnSSBMS.Source
