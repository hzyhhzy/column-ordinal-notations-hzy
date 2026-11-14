import BTnSSBMS.SourceHighAssembly

/-!
Nonempty attachments have an actual highest key parent. Search cannot
fail along the numerical chain: a zero-valued column has an empty key
and is not an open owner. These are finite source properties, not
standard-domain or target-encoding assumptions.
-/
namespace BTnSSBMS.Source

def ZeroKeys (d : Nat) (context : KeyContext) : Prop :=
  ∀ (i : Nat) (a : ParentLabel) (key : Key),
    context[i]? = some (a, key) → a.coordinates[d - 1]?.getD 0 = 0 → key = .nil

def PositiveOwners (row : Nat) (context : ParentContext) (owners : List Nat) : Prop :=
  ∀ i ∈ owners, i < context.length ∧ 0 < Parents.reading context row i

theorem projected_key_lookup {d : Nat} {context : ParentContext} {keyContext : KeyContext}
    (projection : keyContext.map (fun entry => Parents.truncate d entry.1) = context)
    {i : Nat} {a : ParentLabel} {key : Key} (found : keyContext[i]? = some (a, key)) :
    context[i]? = some (Parents.truncate d a) := by
  rw [← projection, List.getElem?_map, found, Option.map_some]

theorem topSearch_nonempty_exists {d : Nat} (positive : 0 < d)
    {context : ParentContext} {keyContext : KeyContext} {owners : List Nat}
    (projection : keyContext.map (fun entry => Parents.truncate d entry.1) = context)
    (valid : Parents.ContextValid context) (unit : Parents.UnitSteps d context)
    (zeros : ZeroKeys d keyContext) (ownerPositive : PositiveOwners (d - 1) context owners)
    (key : Key) (nonempty : key ≠ .nil) (position : Nat) (inside : position < context.length) :
    ∃ root, topSearch d keyContext owners key (position + 1) = some root := by
  have size : keyContext.length = context.length := by
    have lengths := congrArg List.length projection
    simpa only [List.length_map] using lengths
  induction position using Nat.strongRecOn with
  | ind position ih =>
    have keyInside : position < keyContext.length := by omega
    obtain ⟨a, oldKey, lookup⟩ : ∃ a k, keyContext[position]? = some (a, k) :=
      ⟨keyContext[position].1, keyContext[position].2, List.getElem?_eq_getElem keyInside⟩
    have numericalLookup := projected_key_lookup projection lookup
    have value : Parents.reading context (d - 1) position = a.coordinates[d - 1]?.getD 0 := by
      simp only [Parents.reading, numericalLookup, Option.getD_some, Parents.truncate]
    by_cases hit : (!owners.contains position && Keys.compare oldKey key == .lt) = true
    · exact ⟨position, by rw [topSearch]; simp only [lookup, hit, if_true]⟩
    · have valuePositive : 0 < Parents.reading context (d - 1) position := by
        by_cases yes : 0 < Parents.reading context (d - 1) position
        · exact yes
        have zero : a.coordinates[d - 1]?.getD 0 = 0 := by omega
        have emptyKey := zeros position a oldKey lookup zero
        have unowned : owners.contains position = false := by
          apply Bool.eq_false_iff.mpr
          intro member
          have above := (ownerPositive position (by simpa only [List.contains_eq_mem, decide_eq_true_eq] using member)).2
          omega
        apply False.elim
        apply hit
        rw [unowned, emptyKey]
        cases key with
        | nil => exact False.elim (nonempty rfl)
        | cons h hs => rfl
      obtain ⟨parent, numericalEdge⟩ := unit.positive_has_parent (by omega : d - 1 < d) inside valuePositive
      have earlier := Parents.parent_earlier valid numericalEdge
      have stored : a.parents[d - 1]?.join = some parent := by
        simpa only [Parents.parent, numericalLookup, Option.bind_some, Parents.truncate,
          List.getElem?_take_of_lt (by omega : d - 1 < d)] using numericalEdge
      obtain ⟨root, found⟩ := ih parent earlier (by omega)
      exact ⟨root, by rw [topSearch]; simp only [lookup, hit, stored, earlier, if_true]; exact found⟩

theorem PositiveOwners.append_label {d row : Nat} {context : ParentContext} {owners : List Nat}
    (positive : PositiveOwners row context owners) (a : List Nat) :
    PositiveOwners row (context ++ [Parents.label d context a]) owners := by
  intro i member
  obtain ⟨inside, above⟩ := positive i member
  refine ⟨by simp only [List.length_append, List.length_cons, List.length_nil]; omega, ?_⟩
  rw [← Parents.reading_prefix (List.prefix_append ..) row i inside]
  exact above

theorem PositiveOwners.enter {d row : Nat} {context : ParentContext} {owners : List Nat}
    (positive : PositiveOwners row context owners) (a : List Nat) (above : 0 < a[row]?.getD 0) :
    PositiveOwners row (context ++ [Parents.label d context a]) (owners ++ [context.length]) := by
  intro i member
  rcases List.mem_append.mp member with old | atEnd
  · exact positive.append_label a i old
  · have same : i = context.length := by simpa only [List.mem_singleton] using atEnd
    subst i
    exact ⟨by simp, by rw [Parents.reading_append_label]; exact above⟩

theorem ZeroKeys.append {d : Nat} {context : KeyContext} (zeros : ZeroKeys d context)
    (a : ParentLabel) (key : Key) (atZero : a.coordinates[d - 1]?.getD 0 = 0 → key = .nil) :
    ZeroKeys d (context ++ [(a, key)]) := by
  intro i b k lookup zero
  by_cases old : i < context.length
  · rw [List.getElem?_append_left old] at lookup
    exact zeros i b k lookup zero
  · have inside := (List.getElem?_eq_some_iff.mp lookup).choose
    have same : i = context.length := by
      simp only [List.length_append, List.length_cons, List.length_nil] at inside
      omega
    subst i
    rw [List.getElem?_concat_length] at lookup
    have equal := Option.some.inj lookup
    cases equal
    exact atZero zero

mutual
  def AttachedTop (d : Nat) : ParentExpr → Prop
    | .nil => True
    | .cons a hs rest =>
      (hs ≠ .nil → ∃ root, a.parents[d]?.join = some root) ∧
      AttachedTopForests d hs ∧ AttachedTop d rest
  def AttachedTopForests (d : Nat) : Forests ParentLabel → Prop
    | .nil => True
    | .cons h hs => AttachedTop d h ∧ AttachedTopForests d hs
end

mutual
  theorem fillTop_annotate_attachedTop (d : Nat) (positive : 0 < d)
      (context : ParentContext) (keyContext : KeyContext) (owners : List Nat)
      (projection : keyContext.map (fun entry => Parents.truncate d entry.1) = context)
      (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
      (zeros : ZeroKeys d keyContext) (ownerPositive : PositiveOwners (d - 1) context owners)
      (e : NumericalExpr) (legal : FiniteLegal d context e) :
      AttachedTop d (fillTop d keyContext owners (Parents.annotate d context e)) := by
    cases e with
    | nil => trivial
    | cons a hs rest =>
      let numeric := Parents.label d context a
      let key := Keys.ofColumn d keyContext.length numeric (Parents.annotateForests d (context ++ [numeric]) hs)
      let top := topSearch d keyContext owners key ((numeric.parents[d - 1]?.join).map (· + 1) |>.getD 0)
      let extended : ParentLabel := {numeric with parents := numeric.parents ++ [top]}
      let next : KeyContext := keyContext ++ [(extended, key)]
      have size : keyContext.length = context.length := by
        simpa only [List.length_map] using congrArg List.length projection
      have nextProjection : next.map (fun entry => Parents.truncate d entry.1) = context ++ [numeric] := by
        simp only [next, List.map_append, List.map_cons, List.map_nil, projection]
        rw [show Parents.truncate d extended = numeric from Parents.truncate_extended_label d context a [top]]
      have nextCoherent := Parents.coherent_append_label coherent a
      have nextValid := Parents.context_valid_append_label d context valid a
      have nextZeros : ZeroKeys d next := by
        apply zeros.append extended key
        intro zero
        have noForests : hs = .nil := by
          by_cases empty : hs = .nil
          · exact empty
          have above := legal.2.2.1 empty (d - 1) (by omega)
          change a[d - 1]?.getD 0 = 0 at zero
          omega
        change Keys.ofColumn d keyContext.length numeric (Parents.annotateForests d (context ++ [numeric]) hs) = .nil
        rw [noForests]
        rfl
      change (∀ _ : fillTopForests d next (owners ++ [keyContext.length])
          (Parents.annotateForests d (context ++ [numeric]) hs) ≠ .nil,
          ∃ root, (numeric.parents ++ [top])[d]?.join = some root) ∧
        AttachedTopForests d (fillTopForests d next (owners ++ [keyContext.length])
          (Parents.annotateForests d (context ++ [numeric]) hs)) ∧
        AttachedTop d (fillTop d next owners (Parents.annotate d (context ++ [numeric]) rest))
      refine ⟨?_, ?_, fillTop_annotate_attachedTop d positive _ next owners nextProjection
        nextCoherent nextValid nextZeros (ownerPositive.append_label a) rest legal.2.2.2.2⟩
      · intro attached
        have nonempty : hs ≠ .nil := by intro empty; rw [empty] at attached; exact attached rfl
        have keyNonempty : key ≠ .nil := by
          dsimp only [key]
          cases hs with
          | nil => exact False.elim (nonempty rfl)
          | cons h tail => intro impossible; cases impossible
        have value : 0 < Parents.reading (context ++ [numeric]) (d - 1) context.length := by
          rw [Parents.reading_append_label]
          exact legal.2.2.1 nonempty (d - 1) (by omega)
        obtain ⟨parent, input⟩ := legal.2.1.positive_has_parent (by omega : d - 1 < d) (by simp) value
        rw [Parents.append_label_parent] at input
        have parentInside := Parents.label_parent_bound d context a (d - 1) parent input
        have priorUnit := legal.2.1.restrict nextValid (List.prefix_append ..)
        obtain ⟨root, search⟩ := topSearch_nonempty_exists positive projection valid priorUnit zeros ownerPositive
          key keyNonempty parent parentInside
        have topFound : top = some root := by
          change topSearch d keyContext owners key
            ((numeric.parents[d - 1]?.join).map (· + 1) |>.getD 0) = some root
          rw [input, Option.map_some, Option.getD_some]
          exact search
        have lookup : (numeric.parents ++ [top])[d]? = some top := by
          simpa only [show numeric.parents.length = d from Parents.label_width d context a] using
            (List.getElem?_concat_length : (numeric.parents ++ [top])[numeric.parents.length]? = some top)
        exact ⟨root, by rw [lookup, Option.join_some, topFound]⟩
      · cases hs with
        | nil => trivial
        | cons h tail =>
          have ownerAbove := legal.2.2.1 (by intro impossible; cases impossible) (d - 1) (by omega)
          rw [size]
          exact fillTopForests_annotate_attachedTop d positive _ next (owners ++ [context.length])
            nextProjection nextCoherent nextValid nextZeros (ownerPositive.enter a ownerAbove)
            (.cons h tail) (a[0]?.getD 0) legal.2.2.2.1
  theorem fillTopForests_annotate_attachedTop (d : Nat) (positive : 0 < d)
      (context : ParentContext) (keyContext : KeyContext) (owners : List Nat)
      (projection : keyContext.map (fun entry => Parents.truncate d entry.1) = context)
      (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
      (zeros : ZeroKeys d keyContext) (ownerPositive : PositiveOwners (d - 1) context owners)
      (hs : Forests (List Nat)) (owner : Nat) (legal : FiniteLegalForests d context owner hs) :
      AttachedTopForests d (fillTopForests d keyContext owners (Parents.annotateForests d context hs)) := by
    cases hs with
    | nil => trivial
    | cons h rest => exact ⟨fillTop_annotate_attachedTop d positive context keyContext owners projection
        coherent valid zeros ownerPositive h legal.2.1,
      fillTopForests_annotate_attachedTop d positive context keyContext owners projection
        coherent valid zeros ownerPositive rest owner legal.2.2⟩
end

theorem parents_attachedTop {d : Nat} (positive : 0 < d) (e : NumericalExpr)
    (legal : FiniteLegal d [] e) : AttachedTop d (parents d e) :=
  fillTop_annotate_attachedTop d positive [] [] [] rfl (Parents.empty_coherent d)
    Parents.empty_context_valid (by intro i a k impossible; simp at impossible)
    (by intro i impossible; simp at impossible) e legal

end BTnSSBMS.Source
