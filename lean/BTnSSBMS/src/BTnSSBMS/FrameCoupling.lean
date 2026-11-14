import BTnSSBMS.QueryCopyTransport

/-!
Couple two real binding lists by the key and height fields which the
encoder actually reads. Definition/latest pointers may differ. This
relation will be maintained through the real encoder, rather than
assuming its transformed state is obtained by mapping whole bindings.
-/
namespace BTnSSBMS.Encoder

def KeyBindingRel (keyOf : Binding → Key) (old new : Binding) : Prop :=
  new.key = keyOf old ∧ new.height = old.height

inductive KeyFrameRel (keyOf : Binding → Key) : List Binding → List Binding → Prop
  | nil : KeyFrameRel keyOf [] []
  | cons {old new : Binding} {left right : List Binding}
      (head : KeyBindingRel keyOf old new) (tail : KeyFrameRel keyOf left right) :
      KeyFrameRel keyOf (old :: left) (new :: right)

theorem KeyFrameRel.append {keyOf : Binding → Key} {a b c e : List Binding}
    (left : KeyFrameRel keyOf a b) (right : KeyFrameRel keyOf c e) :
    KeyFrameRel keyOf (a ++ c) (b ++ e) := by
  induction left with
  | nil => exact right
  | cons pair tail ih => exact .cons pair ih

theorem KeyFrameRel.congr {keyOf newKeyOf : Binding → Key} {left right : List Binding}
    (related : KeyFrameRel keyOf left right)
    (same : ∀ b ∈ left, newKeyOf b = keyOf b) : KeyFrameRel newKeyOf left right := by
  induction related with
  | nil => exact .nil
  | @cons a b left right pair tail ih =>
    refine .cons ⟨?_, pair.2⟩ (ih (fun x member => same x (by simp only [List.mem_cons]; exact Or.inr member)))
    rw [same a (by simp)]
    exact pair.1

theorem KeyFrameRel.heights {keyOf : Binding → Key} {left right : List Binding}
    (related : KeyFrameRel keyOf left right) : right.map Binding.height = left.map Binding.height := by
  induction related with
  | nil => rfl
  | cons pair tail ih => simp only [List.map_cons, pair.2, ih]

private theorem base_height_as_list (frame : List Binding) :
    (base frame).height = (frame.map Binding.height).getLast?.getD 0 := by
  simp only [base, List.getLast?_map]
  cases frame.getLast? <;> rfl

theorem KeyFrameRel.base_height {keyOf : Binding → Key} {left right : List Binding}
    (related : KeyFrameRel keyOf left right) : (base right).height = (base left).height := by
  rw [base_height_as_list, base_height_as_list, related.heights]

theorem KeyFrameRel.virtual {keyOf : Binding → Key} (empty : keyOf zeroBinding = .nil) :
    KeyFrameRel keyOf virtualFrame virtualFrame :=
  .cons ⟨empty.symm, rfl⟩ .nil

theorem KeyFrameRel.smaller {keyOf : Binding → Key} {left right : List Binding}
    (related : KeyFrameRel keyOf left right) (oldKey newKey : Key)
    (comparisons : ∀ b ∈ left, Keys.compare (keyOf b) newKey = Keys.compare b.key oldKey) :
    KeyFrameRel keyOf (smaller left oldKey) (smaller right newKey) := by
  induction related with
  | nil => exact .nil
  | @cons a b left right pair tail ih =>
    have head : Keys.compare b.key newKey = Keys.compare a.key oldKey :=
      pair.1 ▸ comparisons a (by simp)
    have rest := ih (fun x member => comparisons x (by simp only [List.mem_cons]; exact Or.inr member))
    simp only [Encoder.smaller, List.filter_cons, head]
    split
    · exact .cons pair rest
    · exact rest

/-- The actual find operation either misses in both frames or returns
bindings at the paired position, with the same height. -/
theorem KeyFrameRel.equal_cases {keyOf : Binding → Key} {left right : List Binding}
    (related : KeyFrameRel keyOf left right) (oldKey newKey : Key)
    (comparisons : ∀ b ∈ left, Keys.compare (keyOf b) newKey = Keys.compare b.key oldKey) :
    match equal left oldKey with
    | none => equal right newKey = none
    | some old => ∃ new, equal right newKey = some new ∧ KeyBindingRel keyOf old new := by
  induction related with
  | nil => rfl
  | @cons a b left right pair tail ih =>
    have head : Keys.compare b.key newKey = Keys.compare a.key oldKey :=
      pair.1 ▸ comparisons a (by simp)
    have rest := ih (fun x member => comparisons x (by simp only [List.mem_cons]; exact Or.inr member))
    cases hit : Keys.compare a.key oldKey == .eq with
    | true =>
      simp only [equal, List.find?_cons, head, hit]
      exact ⟨b, rfl, pair⟩
    | false => simpa only [equal, List.find?_cons, head, hit] using rest

theorem KeyFrameRel.equal_none {keyOf : Binding → Key} {left right : List Binding}
    (related : KeyFrameRel keyOf left right) (oldKey newKey : Key)
    (comparisons : ∀ b ∈ left, Keys.compare (keyOf b) newKey = Keys.compare b.key oldKey)
    (fresh : equal left oldKey = none) : equal right newKey = none := by
  simpa only [fresh] using related.equal_cases oldKey newKey comparisons

theorem KeyFrameRel.equal_some {keyOf : Binding → Key} {left right : List Binding}
    (related : KeyFrameRel keyOf left right) (oldKey newKey : Key)
    (comparisons : ∀ b ∈ left, Keys.compare (keyOf b) newKey = Keys.compare b.key oldKey)
    (old : Binding) (found : equal left oldKey = some old) :
    ∃ new, equal right newKey = some new ∧ KeyBindingRel keyOf old new := by
  simpa only [found] using related.equal_cases oldKey newKey comparisons

theorem KeyFrameRel.firstHeight {keyOf : Binding → Key} {left right : List Binding}
    (related : KeyFrameRel keyOf left right) (oldKey newKey : Key)
    (comparisons : ∀ b ∈ left, Keys.compare (keyOf b) newKey = Keys.compare b.key oldKey) :
    firstHeight right newKey = firstHeight left oldKey := by
  cases found : equal left oldKey with
  | none =>
    rw [Encoder.firstHeight, related.equal_none oldKey newKey comparisons found, Encoder.firstHeight, found]
    exact congrArg (· + 1) (related.smaller oldKey newKey comparisons).base_height
  | some old =>
    obtain ⟨new, newFound, pair⟩ := related.equal_some oldKey newKey comparisons old found
    rw [Encoder.firstHeight, newFound, Encoder.firstHeight, found]
    exact pair.2

/-- Instantiate the finite list lemma with the proved comparison of
actual queried source materials, not a supplied comparison premise. -/
theorem MaterialQuery.coupled_tests {d : Nat} {source target : ParentContext}
    {coordinates visible owners moved : List Nat} {materials : List (Forests (List Nat))}
    {state : State d} {hs : Forests (List Nat)} {newFrame : List Binding}
    (query : MaterialQuery d source coordinates visible owners materials state hs)
    (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
    (targetUnit : Parents.UnitSteps d target)
    (view : Parents.NumericalView d (source ++ [Parents.label d source coordinates]) target moved)
    (targetWidth : ∀ i, i < target.length → (target[i]?.getD default).coordinates.length = d)
    (positive : 0 < d)
    (related : KeyFrameRel
      (fun b => (rekeyBinding d (source ++ [Parents.label d source coordinates]) target visible moved materials b).key)
      (frameAt state (representative visible (Parents.label d source coordinates) (d - 1))) newFrame) :
    let frame := frameAt state (representative visible (Parents.label d source coordinates) (d - 1))
    let oldKey := queryKey d source coordinates hs
    let newKey := movedQueryKey d source target coordinates moved hs
    let keyOf := fun b => (rekeyBinding d (source ++ [Parents.label d source coordinates]) target visible moved materials b).key
    KeyFrameRel keyOf (smaller frame oldKey) (smaller newFrame newKey) ∧
      firstHeight newFrame newKey = firstHeight frame oldKey ∧
      (match equal frame oldKey with
      | none => equal newFrame newKey = none
      | some old => ∃ new, equal newFrame newKey = some new ∧ KeyBindingRel keyOf old new) := by
  have comparisons := rekey_queried_binding_compare query.inherited query.view query.coherent query.valid
    query.unit targetCoherent targetValid targetUnit view targetWidth positive query.width hs query.legal
  exact ⟨related.smaller _ _ comparisons, related.firstHeight _ _ comparisons, related.equal_cases _ _ comparisons⟩

end BTnSSBMS.Encoder
