import BTnSSBMS.RelocationOrder

/-! Finite legality and owner fences for canonical numerical transport.
These statements do not assert standardness or any block-order invariant. -/
namespace BTnSSBMS.Source

theorem relocationHead_unitSteps {d : Nat} {source target : ParentContext} {visible : List Nat}
    (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
    (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
    (targetUnit : Parents.UnitSteps d target)
    (view : Parents.NumericalView d source target visible) (a : List Nat) :
    Parents.UnitSteps d (target ++ [Parents.label d target (relocationHead d source target visible a)]) := by
  apply targetUnit.extend_one (Parents.context_valid_append_label d target targetValid _) (List.prefix_append _ _)
    (by simp)
  intro j room
  rw [Parents.reading_append_label, Parents.append_label_parent,
    relocationHead_parents sourceCoherent sourceValid targetCoherent targetValid view a j room,
    relocationHead_value d source target visible a room]
  cases found : (Parents.label d source a).parents[j]?.join with
  | none => simp only [Parents.representedValue, found, Option.map_none, Option.getD_none]
  | some p =>
    have bound := Parents.label_parent_bound d source a j p found
    simp only [Parents.representedValue, found, Option.map_some, Option.getD_some]
    exact congrArg (· + 1) (Parents.reading_prefix (List.prefix_append _ _) j (Parents.point visible p)
      (view.bounded p bound))

theorem relocationHead_positive {d : Nat} {source target : ParentContext} {visible : List Nat}
    (a : List Nat) (unit : Parents.UnitSteps d (source ++ [Parents.label d source a]))
    {j : Nat} (room : j < d) (positive : 0 < a[j]?.getD 0) :
    0 < (relocationHead d source target visible a)[j]?.getD 0 := by
  have value := Parents.label_unit_value a unit room
  rw [relocationHead_value d source target visible a room]
  cases found : (Parents.label d source a).parents[j]?.join with
  | none => simp only [found, Option.map_none, Option.getD_none] at value; omega
  | some p => simp only [Parents.representedValue, found, Option.map_some, Option.getD_some]; omega

theorem relocationHead_above {d : Nat} {source target : ParentContext} {visible : List Nat}
    (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
    (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
    (view : Parents.NumericalView d source target visible) (positive : 0 < d)
    {owner : Nat} (inside : owner < source.length)
    (fence : Parents.Ancestor source 0 owner (source.length - 1)) (a : List Nat)
    (above : Parents.reading source 0 owner < a[0]?.getD 0) :
    Parents.reading target 0 (Parents.point visible owner) <
      (relocationHead d source target visible a)[0]?.getD 0 := by
  have next := relocation_view_append sourceCoherent sourceValid targetCoherent targetValid view a
  have path := Parents.append_above_fence sourceCoherent sourceValid positive inside fence a above
  have lifted := next.lift 0 positive owner source.length (by simp; omega) (by simp) path
  rw [Parents.point_append_old visible owner target.length (by rw [view.length]; exact inside),
    ← view.length, Parents.point_append_last] at lifted
  have strict := lifted.reading_lt (Parents.coherent_append_label targetCoherent _)
    (by have bound := view.bounded owner inside; omega)
  rw [Parents.reading_append_label,
    ← Parents.reading_prefix (List.prefix_append target _) 0 (Parents.point visible owner) (view.bounded owner inside)] at strict
  exact strict

theorem relocate_above (d : Nat) (e : NumericalExpr) (source target : ParentContext) (visible : List Nat)
    (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
    (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
    (view : Parents.NumericalView d source target visible) (positive : 0 < d)
    (owner : Nat) (inside : owner < source.length)
    (fence : Parents.Ancestor source 0 owner (source.length - 1))
    (above : ∀ a ∈ labels e, Parents.reading source 0 owner < a[0]?.getD 0) :
    ∀ a ∈ labels (relocate d source target visible e),
      Parents.reading target 0 (Parents.point visible owner) < a[0]?.getD 0 := by
  cases e with
  | nil => simp only [relocate, labels, List.not_mem_nil, false_implies, implies_true]
  | cons a hs tail =>
    intro col member
    simp only [relocate, labels, List.mem_cons] at member
    rcases member with rfl | later
    · exact relocationHead_above sourceCoherent sourceValid targetCoherent targetValid view positive inside fence a
        (above a (by simp [labels]))
    · have next := relocation_view_append sourceCoherent sourceValid targetCoherent targetValid view a
      have nextFence := Parents.append_above_fence sourceCoherent sourceValid positive inside fence a
        (above a (by simp [labels]))
      have nextAbove : ∀ col ∈ labels tail,
          Parents.reading (source ++ [Parents.label d source a]) 0 owner < col[0]?.getD 0 := by
        intro col member
        rw [← Parents.reading_prefix (List.prefix_append source _) 0 owner inside]
        exact above col (by simp only [labels, List.mem_cons]; exact Or.inr member)
      have result := relocate_above d tail (source ++ [Parents.label d source a])
        (target ++ [Parents.label d target (relocationHead d source target visible a)]) (visible ++ [target.length])
        (Parents.coherent_append_label sourceCoherent a) (Parents.context_valid_append_label d source sourceValid a)
        (Parents.coherent_append_label targetCoherent _) (Parents.context_valid_append_label d target targetValid _)
        next positive owner (by simp; omega) (by simpa using nextFence) nextAbove col later
      rw [Parents.point_append_old visible owner target.length (by rw [view.length]; exact inside),
        ← Parents.reading_prefix (List.prefix_append target _) 0 (Parents.point visible owner) (view.bounded owner inside)] at result
      exact result

mutual
  theorem relocate_finiteLegal (d : Nat) (e : NumericalExpr) (source target : ParentContext) (visible : List Nat)
      (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
      (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
      (targetUnit : Parents.UnitSteps d target) (view : Parents.NumericalView d source target visible)
      (positive : 0 < d) (legal : FiniteLegal d source e) :
      FiniteLegal d target (relocate d source target visible e) := by
    cases e with
    | nil => trivial
    | cons a hs tail =>
      have next := relocation_view_append sourceCoherent sourceValid targetCoherent targetValid view a
      have nextUnit := relocationHead_unitSteps sourceCoherent sourceValid targetCoherent targetValid targetUnit view a
      have nextSource := Parents.coherent_append_label sourceCoherent a
      have nextSourceValid := Parents.context_valid_append_label d source sourceValid a
      have nextTarget := Parents.coherent_append_label targetCoherent (relocationHead d source target visible a)
      have nextTargetValid := Parents.context_valid_append_label d target targetValid (relocationHead d source target visible a)
      refine ⟨relocationHead_width d source target visible a, nextUnit, ?_, ?_,
        relocate_finiteLegal d tail _ _ _ nextSource nextSourceValid nextTarget nextTargetValid nextUnit next positive legal.2.2.2.2⟩
      · intro attached j room
        have nonempty : hs ≠ .nil := by intro empty; subst hs; exact attached rfl
        exact relocationHead_positive a legal.2.1 room (legal.2.2.1 nonempty j room)
      · have forests := relocateForests_finiteLegal d hs _ _ _ nextSource nextSourceValid nextTarget nextTargetValid
          nextUnit next positive source.length (by simp)
          (by simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_sub_cancel]; exact .refl _)
          (by rw [Parents.reading_append_label]; exact legal.2.2.2.1)
        rw [← view.length, Parents.point_append_last, Parents.reading_append_label] at forests
        exact forests

  theorem relocateForests_finiteLegal (d : Nat) (hs : Forests (List Nat))
      (source target : ParentContext) (visible : List Nat)
      (sourceCoherent : Parents.Coherent d source) (sourceValid : Parents.ContextValid source)
      (targetCoherent : Parents.Coherent d target) (targetValid : Parents.ContextValid target)
      (targetUnit : Parents.UnitSteps d target) (view : Parents.NumericalView d source target visible)
      (positive : 0 < d) (owner : Nat) (inside : owner < source.length)
      (fence : Parents.Ancestor source 0 owner (source.length - 1))
      (legal : FiniteLegalForests d source (Parents.reading source 0 owner) hs) :
      FiniteLegalForests d target (Parents.reading target 0 (Parents.point visible owner))
        (relocateForests d source target visible hs) := by
    cases hs with
    | nil => trivial
    | cons h hs =>
      exact ⟨relocate_above d h source target visible sourceCoherent sourceValid targetCoherent targetValid view
          positive owner inside fence legal.1,
        relocate_finiteLegal d h source target visible sourceCoherent sourceValid targetCoherent targetValid targetUnit view
          positive legal.2.1,
        relocateForests_finiteLegal d hs source target visible sourceCoherent sourceValid targetCoherent targetValid targetUnit view
          positive owner inside fence legal.2.2⟩
end

end BTnSSBMS.Source
