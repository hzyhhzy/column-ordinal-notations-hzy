import BTnSSBMS.SourceFS

/-!
Preservation of the prescribed zero leaf at the start of a standard source.
This is proved from the actual FS, including both forest and copy branches.
It does not assume the much stronger source block invariants.
-/
namespace BTnSSBMS.Source

def LeadingZero (d : Nat) (e : NumericalExpr) : Prop :=
  e = .nil ∨ ∃ t, e = .cons (List.replicate d 0) .nil t

theorem shift_zero (a delta : List Nat) (threshold : Nat) :
    shift a threshold delta 0 = a := by
  simp [shift]
  rw [List.mapIdx_eq_iff]
  intro i
  simp

theorem special_preserves_head (index depth : Nat) (a : List Nat)
    (hs : Forests (List Nat)) (b : List Nat) (ks : Forests (List Nat))
    (rest : NumericalExpr) :
    special index depth (.cons a hs (.cons b ks rest)) =
      .cons a hs (special index depth (.cons b ks rest)) := by
  cases depth <;> simp only [special, modifyLast]

theorem copied_head (d b root : Nat) (a c : List Nat)
    (hs : Forests (List Nat)) (rest tail : NumericalExpr)
    (hole : Option Nat) (delta : List Nat) :
    ∃ next, ascendReplace
      (mark b root [] (parents d (.cons a .nil (.cons c hs rest)))) tail hole delta 0 =
      .cons a .nil next := by
  simp only [parents, Parents.annotate, Parents.annotateForests, fillTop, fillTopForests,
    mark, Forests.map, markForests, ascendReplace, ascendForests, shift_zero,
    Bool.false_and, Bool.false_eq_true, if_false, ite_self]
  change ∃ next, Expr.cons a .nil _ = .cons a .nil next
  exact ⟨_, rfl⟩

theorem expand_leading_zero (d index : Nat) (e f : NumericalExpr)
    (head : LeadingZero d e) (step : expand? d e index = some f) :
    LeadingZero d f := by
  rcases head with rfl | ⟨t, rfl⟩
  · have same : f = .nil := by simpa [expand_empty] using step.symm
    exact Or.inl same
  · cases t with
    | nil =>
      have same : f = .nil := by
        simpa [expand?, last?, zeroColumn, dropLast] using step.symm
      exact Or.inl same
    | cons c hs rest =>
      simp only [expand?, last?] at step
      split at step
      · simp only [Option.pure_def, Option.some.injEq] at step
        exact Or.inl step.symm
      next last hl =>
        split at step
        · simp only [dropLast, Option.pure_def, Option.some.injEq] at step
          exact Or.inr ⟨_, step.symm⟩
        next nz =>
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at step
          obtain ⟨stop, _, step⟩ := step
          obtain ⟨stopColumn, _, step⟩ := step
          split at step
          · simp only [Option.pure_def, special_preserves_head, Option.some.injEq] at step
            exact Or.inr ⟨_, step.symm⟩
          next ns =>
            simp only [Option.bind_eq_some_iff] at step
            obtain ⟨stopP, _, stopLabel, _, rootPair, _, layerPair, _, rootCol, _,
              rootPart, _, tailPart, _, tailColumn, _, same⟩ := step
            simp only [Option.pure_def, Option.some.injEq] at same
            obtain ⟨next, leading⟩ := copied_head d rootPair.1 rootPair.2
              (List.replicate d 0) c hs rest _ (some _) _
            exact Or.inr ⟨next, same.symm.trans leading⟩

theorem reachable_leading_zero (d : Nat) (start e : NumericalExpr)
    (head : LeadingZero d start) (path : Reachable d start e) : LeadingZero d e := by
  induction path with
  | refl => exact head
  | step path edge ih => exact expand_leading_zero d _ _ _ ih edge

theorem standard_leading_zero (d : Nat) (e : NumericalExpr)
    (standard : Standard d e) : LeadingZero d e := by
  obtain ⟨k, path⟩ := standard
  exact reachable_leading_zero d (seed d k) e (Or.inr ⟨_, rfl⟩) path

end BTnSSBMS.Source
