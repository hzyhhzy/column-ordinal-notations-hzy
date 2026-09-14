import IPDTreeLowerClosure

/-! The all-position version of the actual finite tree lowering algorithm.
It recurses only into original children; closure candidates are not recursively
lowered again.  The lower-head operation is supplied by the next lower IPD level. -/

namespace IPD.Tree
set_option autoImplicit false
set_option maxHeartbeats 800000
universe u
variable {H : Type u} [LinearOrder H] [WellFoundedLT H]

noncomputable def initialBound (h : H) (xs : List (Tree H)) : Tree H := by
  classical
  exact if xs = [] then .zero else maximum (.node h [] :: xs)

theorem initialBound_lt (h : H) (xs : List (Tree H)) : initialBound h xs < .node h xs := by
  classical
  unfold initialBound
  split
  · exact LPO.zero h xs
  · rename_i hne
    apply maximum_lt _ _ (LPO.zero h xs)
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact leaf_lt_nonleaf hne
    · exact child_lt hx

noncomputable def lower (n : Nat) (lowerHead : H → Option H) : Tree H → Option (Tree H)
  | .zero => none
  | .node h xs => some (rounds
      (closureRound n h (xs.map fun x => (x, lower n lowerHead x)) (lowerHead h))
      (n+1) (initialBound h xs))

@[simp] theorem lower_zero (n : Nat) (lowerHead : H → Option H) :
    lower n lowerHead .zero = none := by simp [lower]

theorem lower_node (n : Nat) (lowerHead : H → Option H) (h : H) (xs : List (Tree H)) :
    lower n lowerHead (.node h xs) = some (rounds
      (closureRound n h (xs.map fun x => (x, lower n lowerHead x)) (lowerHead h))
      (n+1) (initialBound h xs)) := by simp [lower]

theorem lower_lt (n : Nat) (lowerHead : H → Option H)
    (hh : ∀ h g, lowerHead h = some g → g < h) (t : Tree H) :
    ∀ u, lower n lowerHead t = some u → u < t := by
  induction t using IPD.Tree.inductionOn with
  | hz => simp
  | hn h xs ih =>
    intro u hu
    rw [lower_node] at hu
    have hu' := Option.some.inj hu
    rw [← hu']
    let ps := xs.map fun x => (x, lower n lowerHead x)
    have hp : ps.map Prod.fst = xs := by simp [ps, List.map_map, Function.comp_def]
    have hl : LowersValid ps := by
      intro p hmem b hpb
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hmem
      exact ih x hx b hpb
    apply rounds_lt _ _ (fun a ha => ?_) (n+1) _ (initialBound_lt h xs)
    have hc := closureRound_lt n h ps (lowerHead h) hl (hh h) a
      (by simpa only [hp] using ha)
    simpa only [hp] using hc

theorem lower_none_iff (n : Nat) (lowerHead : H → Option H) (t : Tree H) :
    lower n lowerHead t = none ↔ t = .zero := by
  cases t with
  | zero => simp
  | node h xs => simp only [lower_node, Option.some_ne_none, node_ne_zero]

end IPD.Tree

#print axioms IPD.Tree.lower_lt
#print axioms IPD.Tree.lower_none_iff
