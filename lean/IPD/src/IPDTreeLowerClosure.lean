import IPDTreeLinearOrder

/-!
# Finite candidate closure used by `lower`

An argument pair stores an original child and its optional lower approximation.
`replacements` enumerates all positions, preserving the preceding children and
replacing the following children by the current bound, exactly as in ipd.py.
-/

namespace IPD.Tree
set_option autoImplicit false
set_option maxHeartbeats 800000
universe u
variable {H : Type u} [LinearOrder H] [WellFoundedLT H]

abbrev LowerPair (H : Type u) := Tree H × Option (Tree H)

def replacements (bound : Tree H) : List (LowerPair H) → List (List (Tree H))
  | [] => []
  | (a, lo) :: ps =>
    (lo.toList.map fun b => b :: List.replicate ps.length bound) ++
      ((replacements bound ps).map (List.cons a))

def LowersValid (ps : List (LowerPair H)) : Prop :=
  ∀ p ∈ ps, ∀ b, p.2 = some b → b < p.1

theorem replacements_properties (ps : List (LowerPair H))
    (hlow : LowersValid ps) (bound target : Tree H) (hb : bound < target)
    (hchildren : ∀ p ∈ ps, p.1 < target) :
    ∀ ys ∈ replacements bound ps,
      ys.length = ps.length ∧ ArgsLt ((· < ·) : H → H → Prop) ys (ps.map Prod.fst) ∧
      ∀ y ∈ ys, y < target := by
  induction ps with
  | nil => simp [replacements]
  | cons p ps ih =>
    rcases p with ⟨a, lo⟩
    intro ys hy
    rcases List.mem_append.mp hy with hy | hy
    · obtain ⟨b, hblo, rfl⟩ := List.mem_map.mp hy
      have hlo : lo = some b := by simpa using hblo
      have hba := hlow (a, lo) (by simp) b hlo
      refine ⟨by simp, .rel hba, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact lt_trans hba (hchildren (a, lo) (by simp))
      · have hyb : y = bound := (List.mem_replicate.mp hy).2
        simpa only [hyb] using hb
    · obtain ⟨zs, hzs, rfl⟩ := List.mem_map.mp hy
      obtain ⟨hlen, hlex, hall⟩ := ih
        (fun p hp b hpb => hlow p (by simp [hp]) b hpb)
        (fun p hp => hchildren p (by simp [hp])) zs hzs
      refine ⟨by simpa using hlen, .cons hlex, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hchildren (y, lo) (by simp)
      · exact hall y hy

noncomputable def maximum (xs : List (Tree H)) : Tree H := xs.foldl max .zero

private theorem fold_max_lt (xs : List (Tree H)) (a target : Tree H)
    (ha : a < target) (hx : ∀ x ∈ xs, x < target) : xs.foldl max a < target := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih =>
    apply ih (max a x) (max_lt ha (hx x (by simp)))
    exact fun t ht => hx t (by simp [ht])

theorem maximum_lt (xs : List (Tree H)) (target : Tree H)
    (hz : (.zero : Tree H) < target) (hx : ∀ x ∈ xs, x < target) :
    maximum xs < target := fold_max_lt xs .zero target hz hx

noncomputable def closureRound (n : Nat) (h : H) (ps : List (LowerPair H))
    (smallerHead : Option H) (bound : Tree H) : Tree H := by
  classical
  exact maximum (bound ::
    ((if ps = [] then [] else [Tree.node h (List.replicate (ps.length - 1) bound)]) ++
    (smallerHead.toList.map fun g => Tree.node g (List.replicate n bound)) ++
    ((replacements bound ps).map (Tree.node h))))

theorem closureRound_lt (n : Nat) (h : H) (ps : List (LowerPair H))
    (smallerHead : Option H) (hlow : LowersValid ps)
    (hh : ∀ g, smallerHead = some g → g < h)
    (bound : Tree H) (hb : bound < .node h (ps.map Prod.fst)) :
    closureRound n h ps smallerHead bound < .node h (ps.map Prod.fst) := by
  classical
  apply maximum_lt _ _ (LPO.zero h _)
  intro t ht
  rcases List.mem_cons.mp ht with rfl | ht
  · exact hb
  · rcases List.mem_append.mp ht with ht | ht
    · rcases List.mem_append.mp ht with ht | ht
      · split at ht
        · simp at ht
        · rename_i hne
          simp only [List.mem_singleton] at ht
          subst t
          apply LPO.arity
          · simp only [List.length_replicate, List.length_map]
            have hp : 0 < ps.length := List.length_pos_iff.mpr hne
            omega
          · intro x hx
            have hxb : x = bound := (List.mem_replicate.mp hx).2
            rw [hxb]
            exact (lt_iff_lpo _ _).mp hb
      · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp ht
        have hg' : smallerHead = some g := by simpa using hg
        apply LPO.head (hh g hg')
        intro x hx
        have hxb : x = bound := (List.mem_replicate.mp hx).2
        rw [hxb]
        exact (lt_iff_lpo _ _).mp hb
    · obtain ⟨ys, hy, rfl⟩ := List.mem_map.mp ht
      obtain ⟨hlen, hlex, hall⟩ := replacements_properties ps hlow bound
        (.node h (ps.map Prod.fst)) hb
        (fun p hp => child_lt (List.mem_map_of_mem hp)) ys hy
      exact LPO.lex (by simpa only [List.length_map] using hlen) hlex hall

def rounds (step : Tree H → Tree H) : Nat → Tree H → Tree H
  | 0, a => a
  | n+1, a => rounds step n (step a)

theorem rounds_lt (step : Tree H → Tree H) (target : Tree H)
    (hs : ∀ a, a < target → step a < target) (n : Nat) (a : Tree H) (ha : a < target) :
    rounds step n a < target := by
  induction n generalizing a with
  | zero => exact ha
  | succ n ih => exact ih (step a) (hs a ha)

end IPD.Tree

#print axioms IPD.Tree.replacements_properties
#print axioms IPD.Tree.closureRound_lt
#print axioms IPD.Tree.rounds_lt
