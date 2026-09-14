import IPDTreeLocalRename
import IPDTreeLower

/-! Lowering and relabeling preserve the allowed head alphabet. -/

namespace IPD.Tree
set_option autoImplicit false
set_option maxHeartbeats 1000000
universe u v
variable {H : Type u} {J : Type v}

theorem all_rename (P : H → Prop) (Q : J → Prop) (f : H → J)
    (hf : ∀ h, P h → Q (f h)) (t : Tree H) : All P t → All Q (rename f t) := by
  induction t using IPD.Tree.inductionOn with
  | hz => intro _; exact (rename_zero f) ▸ all_zero Q
  | hn h xs ih =>
    intro ht
    obtain ⟨hh, hxs⟩ := (all_node_iff P h xs).mp ht
    rw [rename_node, all_node_iff]
    refine ⟨hf h hh, ?_⟩
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact ih y hy (hxs y hy)

section Lower
variable [LinearOrder H] [WellFoundedLT H]

def PairsAll (P : H → Prop) (ps : List (LowerPair H)) : Prop :=
  ∀ p ∈ ps, All P p.1 ∧ ∀ b, p.2 = some b → All P b

theorem replacements_all (P : H → Prop) (ps : List (LowerPair H))
    (hp : PairsAll P ps) (bound : Tree H) (hb : All P bound) :
    ∀ ys ∈ replacements bound ps, ∀ y ∈ ys, All P y := by
  induction ps with
  | nil => simp [replacements]
  | cons p ps ih =>
    rcases p with ⟨a, lo⟩
    intro ys hy y hym
    rcases List.mem_append.mp hy with hy | hy
    · obtain ⟨b, hblo, rfl⟩ := List.mem_map.mp hy
      have hlo : lo = some b := by simpa using hblo
      rcases List.mem_cons.mp hym with rfl | hm
      · exact (hp (a, lo) (by simp)).2 y hlo
      · have he : y = bound := (List.mem_replicate.mp hm).2
        simpa only [he] using hb
    · obtain ⟨zs, hz, rfl⟩ := List.mem_map.mp hy
      rcases List.mem_cons.mp hym with rfl | hm
      · exact (hp (y, lo) (by simp)).1
      · exact ih (fun p hm => hp p (by simp [hm])) zs hz y hm

private theorem fold_max_all (P : H → Prop) (xs : List (Tree H)) (a : Tree H)
    (ha : All P a) (hx : ∀ x ∈ xs, All P x) : All P (xs.foldl max a) := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih =>
    apply ih (max a x)
    · rcases le_total a x with h | h
      · rw [max_eq_right h]
        exact hx x (by simp)
      · rw [max_eq_left h]
        exact ha
    · exact fun t ht => hx t (by simp [ht])

theorem maximum_all (P : H → Prop) (xs : List (Tree H))
    (h : ∀ x ∈ xs, All P x) : All P (maximum xs) :=
  fold_max_all P xs .zero (all_zero P) h

theorem closureRound_all (P : H → Prop) (n : Nat) (h : H) (ps : List (LowerPair H))
    (smallerHead : Option H) (hh : P h) (hp : PairsAll P ps)
    (hs : ∀ g, smallerHead = some g → P g) (bound : Tree H) (hb : All P bound) :
    All P (closureRound n h ps smallerHead bound) := by
  classical
  apply maximum_all
  intro t ht
  rcases List.mem_cons.mp ht with rfl | ht
  · exact hb
  · rcases List.mem_append.mp ht with ht | ht
    · rcases List.mem_append.mp ht with ht | ht
      · split at ht
        · simp at ht
        · simp only [List.mem_singleton] at ht
          subst t
          apply (all_node_iff _ _ _).mpr
          refine ⟨hh, ?_⟩
          intro x hx
          have he : x = bound := (List.mem_replicate.mp hx).2
          simpa only [he] using hb
      · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp ht
        have hg' : smallerHead = some g := by simpa using hg
        apply (all_node_iff _ _ _).mpr
        refine ⟨hs g hg', ?_⟩
        intro x hx
        have he : x = bound := (List.mem_replicate.mp hx).2
        simpa only [he] using hb
    · obtain ⟨ys, hy, rfl⟩ := List.mem_map.mp ht
      exact (all_node_iff _ _ _).mpr ⟨hh, replacements_all P ps hp bound hb ys hy⟩

theorem initialBound_all (P : H → Prop) (h : H) (xs : List (Tree H))
    (hh : P h) (hx : ∀ x ∈ xs, All P x) : All P (initialBound h xs) := by
  classical
  unfold initialBound
  split
  · exact all_zero P
  · apply maximum_all
    intro x hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact (all_node_iff _ _ _).mpr ⟨hh, by simp⟩
    · exact hx x hm

omit [LinearOrder H] [WellFoundedLT H] in
theorem rounds_all (P : H → Prop) (step : Tree H → Tree H)
    (hs : ∀ a, All P a → All P (step a)) (n : Nat) (a : Tree H) (ha : All P a) :
    All P (rounds step n a) := by
  induction n generalizing a with
  | zero => exact ha
  | succ n ih => exact ih (step a) (hs a ha)

theorem lower_all (P : H → Prop) (n : Nat) (lowerHead : H → Option H)
    (hh : ∀ h, P h → ∀ g, lowerHead h = some g → P g) (t : Tree H) :
    All P t → ∀ u, lower n lowerHead t = some u → All P u := by
  induction t using IPD.Tree.inductionOn with
  | hz => simp
  | hn h xs ih =>
    intro ht u hu
    obtain ⟨hPh, hPxs⟩ := (all_node_iff _ _ _).mp ht
    rw [lower_node] at hu
    have hu' := Option.some.inj hu
    rw [← hu']
    let ps := xs.map fun x => (x, lower n lowerHead x)
    have hp : PairsAll P ps := by
      intro p hmem
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hmem
      exact ⟨hPxs x hx, fun b hb => ih x hx (hPxs x hx) b hb⟩
    exact rounds_all P _ (fun a ha => closureRound_all P n h ps (lowerHead h)
      hPh hp (hh h hPh) a ha) (n+1) _ (initialBound_all P h xs hPh hPxs)

end Lower
end IPD.Tree

#print axioms IPD.Tree.all_rename
#print axioms IPD.Tree.closureRound_all
#print axioms IPD.Tree.lower_all
