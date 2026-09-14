import Mathlib.Data.Set.Countable
import Mathlib.Data.List.Basic

/-! Countable closure under a countable family of actual finitary operations.
No reflection, regularity, or semantic existence principle is assumed. -/

namespace FiniteDemand.FinitaryClosure

universe u v
variable {X : Type u} {Op : Type v}

def next (eval : Op → List X → X) (H : Set X) : Set X :=
  H ∪ Set.range (fun p : Op × List H => eval p.1 (p.2.map Subtype.val))

def stage (eval : Op → List X → X) (constants : Nat → X) : Nat → Set X
  | 0 => Set.range constants
  | n + 1 => next eval (stage eval constants n)

def closure (eval : Op → List X → X) (constants : Nat → X) : Set X :=
  ⋃ n, stage eval constants n

theorem stage_subset_succ (eval : Op → List X → X) (constants : Nat → X) (n : Nat) :
    stage eval constants n ⊆ stage eval constants (n+1) := fun _ h => Or.inl h

theorem stage_mono (eval : Op → List X → X) (constants : Nat → X) :
    Monotone (stage eval constants) :=
  monotone_nat_of_le_succ (stage_subset_succ eval constants)

theorem mem_closure_iff (eval : Op → List X → X) (constants : Nat → X) (x : X) :
    x ∈ closure eval constants ↔ ∃ n, x ∈ stage eval constants n := Set.mem_iUnion

theorem constant_mem (eval : Op → List X → X) (constants : Nat → X) (n : Nat) :
    constants n ∈ closure eval constants :=
  (mem_closure_iff _ _ _).mpr ⟨0, n, rfl⟩

theorem next_apply (eval : Op → List X → X) (H : Set X) (o : Op) (xs : List X)
    (hxs : ∀ x ∈ xs, x ∈ H) : eval o xs ∈ next eval H := by
  let ys : List H := xs.attach.map (fun x => ⟨x.val, hxs x.val x.property⟩)
  have hy : ys.map Subtype.val = xs := by simp [ys, List.map_map]
  exact Or.inr ⟨(o, ys), by simp [hy]⟩

theorem finite_stage (eval : Op → List X → X) (constants : Nat → X) (xs : List X)
    (hxs : ∀ x ∈ xs, x ∈ closure eval constants) :
    ∃ n, ∀ x ∈ xs, x ∈ stage eval constants n := by
  induction xs with
  | nil => exact ⟨0, by simp⟩
  | cons x xs ih =>
    obtain ⟨n, hn⟩ := (mem_closure_iff _ _ _).mp (hxs x (by simp))
    obtain ⟨m, hm⟩ := ih (fun y hy => hxs y (by simp [hy]))
    refine ⟨max n m, ?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact stage_mono eval constants (Nat.le_max_left _ _) hn
    · exact stage_mono eval constants (Nat.le_max_right _ _) (hm y hy)

theorem apply_mem (eval : Op → List X → X) (constants : Nat → X) (o : Op) (xs : List X)
    (hxs : ∀ x ∈ xs, x ∈ closure eval constants) : eval o xs ∈ closure eval constants := by
  obtain ⟨n, hn⟩ := finite_stage eval constants xs hxs
  exact (mem_closure_iff _ _ _).mpr ⟨n+1, next_apply eval _ o xs hn⟩

theorem next_countable [Countable Op] (eval : Op → List X → X) (H : Set X)
    (hH : H.Countable) : (next eval H).Countable := by
  letI : Countable H := hH.to_subtype
  exact hH.union (Set.countable_range _)

theorem countable [Countable Op] (eval : Op → List X → X) (constants : Nat → X) :
    (closure eval constants).Countable := by
  apply Set.countable_iUnion
  intro n
  induction n with
  | zero => exact Set.countable_range constants
  | succ n ih => exact next_countable eval _ ih

theorem invariant (eval : Op → List X → X) (constants : Nat → X) (P : X → Prop)
    (hc : ∀ n, P (constants n))
    (he : ∀ o xs, (∀ x ∈ xs, P x) → P (eval o xs)) :
    ∀ x ∈ closure eval constants, P x := by
  intro x hx
  obtain ⟨n, hn⟩ := (mem_closure_iff _ _ _).mp hx
  have hall : ∀ n x, x ∈ stage eval constants n → P x := by
    intro n
    induction n with
    | zero =>
      intro x hx
      obtain ⟨i, rfl⟩ := hx
      exact hc i
    | succ n ih =>
      intro x hx
      rcases hx with hx | ⟨⟨o, ys⟩, rfl⟩
      · exact ih x hx
      · apply he
        intro y hy
        obtain ⟨z, _, rfl⟩ := List.mem_map.mp hy
        exact ih z.val z.property
  exact hall n x hn

end FiniteDemand.FinitaryClosure

#print axioms FiniteDemand.FinitaryClosure.apply_mem
#print axioms FiniteDemand.FinitaryClosure.countable
#print axioms FiniteDemand.FinitaryClosure.invariant
