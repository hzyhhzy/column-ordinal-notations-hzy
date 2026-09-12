import OrdinalFormal.RPD
import OrdinalFormal.LRD
import OrdinalFormal.Reachability

namespace OrdinalFormal

set_option maxHeartbeats 500000

universe u
variable {α : Type u}

/-- Allowing the convention 0[n]=0 in generation does not enlarge the
finite descendant domain of the STRICT step relation. -/
theorem reach_fs (zero : α) (fs : α → Nat → α)
    (zero_fs : ∀ n, fs zero n = zero) (a : α) (n : Nat) :
    Reach (FSStep zero fs) a (fs a n) := by
  classical
  by_cases h : a = zero
  · subst a
    rw [zero_fs]
    exact .refl _
  · exact .single ⟨h, n, rfl⟩

theorem reach_preserves (zero : α) (fs : α → Nat → α) (P : α → Prop)
    (child : ∀ a, P a → ∀ n, P (fs a n))
    {a b : α} (h : Reach (FSStep zero fs) a b) (ha : P a) : P b := by
  induction h with
  | refl => exact ha
  | @cons a d b had hdb ih =>
    obtain ⟨_, n, rfl⟩ := had
    exact ih (child a ha n)

namespace RPD

abbrev Step := FSStep ([] : Diagram) fs

private theorem standard_sound {a : Term} (h : Standard a) :
    match a with
    | .top => True
    | .finite g => SeedDomain (Step := Step) seed g := by
  induction h with
  | top => trivial
  | @child a h n ih =>
    cases a with
    | top => exact ⟨n, .refl _⟩
    | finite g =>
      obtain ⟨d, hd⟩ := ih
      exact ⟨d, hd.trans (reach_fs [] fs (fun n => Columns.expand_empty _ _ n) g n)⟩

theorem standard_finite_iff (g : Diagram) :
    Standard (.finite g) ↔ SeedDomain (Step := Step) seed g := by
  constructor
  · exact standard_sound
  · rintro ⟨n, h⟩
    exact reach_preserves [] fs (fun g => Standard (.finite g))
      (fun _ ha k => Standard.child ha k) h (Standard.child Standard.top n)

end RPD

namespace LRD

abbrev Step := FSStep ([] : Diagram) fs

theorem standard_iff (g : Diagram) : Standard g ↔ Reach Step seed g := by
  constructor
  · intro h
    induction h with
    | seed => exact .refl _
    | @child a h n ih =>
      exact ih.trans (reach_fs [] fs (fun n => Columns.expand_empty _ _ n) a n)
  · intro h
    exact reach_preserves [] fs Standard (fun _ ha n => .child ha n) h .seed

end LRD

end OrdinalFormal
