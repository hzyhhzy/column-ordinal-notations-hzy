import OrdinalFormal.OmegaLRD3
import OrdinalFormal.Domains

namespace OrdinalFormal.OmegaLRD3
set_option autoImplicit false

abbrev Step := FSStep Diagram.nil fs

@[simp] theorem fs_nil (n : Nat) : fs .nil n = .nil := rfl

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
      exact ⟨d, hd.trans (reach_fs .nil fs fs_nil g n)⟩

theorem standard_finite_iff (g : Diagram) :
    Standard (.finite g) ↔ SeedDomain (Step := Step) seed g := by
  constructor
  · exact standard_sound
  · rintro ⟨n, h⟩
    exact reach_preserves .nil fs (fun g => Standard (.finite g))
      (fun _ ha k => Standard.child ha k) h (Standard.child Standard.top n)

theorem seed_reachable (d : Nat) : Reach Step (seed (d + 1)) (seed d) := by
  simpa only [seed_once_zero] using reach_fs .nil fs fs_nil (seed (d + 1)) 0

#print axioms standard_finite_iff
#print axioms seed_reachable
end OrdinalFormal.OmegaLRD3
