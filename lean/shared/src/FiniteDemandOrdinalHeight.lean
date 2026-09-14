import Mathlib.SetTheory.Ordinal.Family
import Mathlib.Data.Set.Countable

/-!
A downward closed countable collection of ordinals below an uncountable
endpoint is exactly an initial segment below a strictly smaller ordinal.
The proof uses no regularity assumption about the endpoint.
-/

namespace FiniteDemand.OrdinalHeight
open Set Ordinal Order
universe u

noncomputable def height (H : Set Ordinal.{u}) : Ordinal.{u} := sSup ((· + 1) '' H)

theorem successors_bounded {H : Set Ordinal.{u}} {kappa : Ordinal.{u}}
    (hb : ∀ x ∈ H, x < kappa) : BddAbove ((· + 1) '' H) := by
  refine ⟨kappa, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact add_one_le_iff.mpr (hb x hx)

theorem height_le {H : Set Ordinal.{u}} {kappa : Ordinal.{u}}
    (hne : H.Nonempty) (hb : ∀ x ∈ H, x < kappa) : height H ≤ kappa := by
  apply csSup_le (hne.image _)
  rintro _ ⟨x, hx, rfl⟩
  exact add_one_le_iff.mpr (hb x hx)

theorem mem_iff_lt {H : Set Ordinal.{u}} {kappa : Ordinal.{u}}
    (hne : H.Nonempty) (hb : ∀ x ∈ H, x < kappa)
    (hdown : ∀ x ∈ H, ∀ y, y < x → y ∈ H) (y : Ordinal.{u}) :
    y ∈ H ↔ y < height H := by
  constructor
  · intro hy
    exact lt_of_lt_of_le (lt_add_one y)
      (le_csSup (successors_bounded hb) (mem_image_of_mem _ hy))
  · intro hy
    obtain ⟨_, ⟨x, hx, rfl⟩, hyx⟩ :=
      (lt_csSup_iff (successors_bounded hb) (hne.image _)).mp hy
    rcases (lt_add_one_iff.mp hyx).eq_or_lt with heq | hlt
    · exact heq ▸ hx
    · exact hdown x hx y hlt

theorem height_lt {H : Set Ordinal.{u}} {kappa : Ordinal.{u}}
    (hne : H.Nonempty) (hc : H.Countable) (hb : ∀ x ∈ H, x < kappa)
    (hdown : ∀ x ∈ H, ∀ y, y < x → y ∈ H) (hk : ¬ (Iio kappa).Countable) :
    height H < kappa := by
  refine lt_of_le_of_ne (height_le hne hb) ?_
  intro heq
  apply hk
  have hH : H = Iio kappa := by
    ext y
    simpa [heq] using mem_iff_lt hne hb hdown y
  exact hH ▸ hc

end FiniteDemand.OrdinalHeight

#print axioms FiniteDemand.OrdinalHeight.mem_iff_lt
#print axioms FiniteDemand.OrdinalHeight.height_lt
