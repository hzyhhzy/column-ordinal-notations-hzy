import FiniteDemandInitialRepresentation
import Mathlib.SetTheory.Cardinal.Aleph

/-!
# An actual host-Lean ambient instance

This instantiates the auxiliary environment using omega_1 and selected
enumerations of its smaller ordinals. It removes ambient assumptions from the
host-Lean well-ordering exits. This construction uses host choice; it is NOT a
certification of that step in KP. The weak-theory proof must construct the
corresponding environment in L and transfer the concrete ordinal ranks.
-/

namespace FiniteDemand.HostAmbient
open Set Cardinal
universe u

theorem iio_countable_iff (a : Label.{u}) : (Iio a).Countable ↔ a.card ≤ Cardinal.aleph0 := by
  rw [← Cardinal.le_aleph0_iff_set_countable, Cardinal.mk_Iio_ordinal, Cardinal.lift_le_aleph0]

theorem below_omegaOne_countable {a : Label.{u}} (ha : a < Ordinal.omega 1) :
    (Iio a).Countable := by
  apply (iio_countable_iff a).mpr
  exact (Cardinal.lt_aleph_one_iff).mp ((Cardinal.lt_omega_iff_card_lt).mp ha)

theorem omegaOne_uncountable : ¬ (Iio (Ordinal.omega.{u} 1)).Countable := by
  intro h
  have hh := (iio_countable_iff _).mp h
  rw [Ordinal.card_omega] at hh
  exact Cardinal.aleph0_lt_aleph_one.not_ge hh

theorem exists_enumeration {a : Label.{u}} (ha : 0 < a) (ha1 : a < Ordinal.omega 1) :
    ∃ f : Nat → Iio a, Function.Surjective f :=
  (Set.countable_iff_exists_surjective ⟨0, ha⟩).mp (below_omegaOne_countable ha1)

noncomputable def enumerate (a : Label.{u}) (n : Nat) : Label.{u} := by
  classical
  exact if h : 0 < a ∧ a < Ordinal.omega 1 then
    (Classical.choose (exists_enumeration h.1 h.2) n).val else 0

theorem enumerate_bounded (a : Label.{u}) (ha : a < Ordinal.omega 1) (n : Nat) :
    enumerate a n < Ordinal.omega 1 := by
  classical
  by_cases h : 0 < a ∧ a < Ordinal.omega 1
  · simp only [enumerate, dif_pos h]
    exact lt_trans (Classical.choose (exists_enumeration h.1 h.2) n).property ha
  · simp only [enumerate, dif_neg h]
    exact lt_trans Ordinal.omega0_pos Ordinal.omega0_lt_omega_one

theorem enumerate_covers (a : Label.{u}) (ha : a < Ordinal.omega 1)
    (b : Label.{u}) (hb : b < a) : ∃ n, enumerate a n = b := by
  classical
  have h : 0 < a ∧ a < Ordinal.omega 1 := ⟨lt_of_le_of_lt (bot_le : 0 ≤ b) hb, ha⟩
  obtain ⟨n, hn⟩ := Classical.choose_spec (exists_enumeration h.1 h.2) ⟨b, hb⟩
  refine ⟨n, ?_⟩
  simp only [enumerate, dif_pos h]
  exact congrArg Subtype.val hn

noncomputable def actual : Ambient.{u} where
  kappa := Ordinal.omega 1
  enumerate := enumerate
  omega_lt := Ordinal.omega0_lt_omega_one
  uncountable := omegaOne_uncountable
  bounded := enumerate_bounded
  covers := enumerate_covers

end FiniteDemand.HostAmbient

#print axioms FiniteDemand.HostAmbient.omegaOne_uncountable
#print axioms FiniteDemand.HostAmbient.enumerate_covers
#print axioms FiniteDemand.HostAmbient.actual
