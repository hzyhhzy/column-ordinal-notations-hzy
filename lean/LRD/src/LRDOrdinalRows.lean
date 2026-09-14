import Mathlib.SetTheory.Cardinal.Aleph
import OrdinalRowLanguage
import OrdinalFormal.LRDColumnDecrease
import OrdinalFormal.LRDRowWellFounded

/-!
The actual normalized LRD row order embeds into one fixed countable ordinal.
The well-order input is the previously proved executable row comparator, not
diagram accessibility. This supplies row parameters for the new semantic
backend; it does not itself prove well-ordering of LRD column diagrams.
-/

namespace OrdinalFormal.LRDOrdinalRows
open LRDStructure LRDNormalLift
open scoped Cardinal Ordinal
set_option autoImplicit false
set_option maxHeartbeats 600000

def syntaxCode : LRD.Row → Option (List Nat)
  | .poly cs => some cs
  | .limit => none

theorem syntaxCode_injective : Function.Injective syntaxCode := by
  intro a b h
  cases a <;> cases b <;> simp_all [syntaxCode]

instance rowCountable : Countable LRD.Row := syntaxCode_injective.countable
instance normalRowCountable : Countable NormalRow := inferInstance

instance normalRowWellOrder : IsWellOrder NormalRow normalLt where
  wf := LRDRowWellFounded.normalRowCmp_wellFounded
  trichotomous := by
    intro a b hab hba
    rcases LRDColumnDecrease.normal_compare_laws.trichotomy a b with h | h | h
    · exact False.elim (hab h)
    · exact h
    · exact False.elim (hba h)

noncomputable def rowOrderType : Ordinal.{0} := Ordinal.type normalLt
noncomputable def ordinalCode (row : NormalRow) : Ordinal.{0} :=
  Ordinal.typein normalLt row

theorem ordinalCode_lt_iff (a b : NormalRow) :
    ordinalCode a < ordinalCode b ↔ normalRowCmp a b = .lt :=
  Ordinal.typein_lt_typein normalLt

theorem ordinalCode_injective : Function.Injective ordinalCode :=
  Ordinal.typein_injective normalLt

theorem ordinalCode_eq_iff (a b : NormalRow) : ordinalCode a = ordinalCode b ↔ a = b :=
  ordinalCode_injective.eq_iff

theorem ordinalCode_lt_type (a : NormalRow) : ordinalCode a < rowOrderType :=
  Ordinal.typein_lt_type normalLt a

theorem rowOrderType_card_le : rowOrderType.card ≤ Cardinal.aleph0 := by
  rw [rowOrderType, Ordinal.card_type]
  exact Cardinal.mk_le_aleph0

theorem rowOrderType_lt_omegaOne : rowOrderType < Ordinal.omega 1 := by
  rw [Cardinal.lt_omega_iff_card_lt, Cardinal.lt_aleph_one_iff]
  exact rowOrderType_card_le

/-- The fixed bound need not be calculated as a Cantor-normal-form ordinal.
Its countability and its exact order-preserving codes suffice for the backend. -/
noncomputable def sigma : Ordinal.{0} := max Ordinal.omega0 rowOrderType

theorem omega_le_sigma : Ordinal.omega0 ≤ sigma := le_max_left _ _
theorem type_le_sigma : rowOrderType ≤ sigma := le_max_right _ _

theorem sigma_lt_omegaOne : sigma < Ordinal.omega 1 :=
  max_lt Ordinal.omega0_lt_omega_one rowOrderType_lt_omegaOne

theorem sigma_card_le : sigma.card ≤ Cardinal.aleph0 := by
  have h := sigma_lt_omegaOne
  rwa [Cardinal.lt_omega_iff_card_lt, Cardinal.lt_aleph_one_iff] at h

noncomputable def embedRow (row : NormalRow) : OrdinalRow.RowBelow sigma :=
  ⟨ordinalCode row, lt_of_lt_of_le (ordinalCode_lt_type row) type_le_sigma⟩

theorem embedRow_lt_iff (a b : NormalRow) :
    (embedRow a).val < (embedRow b).val ↔ normalRowCmp a b = .lt :=
  ordinalCode_lt_iff a b

theorem embedRow_injective : Function.Injective embedRow := by
  intro a b h
  exact ordinalCode_injective (congrArg Subtype.val h)

/-- The actual generated package, after the proved normalization bridge, is
strictly lower in this same fixed ordinal interpretation. -/
theorem package_code_lt {high low : NormalRow} {b : Nat}
    (h : low ∈ normalPackage high b) :
    (embedRow low).val < (embedRow high).val :=
  (embedRow_lt_iff low high).mpr (normalPackage_lt h)

#print axioms normalRowWellOrder
#print axioms ordinalCode_lt_iff
#print axioms sigma_lt_omegaOne
#print axioms embedRow_injective
#print axioms package_code_lt

end OrdinalFormal.LRDOrdinalRows
