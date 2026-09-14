import IPDTreeOrder
import Mathlib.Order.WithBot

/-! The abstract LPO relation as an ordinary Lean linear well-order.
The use of a noncomputable order instance does not change its relation;
`lt_iff_lpo` is definitional. Computational correspondence is separate. -/

namespace IPD.Tree
set_option autoImplicit false
universe u
variable {H : Type u} [LinearOrder H] [WellFoundedLT H]

instance lpoStrictTotalOrder : IsStrictTotalOrder (Tree H) (LPO (· < ·)) where
  irrefl := lpo_irrefl wellFounded_lt
  trans _ _ _ := lpo_trans wellFounded_lt lt_trichotomy
  trichotomous a b hab hba := by
    rcases lpo_trichotomy lt_trichotomy a b with h | h | h
    · exact (hab h).elim
    · exact h
    · exact (hba h).elim

noncomputable instance linearOrder : LinearOrder (Tree H) := by
  classical
  exact linearOrderOfSTO (LPO (· < ·))

theorem lt_iff_lpo (s t : Tree H) : s < t ↔ LPO (· < ·) s t := Iff.rfl

instance wellFoundedLT : WellFoundedLT (Tree H) where
  wf := lpo_wellFounded wellFounded_lt

instance orderBot : OrderBot (Tree H) where
  bot := .zero
  bot_le t := by
    cases t with
    | zero => exact le_rfl
    | node h xs => exact le_of_lt (LPO.zero h xs)

end IPD.Tree

#print axioms IPD.Tree.linearOrder
#print axioms IPD.Tree.wellFoundedLT
#print axioms IPD.Tree.lt_iff_lpo
