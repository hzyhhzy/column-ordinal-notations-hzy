import IPDProfileRename
import IPDTreeLocalRename

/-! Atomic support and comparison on a finite allowed alphabet. -/

namespace IPD.Layer
set_option autoImplicit false
set_option maxHeartbeats 800000
universe u v
variable {X : Type u} {Y : Type v}

def AllAtoms (P : X → Prop) : (d : Nat) → Layer X d → Prop
  | 0 => P
  | d+1 => Tree.All (fun h : WithTop (Layer X d) => match h with
      | none => True
      | some a => AllAtoms P d a)

theorem rename_lt_on [LinearOrder X] [WellFoundedLT X]
    [LinearOrder Y] [WellFoundedLT Y] (P : X → Prop) (f : X → Y)
    (hf : ∀ a b, P a → P b → a < b → f a < f b) (d : Nat) :
    ∀ a b : Layer X d, AllAtoms P d a → AllAtoms P d b → a < b →
      rename f d a < rename f d b := by
  induction d with
  | zero => exact hf
  | succ d ih =>
    intro a b ha hb hab
    apply Tree.rename_lpo_on
      (fun h : WithTop (Layer X d) => match h with
        | none => True
        | some a => AllAtoms P d a)
      (WithTop.map (rename f d)) ?_ b a ha hb hab
    intro x y hx hy hxy
    cases x with
    | top =>
      change (⊤ : WithTop (Layer X d)) < y at hxy
      exact (not_lt_of_ge le_top hxy).elim
    | coe x =>
      cases y with
      | top => exact WithTop.coe_lt_top _
      | coe y =>
        exact WithTop.coe_lt_coe.mpr (ih x y hx hy (WithTop.coe_lt_coe.mp hxy))

theorem rename_lt_iff_on [LinearOrder X] [WellFoundedLT X]
    [LinearOrder Y] [WellFoundedLT Y] (P : X → Prop) (f : X → Y)
    (hf : ∀ a b, P a → P b → a < b → f a < f b)
    (d : Nat) (a b : Layer X d) (ha : AllAtoms P d a) (hb : AllAtoms P d b) :
    rename f d a < rename f d b ↔ a < b := by
  constructor
  · intro h
    rcases lt_trichotomy a b with h' | he | h'
    · exact h'
    · subst b
      exact (lt_irrefl _ h).elim
    · exact (lt_asymm h (rename_lt_on P f hf d b a hb ha h')).elim
  · exact rename_lt_on P f hf d a b ha hb

end IPD.Layer

namespace IPD
universe u v
variable {X : Type u} {Y : Type v}

def ProfileAtoms (P : X → Prop) (p : Profile X) : Prop := Layer.AllAtoms P p.1 p.2

theorem renameProfile_lt_on [LinearOrder X] [WellFoundedLT X]
    [LinearOrder Y] [WellFoundedLT Y] (P : X → Prop) (f : X → Y)
    (hf : ∀ a b, P a → P b → a < b → f a < f b)
    (a b : Profile X) (ha : ProfileAtoms P a) (hb : ProfileAtoms P b) (hab : a < b) :
    renameProfile f a < renameProfile f b := by
  cases hab with
  | left a b h => exact .left _ _ h
  | right a h => exact .right _ (Layer.rename_lt_on P f hf _ _ _ ha hb h)

theorem renameProfile_lt_iff_on [LinearOrder X] [WellFoundedLT X]
    [LinearOrder Y] [WellFoundedLT Y] (P : X → Prop) (f : X → Y)
    (hf : ∀ a b, P a → P b → a < b → f a < f b)
    (a b : Profile X) (ha : ProfileAtoms P a) (hb : ProfileAtoms P b) :
    renameProfile f a < renameProfile f b ↔ a < b := by
  constructor
  · intro h
    rcases lt_trichotomy a b with h' | he | h'
    · exact h'
    · subst b
      exact (lt_irrefl _ h).elim
    · exact (lt_asymm h (renameProfile_lt_on P f hf b a hb ha h')).elim
  · exact renameProfile_lt_on P f hf a b ha hb

end IPD

#print axioms IPD.Layer.rename_lt_iff_on
#print axioms IPD.renameProfile_lt_iff_on
