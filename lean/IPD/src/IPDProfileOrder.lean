import IPDTreeLinearOrder
import IPDTreeRename

/-! The actual nested profile types K_0(X)=X and
K_(n+1)(X)=Tree (WithTop K_n(X)). CAP is the additional greatest **head**.
Profiles are the level-first disjoint sum; no levels are identified. -/

namespace IPD
set_option autoImplicit false
universe u v

def Layer (X : Type u) : Nat → Type u
  | 0 => X
  | n+1 => Tree (WithTop (Layer X n))

private structure WellOrderData (A : Type u) where
  order : LinearOrder A
  wf : @WellFounded A order.lt

private noncomputable def layerData (X : Type u) [LinearOrder X] [WellFoundedLT X] :
    (n : Nat) → WellOrderData (Layer X n)
  | 0 => by
    change WellOrderData X
    exact ⟨inferInstance, wellFounded_lt⟩
  | n+1 => by
    change WellOrderData (Tree (WithTop (Layer X n)))
    let d := layerData X n
    letI : LinearOrder (Layer X n) := d.order
    letI : WellFoundedLT (Layer X n) := ⟨d.wf⟩
    exact ⟨inferInstance, wellFounded_lt⟩

noncomputable instance layerLinearOrder (X : Type u) [LinearOrder X] [WellFoundedLT X]
    (n : Nat) : LinearOrder (Layer X n) := (layerData X n).order

instance layerWellFoundedLT (X : Type u) [LinearOrder X] [WellFoundedLT X]
    (n : Nat) : WellFoundedLT (Layer X n) := ⟨(layerData X n).wf⟩

abbrev Profile (X : Type u) := PSigma (Layer X)

def ProfileLt (X : Type u) [LinearOrder X] [WellFoundedLT X] :
    Profile X → Profile X → Prop := PSigma.Lex (· < ·) (fun _ => (· < ·))

theorem profileLt_wf (X : Type u) [LinearOrder X] [WellFoundedLT X] :
    WellFounded (ProfileLt X) := wellFounded_lt.psigma_lex (fun _ => wellFounded_lt)

theorem profileLt_trichotomy {X : Type u} [LinearOrder X] [WellFoundedLT X]
    (a b : Profile X) : ProfileLt X a b ∨ a = b ∨ ProfileLt X b a := by
  rcases a with ⟨n, a⟩
  rcases b with ⟨m, b⟩
  rcases lt_trichotomy n m with h | h | h
  · exact .inl (.left _ _ h)
  · subst m
    rcases lt_trichotomy a b with h | h | h
    · exact .inl (.right _ h)
    · subst b
      exact .inr (.inl rfl)
    · exact .inr (.inr (.right _ h))
  · exact .inr (.inr (.left _ _ h))

instance profileStrictTotalOrder (X : Type u) [LinearOrder X] [WellFoundedLT X] :
    IsStrictTotalOrder (Profile X) (ProfileLt X) where
  irrefl := (profileLt_wf X).irrefl.irrefl
  trichotomous a b hab hba := by
    rcases profileLt_trichotomy a b with h | h | h
    · exact (hab h).elim
    · exact h
    · exact (hba h).elim
  trans a b c hab hbc := by
    rcases profileLt_trichotomy a c with h | h | h
    · exact h
    · subst c
      exact ((profileLt_wf X).asymmetric _ _ hab hbc).elim
    · exact ((profileLt_wf X).asymmetric₃ _ _ _ hab hbc h).elim

noncomputable instance profileLinearOrder (X : Type u) [LinearOrder X] [WellFoundedLT X] :
    LinearOrder (Profile X) := by
  classical
  exact linearOrderOfSTO (ProfileLt X)

instance profileWellFoundedLT (X : Type u) [LinearOrder X] [WellFoundedLT X] :
    WellFoundedLT (Profile X) := ⟨profileLt_wf X⟩

theorem layer_wellFounded (X : Type u) [LinearOrder X] [WellFoundedLT X] (n : Nat) :
    WellFounded ((· < ·) : Layer X n → Layer X n → Prop) := wellFounded_lt

theorem profile_wellFounded (X : Type u) [LinearOrder X] [WellFoundedLT X] :
    WellFounded ((· < ·) : Profile X → Profile X → Prop) := wellFounded_lt

theorem profile_lt_of_level_lt {X : Type u} [LinearOrder X] [WellFoundedLT X]
    {n m : Nat} (a : Layer X n) (b : Layer X m) (h : n < m) :
    (⟨n, a⟩ : Profile X) < ⟨m, b⟩ := PSigma.Lex.left _ _ h

theorem profile_lt_same_level {X : Type u} [LinearOrder X] [WellFoundedLT X]
    {n : Nat} {a b : Layer X n} (h : a < b) :
    (⟨n, a⟩ : Profile X) < ⟨n, b⟩ := PSigma.Lex.right _ h

end IPD

#print axioms IPD.layer_wellFounded
#print axioms IPD.profile_wellFounded
#print axioms IPD.profile_lt_of_level_lt
