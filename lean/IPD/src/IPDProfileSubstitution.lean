import IPDProfileValidity

/-! Substitution is compositional and depends only on atoms actually used.
These are finite-support statements, not global monotonicity assumptions. -/

namespace IPD.Tree
set_option autoImplicit false
universe u v
variable {X : Type u} {Y : Type v}

theorem all_mono {P Q : X → Prop} (h : ∀ x, P x → Q x) (t : Tree X)
    (ht : All P t) : All Q t := by
  induction t using IPD.Tree.inductionOn with
  | hz => exact all_zero Q
  | hn x xs ih =>
    obtain ⟨hx, hxs⟩ := (all_node_iff P x xs).mp ht
    exact (all_node_iff Q x xs).mpr ⟨h x hx, fun t ht => ih t ht (hxs t ht)⟩

theorem rename_congr_on (P : X → Prop) (f g : X → Y)
    (hfg : ∀ x, P x → f x = g x) (t : Tree X) (ht : All P t) :
    rename f t = rename g t := by
  induction t using IPD.Tree.inductionOn with
  | hz => simp
  | hn x xs ih =>
    obtain ⟨hx, hxs⟩ := (all_node_iff P x xs).mp ht
    simp only [rename_node, hfg x hx]
    congr 1
    exact List.map_congr_left fun t ht => ih t ht (hxs t ht)

end IPD.Tree

namespace IPD.Layer
set_option autoImplicit false
universe u v w
variable {X : Type u} {Y : Type v} {Z : Type w}

theorem allAtoms_mono {P Q : X → Prop} (h : ∀ x, P x → Q x) (d : Nat)
    (a : Layer X d) (ha : AllAtoms P d a) : AllAtoms Q d a := by
  induction d with
  | zero => exact h a ha
  | succ d ih =>
    apply Tree.all_mono (t := a) ?_ ha
    intro x hx
    cases x with
    | top => trivial
    | coe x => exact ih x hx

theorem rename_comp (f : X → Y) (g : Y → Z) (d : Nat) (a : Layer X d) :
    rename g d (rename f d a) = rename (g ∘ f) d a := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change Tree (WithTop (Layer X d)) at a
    change Tree.rename _ (Tree.rename _ a) = Tree.rename _ a
    rw [Tree.rename_comp]
    congr 1
    funext h
    cases h with
    | top => rfl
    | coe h => exact congrArg (fun x : Layer Z d => (x : WithTop (Layer Z d))) (ih h)

theorem rename_congr_on (P : X → Prop) (f g : X → Y)
    (hfg : ∀ x, P x → f x = g x) (d : Nat) (a : Layer X d)
    (ha : AllAtoms P d a) : rename f d a = rename g d a := by
  induction d with
  | zero => exact hfg a ha
  | succ d ih =>
    apply Tree.rename_congr_on _ _ _ ?_ a ha
    intro x hx
    cases x with
    | top => rfl
    | coe x => exact congrArg (fun y : Layer Y d => (y : WithTop (Layer Y d))) (ih x hx)

end IPD.Layer

namespace IPD
set_option autoImplicit false
universe u v w
variable {X : Type u} {Y : Type v} {Z : Type w}

theorem profileAtoms_mono {P Q : X → Prop} (h : ∀ x, P x → Q x)
    (a : Profile X) (ha : ProfileAtoms P a) : ProfileAtoms Q a :=
  Layer.allAtoms_mono h a.1 a.2 ha

theorem renameProfile_comp (f : X → Y) (g : Y → Z) (a : Profile X) :
    renameProfile g (renameProfile f a) = renameProfile (g ∘ f) a := by
  cases a with
  | mk d a => exact congrArg (fun x => (⟨d, x⟩ : Profile Z)) (Layer.rename_comp f g d a)

theorem renameProfile_congr_on (P : X → Prop) (f g : X → Y)
    (hfg : ∀ x, P x → f x = g x) (a : Profile X) (ha : ProfileAtoms P a) :
    renameProfile f a = renameProfile g a := by
  cases a with
  | mk d a =>
    exact congrArg (fun x => (⟨d, x⟩ : Profile Y))
      (Layer.rename_congr_on P f g hfg d a ha)

end IPD

#print axioms IPD.renameProfile_comp
#print axioms IPD.renameProfile_congr_on
#print axioms IPD.profileAtoms_mono
