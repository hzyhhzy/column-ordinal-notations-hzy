import IPDDemandRecursion
import IPDProfileSubstitution

/-! Countable syntax templates with finitely many ordinal ROOT parameters and
one moving SELF. A template is an operation symbol; its ordinal parameters
are arguments, never uncountably many operation symbols. -/

namespace IPD.Semantics
set_option autoImplicit false
set_option maxHeartbeats 1000000
universe u

structure Template where
  arity : Nat
  profile : Profile Nat
  valid : ProfileAtoms (fun i => i ≤ arity) profile

instance templateCountable : Countable Template :=
  Function.Injective.countable (f := fun T : Template => (T.arity,T.profile))
    (by intro a b h; cases a; cases b; simpa only [Prod.mk.injEq,Template.mk.injEq] using h)

def Template.ofEdge (m : Nat) (e : Edge) (he : e.Valid m) : Template :=
  ⟨m,e.profile,profileAtoms_mono (fun i hi => by
      have hp := he.1
      rcases hi with hi | rfl <;> omega)
    e.profile he.2⟩

noncomputable def Template.eval (T : Template) (f : Fin T.arity → Label.{u})
    (b : Label.{u}) : Profile Label.{u} :=
  renameProfile (endpointMap T.arity (labels f) b) T.profile

noncomputable def relocate (old new x : Label.{u}) : Label.{u} :=
  if x = old then new else x

theorem Template.eval_relocate (T : Template) (f : Fin T.arity → Label.{u})
    {old : Label.{u}} (hf : ∀ i, f i < old) (new : Label.{u}) :
    renameProfile (relocate old new) (T.eval f old) = T.eval f new := by
  rw [Template.eval,renameProfile_comp]
  apply renameProfile_congr_on _ _ _ ?_ _ T.valid
  intro i hi
  by_cases hm : i = T.arity
  · simp [Function.comp_def,endpointMap,hm,relocate]
  · have hi' : i < T.arity := by omega
    have hn : f ⟨i,hi'⟩ ≠ old := ne_of_lt (hf ⟨i,hi'⟩)
    simp [Function.comp_def,endpointMap,hm,labels_apply f hi',relocate,hn]

theorem Template.eval_bounded (T : Template) (f : Fin T.arity → Label.{u})
    {b : Label.{u}} (hf : ∀ i, f i < b) :
    ProfileAtoms (fun x => x ≤ b) (T.eval f b) := by
  apply profileAtoms_rename _ _ _ ?_ _ T.valid
  intro i hi
  by_cases hm : i = T.arity
  · simp [endpointMap,hm]
  · have hi' : i < T.arity := by omega
    simpa [endpointMap,hm,labels_apply f hi'] using le_of_lt (hf ⟨i,hi'⟩)

theorem relocate_strict_on {old new : Label.{u}} (ho : old ≤ new) :
    ∀ a b, a ≤ old → b ≤ old → a < b → relocate old new a < relocate old new b := by
  intro a b ha hb hab
  have hane : a ≠ old := ne_of_lt (lt_of_lt_of_le hab hb)
  by_cases hbe : b = old
  · simp only [relocate,hane,hbe,if_false,if_true]
    exact lt_of_lt_of_le (hbe ▸ hab) ho
  · simpa only [relocate,hane,hbe,if_false] using hab

theorem template_lt_endpoint_iff {delta kappa : Label.{u}} (hdk : delta ≤ kappa)
    (T U : Template) (f : Fin T.arity → Label.{u}) (g : Fin U.arity → Label.{u})
    (hf : ∀ i, f i < delta) (hg : ∀ i, g i < delta) :
    T.eval f kappa < U.eval g kappa ↔ T.eval f delta < U.eval g delta := by
  rw [← T.eval_relocate f hf kappa,← U.eval_relocate g hg kappa]
  exact renameProfile_lt_iff_on (fun x => x ≤ delta) (relocate delta kappa)
    (relocate_strict_on hdk) _ _ (T.eval_bounded f hf) (U.eval_bounded g hg)

theorem template_eq_endpoint_iff {delta kappa : Label.{u}} (hdk : delta ≤ kappa)
    (T U : Template) (f : Fin T.arity → Label.{u}) (g : Fin U.arity → Label.{u})
    (hf : ∀ i, f i < delta) (hg : ∀ i, g i < delta) :
    T.eval f kappa = U.eval g kappa ↔ T.eval f delta = U.eval g delta := by
  constructor
  · intro h
    rcases lt_trichotomy (T.eval f delta) (U.eval g delta) with hl | he | hl
    · have hh := (template_lt_endpoint_iff hdk T U f g hf hg).mpr hl
      exact (ne_of_lt hh h).elim
    · exact he
    · have hh := (template_lt_endpoint_iff hdk U T g f hg hf).mpr hl
      exact (ne_of_lt hh h.symm).elim
  · intro h
    rw [← T.eval_relocate f hf kappa,← U.eval_relocate g hg kappa,h]

theorem relocate_profile_valid {old a : Label.{u}} (new : Label.{u}) (ha : a < old)
    (t : Profile Label.{u}) (ht : ProfileAtoms (fun x => x ≤ a ∨ x = old) t) :
    ProfileAtoms (fun x => x ≤ a ∨ x = new) (renameProfile (relocate old new) t) := by
  apply profileAtoms_rename _ _ _ ?_ t ht
  intro x hx
  rcases hx with hx | rfl
  · have hn : x ≠ old := ne_of_lt (lt_of_le_of_lt hx ha)
    exact Or.inl (by simpa [relocate,hn] using hx)
  · exact Or.inr (by simp [relocate])

theorem template_valid_endpoint_iff {delta kappa a : Label.{u}} (hdk : delta < kappa)
    (ha : a < delta) (T : Template) (f : Fin T.arity → Label.{u})
    (hf : ∀ i, f i < delta) :
    ProfileAtoms (fun x => x ≤ a ∨ x = kappa) (T.eval f kappa) ↔
      ProfileAtoms (fun x => x ≤ a ∨ x = delta) (T.eval f delta) := by
  constructor
  · intro ht
    rw [← T.eval_relocate f (fun i => lt_trans (hf i) hdk) delta]
    exact relocate_profile_valid delta (lt_trans ha hdk) _ ht
  · intro ht
    rw [← T.eval_relocate f hf kappa]
    exact relocate_profile_valid kappa ha _ ht

end IPD.Semantics

#print axioms IPD.Semantics.templateCountable
#print axioms IPD.Semantics.Template.eval_relocate
#print axioms IPD.Semantics.template_lt_endpoint_iff
#print axioms IPD.Semantics.template_valid_endpoint_iff
