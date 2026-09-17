import ARD2DemandReflection
import Mathlib.Data.Countable.Basic

/-! Finite two-coordinate templates. Each coordinate independently denotes an
ordinary parameter or the endpoint SELF; no ordinal is an operation code. -/
namespace ARD2Demand
open OrdinalFormal
open OrdinalFormal.ReflectionTransport
set_option autoImplicit false
universe u

def RootEarlier : (Label.{u} × Label.{u}) → (Label.{u} × Label.{u}) → Prop :=
  Prod.Lex (· < ·) (· < ·)

theorem rootEarlier_wellFounded : WellFounded RootEarlier.{u} :=
  Ordinal.lt_wf.prod_lex Ordinal.lt_wf

structure Template where
  arity : Nat
  row : Nat
  root : Nat
  row_le : row ≤ arity
  root_le : root ≤ arity

instance templateCountable : Countable Template :=
  Function.Injective.countable (f := fun T : Template => (T.arity,T.row,T.root))
    (by intro a b h; cases a; cases b; simpa only [Prod.mk.injEq,Template.mk.injEq] using h)

instance entryCountable : Countable ARD2.Entry :=
  Function.Injective.countable (f := fun e : ARD2.Entry => (e.row,e.parent,e.root))
    (by intro a b h; cases a; cases b; simpa only [Prod.mk.injEq,Columns.Entry.mk.injEq] using h)

instance shapeCountable : Countable Shape :=
  Function.Injective.countable (f := fun A : Shape => (A.graph,A.cut,A.needs))
    (by intro a b h; cases a; cases b; simpa only [Prod.mk.injEq,Shape.mk.injEq] using h)

def Template.ofEntry (n : Nat) (e : ARD2.Entry) (he : ARD2.NeedValid n e) : Template :=
  ⟨n,e.row,e.root,he.1,he.2.1⟩

noncomputable def Template.eval (T : Template) (f : Fin T.arity → Label.{u})
    (b : Label.{u}) : Label.{u} × Label.{u} :=
  (ARD2.atEnd T.arity (labels f) b T.row, ARD2.atEnd T.arity (labels f) b T.root)

theorem atEnd_bounded {n : Nat} (f : Fin n → Label.{u}) {b : Label.{u}}
    (hf : ∀ i, f i < b) (i : Nat) : ARD2.atEnd n (labels f) b i ≤ b := by
  by_cases hi : i < n
  · simpa [ARD2.atEnd,hi,labels] using le_of_lt (hf ⟨i,hi⟩)
  · simp [ARD2.atEnd,hi]

theorem Template.eval_bounded (T : Template) (f : Fin T.arity → Label.{u})
    {b : Label.{u}} (hf : ∀ i, f i < b) : (T.eval f b).1 ≤ b ∧ (T.eval f b).2 ≤ b :=
  ⟨atEnd_bounded f hf T.row,atEnd_bounded f hf T.root⟩

theorem atEnd_lt_endpoint_iff {delta kappa : Label.{u}} (hdk : delta ≤ kappa)
    {n m : Nat} (f : Fin n → Label.{u}) (g : Fin m → Label.{u})
    (hf : ∀ i, f i < delta) (hg : ∀ i, g i < delta) (i j : Nat) :
    ARD2.atEnd n (labels f) kappa i < ARD2.atEnd m (labels g) kappa j ↔
      ARD2.atEnd n (labels f) delta i < ARD2.atEnd m (labels g) delta j := by
  by_cases hi : i < n <;> by_cases hj : j < m
  · simp [ARD2.atEnd,hi,hj]
  · have hd := hf ⟨i,hi⟩
    have hk := lt_of_lt_of_le hd hdk
    simp [ARD2.atEnd,hi,hj,labels,hd,hk]
  · have hd := hg ⟨j,hj⟩
    have hk := lt_of_lt_of_le hd hdk
    simp [ARD2.atEnd,hi,hj,labels,not_lt_of_ge hd.le,not_lt_of_ge hk.le]
  · simp [ARD2.atEnd,hi,hj]

theorem atEnd_eq_endpoint_iff {delta kappa : Label.{u}} (hdk : delta ≤ kappa)
    {n m : Nat} (f : Fin n → Label.{u}) (g : Fin m → Label.{u})
    (hf : ∀ i, f i < delta) (hg : ∀ i, g i < delta) (i j : Nat) :
    ARD2.atEnd n (labels f) kappa i = ARD2.atEnd m (labels g) kappa j ↔
      ARD2.atEnd n (labels f) delta i = ARD2.atEnd m (labels g) delta j := by
  by_cases hi : i < n <;> by_cases hj : j < m
  · simp [ARD2.atEnd,hi,hj]
  · have hd := hf ⟨i,hi⟩
    have hk := lt_of_lt_of_le hd hdk
    simp [ARD2.atEnd,hi,hj,labels,ne_of_lt hd,ne_of_lt hk]
  · have hd := hg ⟨j,hj⟩
    have hk := lt_of_lt_of_le hd hdk
    simp [ARD2.atEnd,hi,hj,labels,ne_of_gt hd,ne_of_gt hk]
  · simp [ARD2.atEnd,hi,hj]

theorem template_lt_endpoint_iff {delta kappa : Label.{u}} (hdk : delta ≤ kappa)
    (T U : Template) (f : Fin T.arity → Label.{u}) (g : Fin U.arity → Label.{u})
    (hf : ∀ i, f i < delta) (hg : ∀ i, g i < delta) :
    RootEarlier (T.eval f kappa) (U.eval g kappa) ↔
      RootEarlier (T.eval f delta) (U.eval g delta) := by
  simp only [RootEarlier,Prod.lex_def,Template.eval]
  rw [atEnd_lt_endpoint_iff hdk f g hf hg T.row U.row,
      atEnd_eq_endpoint_iff hdk f g hf hg T.row U.row,
      atEnd_lt_endpoint_iff hdk f g hf hg T.root U.root]

noncomputable def pairRelation (t : Label.{u} × Label.{u}) (a b : Label.{u}) : Prop :=
  relation t.1 t.2 a b

theorem pair_relation_iff (t : Label.{u} × Label.{u}) (a b : Label.{u}) :
    pairRelation t a b ↔ Rule relation (b,t) a := relation_iff t.1 t.2 a b

theorem pair_strict {t : Label.{u} × Label.{u}} {a b : Label.{u}}
    (h : pairRelation t a b) : a < b := strict h

theorem pair_parent_domain {t : Label.{u} × Label.{u}} {a b : Label.{u}}
    (h : pairRelation t a b) : domain a := parent_domain h

end ARD2Demand

#print axioms ARD2Demand.templateCountable
#print axioms ARD2Demand.template_lt_endpoint_iff
