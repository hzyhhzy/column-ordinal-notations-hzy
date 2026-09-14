import Std

/-!
# Finite unions of well-founded restrictions of a transitive relation

The domains need not be disjoint, initial segments, or downward closed.
Transitivity is essential: it makes a return from Q to P lie below the
original P bound. Only finite unions are proved; no countable-union inference
is made. This module supplies no well-foundedness theorem for any notation.
-/

namespace OrdinalFormal.FiniteUnionWellFounded

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 2048
universe u v
variable {A : Type u}

def Restricted (lt : A → A → Prop) (P : A → Prop) :
    {a : A // P a} → {a : A // P a} → Prop := fun a b => lt a.val b.val

/-- Restricting a well-founded domain to any smaller domain needs no
transitivity or initial-segment hypothesis. -/
theorem subset (lt : A → A → Prop) {P Q : A → Prop}
    (hPQ : ∀ a, P a → Q a) (hQ : WellFounded (Restricted lt Q)) :
    WellFounded (Restricted lt P) := by
  let f : {a : A // P a} → {a : A // Q a} := fun a => ⟨a.val, hPQ a.val a.property⟩
  exact ⟨fun a => InvImage.accessible f (hQ.apply (f a))⟩

/-- A binary union is well-founded under the same globally transitive
relation. Both input well-foundedness premises concern only their own domains. -/
theorem union (lt : A → A → Prop)
    (transLt : ∀ {a b c}, lt a b → lt b c → lt a c)
    (P Q : A → Prop)
    (hP : WellFounded (Restricted lt P))
    (hQ : WellFounded (Restricted lt Q)) :
    WellFounded (Restricted lt (fun a => P a ∨ Q a)) := by
  let U := {a : A // P a ∨ Q a}
  let r : U → U → Prop := fun a b => lt a.val b.val
  have qBelow (bound : U)
      (pBelow : ∀ z : U, P z.val → lt z.val bound.val → Acc r z) :
      ∀ y : {a : A // Q a}, lt y.val bound.val → Acc r ⟨y.val, Or.inr y.property⟩ := by
    intro y
    induction hQ.apply y with
    | intro y _ ih =>
      intro hy
      refine Acc.intro _ ?_
      intro z hz
      rcases z.property with hp | hq
      · exact pBelow z hp (transLt hz hy)
      · exact ih ⟨z.val, hq⟩ hz (transLt hz hy)
  have pAcc : ∀ x : {a : A // P a}, Acc r ⟨x.val, Or.inl x.property⟩ := by
    intro x
    induction hP.apply x with
    | intro x _ ih =>
      refine Acc.intro _ ?_
      intro y hy
      rcases y.property with hp | hq
      · exact ih ⟨y.val, hp⟩ hy
      · exact qBelow ⟨x.val, Or.inl x.property⟩
          (fun z hz hzx => ih ⟨z.val, hz⟩ hzx) ⟨y.val, hq⟩ hy
  have qAcc : ∀ x : {a : A // Q a}, Acc r ⟨x.val, Or.inr x.property⟩ := by
    intro x
    induction hQ.apply x with
    | intro x _ ih =>
      refine Acc.intro _ ?_
      intro y hy
      rcases y.property with hp | hq
      · exact pAcc ⟨y.val, hp⟩
      · exact ih ⟨y.val, hq⟩ hy
  refine ⟨fun x => ?_⟩
  rcases x.property with hp | hq
  · exact pAcc ⟨x.val, hp⟩
  · exact qAcc ⟨x.val, hq⟩

def InUnion (ps : List (A → Prop)) (a : A) : Prop := ∃ P ∈ ps, P a

theorem inUnion_cons (P : A → Prop) (ps : List (A → Prop)) (a : A) :
    InUnion (P :: ps) a ↔ P a ∨ InUnion ps a := by
  constructor
  · rintro ⟨Q, hQ, ha⟩
    rcases List.mem_cons.mp hQ with h | h
    · exact Or.inl (h ▸ ha)
    · exact Or.inr ⟨Q, h, ha⟩
  · rintro (h | ⟨Q, hQ, ha⟩)
    · exact ⟨P, List.mem_cons_self, h⟩
    · exact ⟨Q, List.mem_cons_of_mem P hQ, ha⟩

/-- Any finite list of well-founded domains has a well-founded union.
The empty list and repeated/overlapping domains are allowed. -/
theorem list_union (lt : A → A → Prop)
    (transLt : ∀ {a b c}, lt a b → lt b c → lt a c)
    (ps : List (A → Prop))
    (h : ∀ P ∈ ps, WellFounded (Restricted lt P)) :
    WellFounded (Restricted lt (InUnion ps)) := by
  induction ps with
  | nil =>
    refine ⟨fun a => ?_⟩
    obtain ⟨P, hP, _⟩ := a.property
    exact False.elim (List.not_mem_nil hP)
  | cons P ps ih =>
    have hP := h P List.mem_cons_self
    have hps := ih (fun Q hQ => h Q (List.mem_cons_of_mem P hQ))
    exact subset lt (fun a ha => (inUnion_cons P ps a).mp ha)
      (union lt @transLt P (InUnion ps) hP hps)

/-- A domain merely covered by finitely many well-founded pieces is enough;
the pieces need not be subdomains of the covered domain. -/
theorem finite_cover (lt : A → A → Prop)
    (transLt : ∀ {a b c}, lt a b → lt b c → lt a c)
    (S : A → Prop) (ps : List (A → Prop))
    (cover : ∀ a, S a → InUnion ps a)
    (h : ∀ P ∈ ps, WellFounded (Restricted lt P)) :
    WellFounded (Restricted lt S) :=
  subset lt cover (list_union lt @transLt ps h)

/-- Finite families with an arbitrary index type, explicitly enumerated.
Neither decidable equality of indices nor a choice of disjoint pieces is used. -/
theorem indexed_list_union {I : Type v} (lt : A → A → Prop)
    (transLt : ∀ {a b c}, lt a b → lt b c → lt a c)
    (indices : List I) (P : I → A → Prop)
    (h : ∀ i ∈ indices, WellFounded (Restricted lt (P i))) :
    WellFounded (Restricted lt (fun a => ∃ i ∈ indices, P i a)) := by
  apply finite_cover lt @transLt _ (indices.map P)
  · rintro a ⟨i, hi, ha⟩
    exact ⟨P i, List.mem_map.mpr ⟨i, hi, rfl⟩, ha⟩
  · intro Q hQ
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hQ
    exact h i hi

theorem indexed_finite_cover {I : Type v} (lt : A → A → Prop)
    (transLt : ∀ {a b c}, lt a b → lt b c → lt a c)
    (S : A → Prop) (indices : List I) (P : I → A → Prop)
    (cover : ∀ a, S a → ∃ i ∈ indices, P i a)
    (h : ∀ i ∈ indices, WellFounded (Restricted lt (P i))) :
    WellFounded (Restricted lt S) :=
  subset lt cover (indexed_list_union lt @transLt indices P h)

/-- An exhaustive finite enumeration gives the ordinary existential union. -/
theorem finite_family {I : Type v} (lt : A → A → Prop)
    (transLt : ∀ {a b c}, lt a b → lt b c → lt a c)
    (indices : List I) (complete : ∀ i, i ∈ indices) (P : I → A → Prop)
    (h : ∀ i, WellFounded (Restricted lt (P i))) :
    WellFounded (Restricted lt (fun a => ∃ i, P i a)) := by
  apply indexed_finite_cover lt @transLt _ indices P
  · rintro a ⟨i, hi⟩
    exact ⟨i, complete i, hi⟩
  · exact fun i _ => h i

/-- Audit helper: each singleton has a well-founded restriction of any
irreflexive relation, independently of behavior outside that singleton. -/
theorem singleton (lt : A → A → Prop) (irrefl : ∀ a, ¬ lt a a) (a : A) :
    WellFounded (Restricted lt (fun x => x = a)) := by
  refine ⟨fun x => Acc.intro x ?_⟩
  intro y hy
  have hx := x.property
  have hy' := y.property
  change lt y.val x.val at hy
  rw [hx, hy'] at hy
  exact False.elim (irrefl a hy)

/-- Audit boundary: the reverse natural order is transitive, every singleton
restriction is well-founded, but their countable union is not. -/
theorem countable_union_counterexample :
    (∀ {a b c : Nat}, b < a → c < b → c < a) ∧
    (∀ n : Nat, WellFounded (Restricted (fun a b : Nat => b < a) (fun a => a = n))) ∧
    ¬ WellFounded (Restricted (fun a b : Nat => b < a) (fun a => ∃ n : Nat, a = n)) := by
  refine ⟨fun h₁ h₂ => Nat.lt_trans h₂ h₁,
    fun n => singleton (fun a b : Nat => b < a) (fun a => Nat.lt_irrefl a) n, ?_⟩
  have noAcc : ∀ n : Nat, ¬ Acc (fun a b : Nat => b < a) n := by
    intro n hn
    induction hn with
    | intro n _ ih => exact ih (n + 1) (Nat.lt_succ_self n)
  intro hw
  let f : Nat → {a : Nat // ∃ n : Nat, a = n} := fun a => ⟨a, a, rfl⟩
  exact noAcc 0 (InvImage.accessible f (hw.apply (f 0)))

#print axioms union
#print axioms list_union
#print axioms finite_cover
#print axioms finite_family
#print axioms countable_union_counterexample

end OrdinalFormal.FiniteUnionWellFounded
