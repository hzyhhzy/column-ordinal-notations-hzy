import IPDEndpointAgreement
import FiniteDemandFinitaryClosure
import FiniteDemandOrdinalHeight

/-! The closure hypotheses in EndpointAgreement are constructed here.
Countably many syntax templates give countably many finitary operations.
An enumerator makes the hull downward closed; no regularity is assumed. -/

namespace IPD.Semantics.ClosedSupply
set_option autoImplicit false
universe u

abbrev Op := Nat ⊕ ((Template × Nat) ⊕ (Shape × Nat))

noncomputable def eval (kappa : Label.{u}) (e : Label.{u} → Nat → Label.{u}) :
    Op → List Label.{u} → Label.{u}
  | .inl n, xs => e (xs.getD 0 0) n
  | .inr (.inl (T,i)), xs => badOp T i (fun j => xs.getD (j.val+1) 0) (xs.getD 0 0) kappa
  | .inr (.inr (A,i)), xs => extOp relation kappa A i (fun j => xs.getD j 0)

def seeds (gamma : Label.{u}) : Nat → Label.{u}
  | 0 => Ordinal.omega0
  | 1 => gamma
  | _ + 2 => 0

noncomputable def hull (kappa : Label.{u}) (e : Label.{u} → Nat → Label.{u})
    (gamma : Label.{u}) : Set Label.{u} :=
  FiniteDemand.FinitaryClosure.closure (eval kappa e) (seeds gamma)

theorem getD_preserves {X : Type*} (P : X → Prop) (xs : List X) (i : Nat) (z : X)
    (hz : P z) (hxs : ∀ x ∈ xs, P x) : P (xs.getD i z) := by
  induction xs generalizing i with
  | nil => simpa using hz
  | cons x xs ih =>
    cases i with
    | zero => simpa only [List.getD_cons_zero] using hxs x (by simp)
    | succ i => exact ih i (fun y hy => hxs y (by simp [hy]))

theorem getD_ofFn {n : Nat} (f : Fin n → Label.{u}) (j : Fin n) :
    (List.ofFn f).getD j 0 = f j := by
  simp [List.getD_eq_getElem?_getD,List.getElem?_ofFn,j.isLt]

theorem hull_countable (kappa : Label.{u}) (e : Label.{u} → Nat → Label.{u})
    (gamma : Label.{u}) : (hull kappa e gamma).Countable :=
  FiniteDemand.FinitaryClosure.countable _ _

theorem omega_mem (kappa : Label.{u}) (e : Label.{u} → Nat → Label.{u}) (gamma : Label.{u}) :
    Ordinal.omega0 ∈ hull kappa e gamma :=
  FiniteDemand.FinitaryClosure.constant_mem _ (seeds gamma) 0

theorem gamma_mem (kappa : Label.{u}) (e : Label.{u} → Nat → Label.{u}) (gamma : Label.{u}) :
    gamma ∈ hull kappa e gamma :=
  FiniteDemand.FinitaryClosure.constant_mem _ (seeds gamma) 1

theorem hull_bounded {kappa : Label.{u}} (e : Label.{u} → Nat → Label.{u})
    {gamma : Label.{u}} (hk : Ordinal.omega0 < kappa) (hg : gamma < kappa)
    (he : ∀ a, a < kappa → ∀ n, e a n < kappa) :
    ∀ x ∈ hull kappa e gamma, x < kappa := by
  have h0 : (0 : Label.{u}) < kappa := lt_trans Ordinal.omega0_pos hk
  apply FiniteDemand.FinitaryClosure.invariant
  · intro n
    cases n with
    | zero => exact hk
    | succ n =>
      cases n with
      | zero => exact hg
      | succ n => exact h0
  · intro o xs hxs
    rcases o with n | (⟨T,i⟩ | ⟨A,i⟩)
    · exact he _ (getD_preserves (· < kappa) xs 0 0 h0 hxs) n
    · exact badOp_lt T i _ _ kappa h0
    · exact extOp_lt relation kappa A i _ h0

theorem hull_downward {kappa : Label.{u}} (e : Label.{u} → Nat → Label.{u})
    {gamma : Label.{u}} (hk : Ordinal.omega0 < kappa) (hg : gamma < kappa)
    (he : ∀ a, a < kappa → ∀ n, e a n < kappa)
    (hs : ∀ a, a < kappa → ∀ b, b < a → ∃ n, e a n = b) :
    ∀ x ∈ hull kappa e gamma, ∀ y, y < x → y ∈ hull kappa e gamma := by
  intro x hx y hy
  obtain ⟨n,hn⟩ := hs x (hull_bounded e hk hg he x hx) y hy
  have hh := FiniteDemand.FinitaryClosure.apply_mem (eval kappa e) (seeds gamma) (.inl n) [x]
    (by intro z hz; rw [List.mem_singleton.mp hz]; exact hx)
  simpa [eval,List.getD_cons_zero,hn,hull] using hh

noncomputable def nextHeight (kappa : Label.{u}) (e : Label.{u} → Nat → Label.{u})
    (gamma : Label.{u}) : Label.{u} := FiniteDemand.OrdinalHeight.height (hull kappa e gamma)

theorem nextHeight_spec {kappa : Label.{u}} (e : Label.{u} → Nat → Label.{u})
    (hk : Ordinal.omega0 < kappa) (hunc : ¬ (Set.Iio kappa).Countable)
    (he : ∀ a, a < kappa → ∀ n, e a n < kappa)
    (hs : ∀ a, a < kappa → ∀ b, b < a → ∃ n, e a n = b)
    (gamma : Label.{u}) (hg : gamma < kappa) :
    let delta := nextHeight kappa e gamma
    gamma < delta ∧ delta < kappa ∧ domain delta ∧
      BadClosed kappa delta ∧ ExtClosed relation kappa delta := by
  let H := hull kappa e gamma
  have hne : H.Nonempty := ⟨Ordinal.omega0,omega_mem kappa e gamma⟩
  have hb : ∀ x ∈ H, x < kappa := hull_bounded e hk hg he
  have hd : ∀ x ∈ H, ∀ y, y < x → y ∈ H := hull_downward e hk hg he hs
  let delta := FiniteDemand.OrdinalHeight.height H
  have hmem : ∀ x, x ∈ H ↔ x < delta := FiniteDemand.OrdinalHeight.mem_iff_lt hne hb hd
  refine ⟨(hmem gamma).mp (gamma_mem kappa e gamma),
    FiniteDemand.OrdinalHeight.height_lt hne (hull_countable kappa e gamma) hb hd hunc,
    (hmem Ordinal.omega0).mp (omega_mem kappa e gamma),?_,?_⟩
  · intro T i f a hf ha
    apply (hmem _).mp
    have hh := FiniteDemand.FinitaryClosure.apply_mem (eval kappa e) (seeds gamma)
      (.inr (.inl (T,i))) (a :: List.ofFn f) (by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact (hmem _).mpr ha
        · obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
          exact (hmem _).mpr (hf j))
    simpa only [eval,List.getD_cons_zero,List.getD_cons_succ,getD_ofFn,H,hull] using hh
  · intro A i pref hpref
    apply (hmem _).mp
    have hh := FiniteDemand.FinitaryClosure.apply_mem (eval kappa e) (seeds gamma)
      (.inr (.inr (A,i))) (List.ofFn pref) (by
        intro x hx
        obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
        exact (hmem _).mpr (hpref j))
    simpa only [eval,getD_ofFn,H,hull] using hh

theorem exists_closed_above {kappa : Label.{u}} (e : Label.{u} → Nat → Label.{u})
    (hk : Ordinal.omega0 < kappa) (hunc : ¬ (Set.Iio kappa).Countable)
    (he : ∀ a, a < kappa → ∀ n, e a n < kappa)
    (hs : ∀ a, a < kappa → ∀ b, b < a → ∃ n, e a n = b)
    (gamma : Label.{u}) (hg : gamma < kappa) :
    ∃ delta, gamma < delta ∧ delta < kappa ∧ domain delta ∧
      BadClosed kappa delta ∧ ExtClosed relation kappa delta :=
  ⟨nextHeight kappa e gamma,nextHeight_spec e hk hunc he hs gamma hg⟩

end IPD.Semantics.ClosedSupply

#print axioms IPD.Semantics.ClosedSupply.hull_countable
#print axioms IPD.Semantics.ClosedSupply.hull_downward
#print axioms IPD.Semantics.ClosedSupply.nextHeight_spec
#print axioms IPD.Semantics.ClosedSupply.exists_closed_above
