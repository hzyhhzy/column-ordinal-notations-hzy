import FiniteDemandEndpointAgreement
import FiniteDemandFinitaryClosure
import FiniteDemandOrdinalHeight

/-!
# Unbounded closed heights from the explicit enumeration hypothesis

The operations are the actual least Bad/Ext witnesses and a supplied uniform
enumerator of the ordinals below kappa. Their countable finitary hull is
downward closed and hence is an ordinal strictly below kappa, without using
regularity. This realizes the paper's auxiliary enumeration hypothesis.

Producing that enumerator in the stipulated weak theory (inside L), and
certifying the bounded recursion and closure there, remain separate tasks.
-/

namespace FiniteDemand.ClosedSupply
open OrdinalFormal.ReflectionTransport

universe u v
variable {Row : Type v} [Countable Row]

abbrev Op (Row : Type v) := Nat ⊕ ((Row × Nat) ⊕ (Shape Row × Nat))

noncomputable def eval (rowLt : Row → Row → Prop) (hw : WellFounded rowLt)
    (kappa : Label.{u}) (e : Label.{u} → Nat → Label.{u}) : Op Row → List Label.{u} → Label.{u}
  | .inl n, xs => e (xs.getD 0 0) n
  | .inr (.inl (k, i)), xs => badOp rowLt hw k i (xs.getD 0 0) (xs.getD 1 0) kappa
  | .inr (.inr (A, i)), xs => extOp (relation rowLt hw) kappa A i (fun j => xs.getD j 0)

def seeds (gamma : Label.{u}) : Nat → Label.{u}
  | 0 => Ordinal.omega0
  | 1 => gamma
  | _ + 2 => 0

noncomputable def hull (rowLt : Row → Row → Prop) (hw : WellFounded rowLt)
    (kappa : Label.{u}) (e : Label.{u} → Nat → Label.{u}) (gamma : Label.{u}) : Set Label.{u} :=
  FinitaryClosure.closure (eval rowLt hw kappa e) (seeds gamma)

theorem getD_preserves {X : Type*} (P : X → Prop) (xs : List X) (i : Nat) (z : X)
    (hz : P z) (hxs : ∀ x ∈ xs, P x) : P (xs.getD i z) := by
  induction xs generalizing i with
  | nil => simpa using hz
  | cons x xs ih =>
    cases i with
    | zero => simpa only [List.getD_cons_zero] using hxs x (by simp)
    | succ i =>
      exact ih i (fun y hy => hxs y (by simp [hy]))

theorem getD_ofFn {n : Nat} (f : Fin n → Label.{u}) (j : Fin n) :
    (List.ofFn f).getD j 0 = f j := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, j.isLt]

theorem hull_countable (rowLt : Row → Row → Prop) (hw : WellFounded rowLt)
    (kappa : Label.{u}) (e : Label.{u} → Nat → Label.{u}) (gamma : Label.{u}) :
    (hull rowLt hw kappa e gamma).Countable := FinitaryClosure.countable _ _

theorem omega_mem (rowLt : Row → Row → Prop) (hw : WellFounded rowLt)
    (kappa : Label.{u}) (e : Label.{u} → Nat → Label.{u}) (gamma : Label.{u}) :
    Ordinal.omega0 ∈ hull rowLt hw kappa e gamma :=
  FinitaryClosure.constant_mem _ (seeds gamma) 0

theorem gamma_mem (rowLt : Row → Row → Prop) (hw : WellFounded rowLt)
    (kappa : Label.{u}) (e : Label.{u} → Nat → Label.{u}) (gamma : Label.{u}) :
    gamma ∈ hull rowLt hw kappa e gamma := FinitaryClosure.constant_mem _ (seeds gamma) 1

theorem hull_bounded (rowLt : Row → Row → Prop) (hw : WellFounded rowLt)
    {kappa : Label.{u}} (e : Label.{u} → Nat → Label.{u}) {gamma : Label.{u}}
    (hk : Ordinal.omega0 < kappa) (hg : gamma < kappa)
    (he : ∀ a, a < kappa → ∀ n, e a n < kappa) :
    ∀ x ∈ hull rowLt hw kappa e gamma, x < kappa := by
  have h0 : (0 : Label.{u}) < kappa := lt_trans Ordinal.omega0_pos hk
  apply FinitaryClosure.invariant
  · intro n
    cases n with
    | zero => exact hk
    | succ n =>
      cases n with
      | zero => exact hg
      | succ n => exact h0
  · intro o xs hxs
    rcases o with n | (⟨k, i⟩ | ⟨A, i⟩)
    · exact he _ (getD_preserves (· < kappa) xs 0 0 h0 hxs) n
    · exact badOp_lt rowLt hw k i _ _ kappa h0
    · exact extOp_lt (relation rowLt hw) kappa A i _ h0

theorem hull_downward (rowLt : Row → Row → Prop) (hw : WellFounded rowLt)
    {kappa : Label.{u}} (e : Label.{u} → Nat → Label.{u}) {gamma : Label.{u}}
    (hk : Ordinal.omega0 < kappa) (hg : gamma < kappa)
    (he : ∀ a, a < kappa → ∀ n, e a n < kappa)
    (hs : ∀ a, a < kappa → ∀ b, b < a → ∃ n, e a n = b) :
    ∀ x ∈ hull rowLt hw kappa e gamma, ∀ y, y < x → y ∈ hull rowLt hw kappa e gamma := by
  intro x hx y hy
  obtain ⟨n, hn⟩ := hs x (hull_bounded rowLt hw e hk hg he x hx) y hy
  have hh := FinitaryClosure.apply_mem (eval rowLt hw kappa e) (seeds gamma) (.inl n) [x]
    (by intro z hz; rw [List.mem_singleton.mp hz]; exact hx)
  simpa [eval, List.getD_cons_zero, hn, hull] using hh

noncomputable def nextHeight (rowLt : Row → Row → Prop) (hw : WellFounded rowLt)
    (kappa : Label.{u}) (e : Label.{u} → Nat → Label.{u}) (gamma : Label.{u}) : Label.{u} :=
  OrdinalHeight.height (hull rowLt hw kappa e gamma)

/-- A genuinely constructed closed height above every gamma < kappa. The only
ambient input beyond uncountability is an explicit uniform enumeration. -/
theorem nextHeight_spec (rowLt : Row → Row → Prop) (hw : WellFounded rowLt)
    {kappa : Label.{u}} (e : Label.{u} → Nat → Label.{u})
    (hk : Ordinal.omega0 < kappa) (hunc : ¬ (Set.Iio kappa).Countable)
    (he : ∀ a, a < kappa → ∀ n, e a n < kappa)
    (hs : ∀ a, a < kappa → ∀ b, b < a → ∃ n, e a n = b)
    (gamma : Label.{u}) (hg : gamma < kappa) :
    let delta := nextHeight rowLt hw kappa e gamma
    gamma < delta ∧ delta < kappa ∧ domain delta ∧
      BadClosed rowLt hw kappa delta ∧ ExtClosed (relation rowLt hw) kappa delta := by
  let H := hull rowLt hw kappa e gamma
  have hne : H.Nonempty := ⟨Ordinal.omega0, omega_mem rowLt hw kappa e gamma⟩
  have hb : ∀ x ∈ H, x < kappa := hull_bounded rowLt hw e hk hg he
  have hd : ∀ x ∈ H, ∀ y, y < x → y ∈ H := hull_downward rowLt hw e hk hg he hs
  let delta := OrdinalHeight.height H
  have hmem : ∀ x, x ∈ H ↔ x < delta := OrdinalHeight.mem_iff_lt hne hb hd
  refine ⟨(hmem gamma).mp (gamma_mem rowLt hw kappa e gamma),
    OrdinalHeight.height_lt hne (hull_countable rowLt hw kappa e gamma) hb hd hunc,
    (hmem Ordinal.omega0).mp (omega_mem rowLt hw kappa e gamma), ?_, ?_⟩
  · intro k i theta a ht ha
    apply (hmem _).mp
    have hh := FinitaryClosure.apply_mem (eval rowLt hw kappa e) (seeds gamma)
      (.inr (.inl (k, i))) [theta, a] (by
        intro x hx
        rcases List.mem_cons.mp hx with hxt | hx
        · rw [hxt]
          exact (hmem theta).mpr ht
        · have hx := List.mem_singleton.mp hx
          subst x
          exact (hmem a).mpr ha)
    simpa [eval, List.getD_cons_zero, List.getD_cons_succ, H, hull] using hh
  · intro A i pref hpref
    apply (hmem _).mp
    have hh := FinitaryClosure.apply_mem (eval rowLt hw kappa e) (seeds gamma)
      (.inr (.inr (A, i))) (List.ofFn pref) (by
        intro x hx
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
        exact (hmem _).mpr (hpref j))
    simpa only [eval, getD_ofFn, H, hull] using hh

theorem exists_closed_above (rowLt : Row → Row → Prop) (hw : WellFounded rowLt)
    {kappa : Label.{u}} (e : Label.{u} → Nat → Label.{u})
    (hk : Ordinal.omega0 < kappa) (hunc : ¬ (Set.Iio kappa).Countable)
    (he : ∀ a, a < kappa → ∀ n, e a n < kappa)
    (hs : ∀ a, a < kappa → ∀ b, b < a → ∃ n, e a n = b)
    (gamma : Label.{u}) (hg : gamma < kappa) :
    ∃ delta, gamma < delta ∧ delta < kappa ∧ domain delta ∧
      BadClosed rowLt hw kappa delta ∧ ExtClosed (relation rowLt hw) kappa delta :=
  ⟨nextHeight rowLt hw kappa e gamma, nextHeight_spec rowLt hw e hk hunc he hs gamma hg⟩

end FiniteDemand.ClosedSupply

#print axioms FiniteDemand.ClosedSupply.hull_bounded
#print axioms FiniteDemand.ClosedSupply.hull_downward
#print axioms FiniteDemand.ClosedSupply.nextHeight_spec
#print axioms FiniteDemand.ClosedSupply.exists_closed_above
