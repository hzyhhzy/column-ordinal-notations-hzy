import Std

/-!
Guarded algebraic deductions used at the finite-table entrance.

`CappedAlgebra` is an INTERFACE. FiniteCapped.lean constructs it from the ordinary
finite defining tables. Introducing this structure alone would not prove that
the concrete tables satisfy its laws.

The cap is a saturation value. Strict monotonicity can only be used when the
image of the upper argument lies strictly below the cap.
-/

set_option autoImplicit false

namespace LaverLowerBounds

structure CappedAlgebra (A : Type) where
  cap : Nat
  app : A → A → A
  comp : A → A → A
  act : A → Nat → Nat
  act_le : ∀ a x, act a x ≤ cap
  le_act : ∀ a x, x ≤ cap → x ≤ act a x
  strict_below_cap : ∀ a x y, x < y → act a y < cap → act a x < act a y
  act_app : ∀ a b x, act (app a b) (act a x) = act a (act b x)
  act_comp : ∀ a b x, act (comp a b) x = act a (act b x)
  app_comp : ∀ e a b, app e (comp a b) = comp (app e a) (app e b)
  congruent : Nat → A → A → Prop
  transport : ∀ {r a b}, congruent r a b → ∀ e,
    congruent (act e r) (app e a) (app e b)
  read_below : ∀ {r a b x}, congruent r a b → act a x < r → act a x = act b x

namespace CappedAlgebra

variable {A : Type} (alg : CappedAlgebra A)

theorem guarded_double_action (j j3 e : A)
    (hcong : alg.congruent 3 j3 (alg.comp j j)) (hj3 : alg.act j3 1 = 3)
    {β : Nat} (he : alg.act e 3 < alg.cap) (hβ : β < alg.act e 1) :
    alg.act (alg.app e j) (alg.act (alg.app e j) β) < alg.act e 3 := by
  have htransport := alg.transport hcong e
  rw [alg.app_comp] at htransport
  have hend : alg.act (alg.app e j3) (alg.act e 1) = alg.act e 3 := by
    rw [alg.act_app, hj3]
  have hlt : alg.act (alg.app e j3) β < alg.act e 3 := by
    have := alg.strict_below_cap (alg.app e j3) β (alg.act e 1) hβ
      (by simpa only [hend] using he)
    simpa only [hend] using this
  have hread := alg.read_below htransport hlt
  rw [alg.act_comp] at hread
  exact hread ▸ hlt

/-- Only the low point values needed for the first finite endpoint bound.
These values are to be certified from A_9 and projection compatibility. -/
structure LowData (j : Nat → A) : Prop where
  next : ∀ n, j (n + 1) = alg.app (j n) (j 1)
  j11 : alg.act (j 1) 1 = 2
  j12 : alg.act (j 1) 2 = 4
  j13 : alg.act (j 1) 3 = 8
  j22 : alg.act (j 2) 2 = 4
  j31 : alg.act (j 3) 1 = 3
  j32 : alg.act (j 3) 2 = 4
  j42 : alg.act (j 4) 2 = 3
  j51 : alg.act (j 5) 1 = 3
  j61 : alg.act (j 6) 1 = 3
  j71 : alg.act (j 7) 1 = 4
  j83 : alg.act (j 8) 3 = 4
  square : alg.congruent 3 (j 3) (alg.comp (j 1) (j 1))
  mu_lower : 9 ≤ alg.act (j 7) 2

theorem next_action (j : Nat → A) (low : alg.LowData j) (n x : Nat) :
    alg.act (j (n + 1)) (alg.act (j n) x) = alg.act (j n) (alg.act (j 1) x) := by
  rw [low.next n, alg.act_app]

/-- The new finite argument replacing the old left-limit argument.
No image at the saturation point is ever treated as an exact critical point. -/
theorem j9_four_below (j : Nat → A) (low : alg.LowData j)
    (hs : alg.act (j 1) 4 < alg.cap) :
    alg.act (j 9) 4 < alg.act (j 1) 4 := by
  have h24 : alg.act (j 2) 4 = alg.act (j 1) 4 := by
    simpa only [low.j12] using alg.next_action j low 1 2
  have h34 : alg.act (j 3) 4 = alg.act (j 1) 4 := by
    simpa only [low.j22, low.j12, h24] using alg.next_action j low 2 2
  have h44 : alg.act (j 4) 4 = alg.act (j 1) 4 := by
    simpa only [low.j32, low.j12, h34] using alg.next_action j low 3 2
  have h53 : alg.act (j 5) 3 = alg.act (j 1) 4 := by
    simpa only [low.j42, low.j12, h44] using alg.next_action j low 4 2
  have h63 : alg.act (j 6) 3 = alg.act (j 5) 2 := by
    simpa only [low.j51, low.j11] using alg.next_action j low 5 1
  have h52 : alg.act (j 5) 2 < alg.act (j 1) 4 := by
    have := alg.strict_below_cap (j 5) 2 3 (by decide) (by omega)
    omega
  have h77 : alg.act (j 7) (alg.act (j 7) 2) < alg.act (j 1) 4 := by
    have h := alg.guarded_double_action (j 1) (j 3) (j 6) low.square low.j31
      (by omega : alg.act (j 6) 3 < alg.cap)
      (by rw [low.j61]; decide : 2 < alg.act (j 6) 1)
    rw [← low.next 6] at h
    change alg.act (j 7) (alg.act (j 7) 2) < alg.act (j 6) 3 at h
    omega
  have h74 : alg.act (j 7) 4 < alg.act (j 7) (alg.act (j 7) 2) :=
    alg.strict_below_cap (j 7) 4 (alg.act (j 7) 2) (by have := low.mu_lower; omega)
      (by omega)
  have h8mu : alg.act (j 8) (alg.act (j 7) 2) = alg.act (j 7) 4 := by
    simpa only [low.j12] using alg.next_action j low 7 2
  have h94 : alg.act (j 9) 4 = alg.act (j 8) 8 := by
    simpa only [low.j83, low.j13] using alg.next_action j low 8 3
  have h88 := alg.strict_below_cap (j 8) 8 (alg.act (j 7) 2)
    (by have := low.mu_lower; omega) (by omega)
  omega

#print axioms guarded_double_action
#print axioms j9_four_below

end CappedAlgebra
end LaverLowerBounds
