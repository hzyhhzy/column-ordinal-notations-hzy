import Std

/-!
Elementary iteration lemmas. No monotonicity in the input is assumed.
The only growth property used is f(x) > x on the indicated tail of Nat.
-/

set_option autoImplicit false

namespace LaverLowerBounds

def iter (f : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | n + 1, x => f (iter f n x)

@[simp] theorem iter_zero (f : Nat → Nat) (x : Nat) : iter f 0 x = x := rfl

@[simp] theorem iter_succ (f : Nat → Nat) (n x : Nat) :
    iter f (n + 1) x = f (iter f n x) := rfl

def Grows (f : Nat → Nat) : Prop := ∀ x, 2 ≤ x → x < f x

theorem iter_ge (f : Nat → Nat) (hf : Grows f) (n x : Nat) (hx : 2 ≤ x) :
    x ≤ iter f n x := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
      have hg := hf (iter f n x) (by omega)
      simp only [iter_succ]
      omega

theorem iter_steps_mono (f : Nat → Nat) (hf : Grows f)
    (x : Nat) (hx : 2 ≤ x) {a b : Nat} (hab : a ≤ b) :
    iter f a x ≤ iter f b x := by
  induction b with
  | zero =>
      have : a = 0 := by omega
      subst a
      exact Nat.le_refl _
  | succ b ih =>
      by_cases h : a ≤ b
      · have h₁ := ih h
        have h₂ := hf (iter f b x) (Nat.le_trans hx (iter_ge f hf b x hx))
        simp only [iter_succ]
        omega
      · have : a = b + 1 := by omega
        subst a
        exact Nat.le_refl _

theorem iter_gt (f : Nat → Nat) (hf : Grows f)
    (n x : Nat) (hn : 1 ≤ n) (hx : 2 ≤ x) : x < iter f n x := by
  have h₁ : iter f 1 x ≤ iter f n x := iter_steps_mono f hf x hx hn
  have h₂ := hf x hx
  simpa only [iter_succ, iter_zero] using Nat.lt_of_lt_of_le h₂ h₁

def buffer (x : Nat) : Nat := 4 * (x + 1)

theorem buffer_mono {x y : Nat} (h : x ≤ y) : buffer x ≤ buffer y := by
  unfold buffer
  omega

theorem le_buffer (x : Nat) : x ≤ buffer x := by
  unfold buffer
  omega

/-- A one-step simulation preserves the same buffer at every call. -/
def Simulates (f g : Nat → Nat) : Prop :=
  ∀ x h, 2 ≤ x → buffer x ≤ h → buffer (g x) ≤ f h

theorem iter_simulates {f g : Nat → Nat} (hg : Grows g)
    (hs : Simulates f g) (n x h : Nat) (hx : 2 ≤ x) (hh : buffer x ≤ h) :
    buffer (iter g n x) ≤ iter f n h := by
  induction n with
  | zero => exact hh
  | succ n ih =>
      exact hs (iter g n x) (iter f n h)
        (Nat.le_trans hx (iter_ge g hg n x hx)) ih

/-- Extra calls are safe along the concrete orbit; f need not be monotone. -/
theorem iter_simulates_of_le {f g : Nat → Nat} (hg : Grows g)
    (hs : Simulates f g) {a b x h : Nat}
    (hab : a ≤ b) (hx : 2 ≤ x) (hh : buffer x ≤ h) :
    buffer (iter g a x) ≤ iter f b h := by
  exact Nat.le_trans (buffer_mono (iter_steps_mono g hg x hx hab))
    (iter_simulates hg hs b x h hx hh)

def level (g : Nat → Nat) : Nat → Nat → Nat
  | 0 => g
  | n + 1 => fun x => iter (level g n) (x + 1) x

theorem level_grows (g : Nat → Nat) (hg : Grows g) (n : Nat) :
    Grows (level g n) := by
  induction n with
  | zero => exact hg
  | succ n ih =>
      intro x hx
      exact iter_gt (level g n) ih (x + 1) x (by omega) hx

theorem level_le_succ (g : Nat → Nat) (hg : Grows g) (n x : Nat)
    (hx : 2 ≤ x) : level g n x ≤ level g (n + 1) x := by
  exact iter_steps_mono (level g n) (level_grows g hg n) x hx
    (show 1 ≤ x + 1 by omega)

theorem level_mono (g : Nat → Nat) (hg : Grows g) (x : Nat)
    (hx : 2 ≤ x) {a b : Nat} (hab : a ≤ b) : level g a x ≤ level g b x := by
  induction b with
  | zero =>
      have : a = 0 := by omega
      subst a
      exact Nat.le_refl _
  | succ b ih =>
      by_cases h : a ≤ b
      · exact Nat.le_trans (ih h) (level_le_succ g hg b x hx)
      · have : a = b + 1 := by omega
        subst a
        exact Nat.le_refl _

/-- If g = F_Lambda, this is F_(Lambda+omega), with [x] = Lambda+(x+1). -/
def diagonal (g : Nat → Nat) (x : Nat) : Nat := level g (x + 1) x

theorem diagonal_grows (g : Nat → Nat) (hg : Grows g) :
    Grows (diagonal g) := fun x hx => level_grows g hg (x + 1) x hx

/-- If g = F_Lambda, this is exactly F_(Lambda+omega+1). -/
def omegaSuccessor (g : Nat → Nat) (x : Nat) : Nat :=
  iter (diagonal g) (x + 1) x

theorem omegaSuccessor_grows (g : Nat → Nat) (hg : Grows g) :
    Grows (omegaSuccessor g) := by
  intro x hx
  exact iter_gt (diagonal g) (diagonal_grows g hg) (x + 1) x (by omega) hx

#print axioms iter_simulates_of_le
#print axioms level_mono
#print axioms omegaSuccessor_grows

end LaverLowerBounds
