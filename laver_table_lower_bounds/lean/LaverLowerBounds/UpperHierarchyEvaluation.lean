import LaverLowerBounds.DiagonalFGH

set_option autoImplicit false

namespace LaverLowerBounds.ParentBMS

inductive RelIter (R : Nat → Nat → Prop) : Nat → Nat → Nat → Prop
  | zero (x) : RelIter R 0 x x
  | step {n x y z} : RelIter R n x y → R y z → RelIter R (n + 1) x z

def LambdaEval (x y : Nat) : Prop := FastEval (seed (x + 1)) x y

def FiniteLevelEval : Nat → Nat → Nat → Prop
  | 0 => LambdaEval
  | n + 1 => fun x y => RelIter (FiniteLevelEval n) (x + 1) x y

def OmegaEval (x y : Nat) : Prop := FiniteLevelEval (x + 1) x y
def OmegaSuccessorEval (x y : Nat) : Prop := RelIter OmegaEval (x + 1) x y

theorem RelIter.unique {R : Nat → Nat → Prop}
    (hR : ∀ x y z, R x y → R x z → y = z) {n x y z : Nat}
    (hy : RelIter R n x y) (hz : RelIter R n x z) : y = z := by
  induction hy generalizing z with
  | zero x => cases hz; rfl
  | step _ hlast ih =>
      cases hz with
      | step hfirst hlast' =>
          have he := ih hfirst
          subst he
          exact hR _ _ _ hlast hlast'

theorem finiteLevelEval_unique (n : Nat) :
    ∀ x y z, FiniteLevelEval n x y → FiniteLevelEval n x z → y = z := by
  induction n with
  | zero => exact fun _ _ _ hy hz => FastEval.unique hy hz
  | succ n ih => exact fun _ _ _ hy hz => RelIter.unique ih hy hz

theorem omegaSuccessorEval_unique {x y z : Nat} (hy : OmegaSuccessorEval x y) (hz : OmegaSuccessorEval x z) : y = z :=
  RelIter.unique (fun a b c => finiteLevelEval_unique (a + 1) a b c) hy hz

theorem relIter_realized {R : Nat → Nat → Prop} {g : Nat → Nat} {bound : Nat}
    (hg : Grows g) (hR : ∀ x, 2 ≤ x → g x ≤ bound → R x (g x))
    (n x : Nat) (hx : 2 ≤ x) (hb : iter g n x ≤ bound) :
    RelIter R n x (iter g n x) := by
  induction n with
  | zero => exact .zero x
  | succ n ih =>
      have hinput := iter_ge g hg n x hx
      have hgrow := hg (iter g n x) (by omega)
      simp only [iter_succ] at hb ⊢
      exact .step (ih (by omega)) (hR _ (by omega) hb)

theorem finiteLevel_realized {g : Nat → Nat} {bound : Nat} (hg : Grows g)
    (hbase : ∀ x, 2 ≤ x → x ≤ bound → LambdaEval x (g x)) (n : Nat) :
    ∀ x, 2 ≤ x → level g n x ≤ bound → FiniteLevelEval n x (level g n x) := by
  induction n with
  | zero =>
      intro x hx hb
      have hh := hg x hx
      exact hbase x hx (by change g x ≤ bound at hb; omega)
  | succ n ih =>
      intro x hx hb
      exact relIter_realized (level_grows g hg n) ih (x + 1) x hx hb

/-- Only oracle values below the FINAL output are required. Thus an actual
finite triple budget certifies every base-level FGH call in this evaluation. -/
theorem omegaSuccessor_realized {g : Nat → Nat} {bound x : Nat} (hg : Grows g)
    (hbase : ∀ a, 2 ≤ a → a ≤ bound → LambdaEval a (g a))
    (hx : 2 ≤ x) (hb : omegaSuccessor g x ≤ bound) :
    OmegaSuccessorEval x (omegaSuccessor g x) := by
  apply relIter_realized (diagonal_grows g hg) (n := x + 1) (x := x) (bound := bound)
  · intro a ha hb
    exact finiteLevel_realized hg hbase (a + 1) a ha hb
  · exact hx
  · exact hb

#print axioms omegaSuccessorEval_unique
#print axioms omegaSuccessor_realized

end LaverLowerBounds.ParentBMS
