import LaverLowerBounds.HigherConstants

set_option autoImplicit false

namespace LaverLowerBounds.FiniteTable.LowerEndpoint

/-- A finite application word. Numerals denote the usual left iterates of
the generator; `app` is table multiplication, not ordinary composition. -/
inductive Word where
  | numeral : Nat → Word
  | app : Word → Word → Word
  deriving DecidableEq, Repr

def Word.eval (family : BinaryFamily) (m : Nat) : Word → Nat
  | .numeral n => n % 2 ^ m
  | .app a b => (family m).mul (a.eval family m) (b.eval family m)

theorem Word.eval_lt (family : BinaryFamily) (m : Nat) (w : Word) :
    w.eval family m < 2 ^ m := by
  cases w with
  | numeral n => exact Nat.mod_lt _ (Nat.two_pow_pos m)
  | app a b => exact (family m).mul_lt _ _

/-- Evaluation of an entire word commutes with finite-table projection. -/
theorem Word.projection (family : BinaryFamily) {m n : Nat} (hmn : m ≤ n)
    (w : Word) : w.eval family n % 2 ^ m = w.eval family m := by
  induction w with
  | numeral a =>
    exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hmn)
  | app a b ia ib =>
    change (family n).mul _ _ % 2 ^ m = (family m).mul _ _
    rw [(family n).projection (family m) (Nat.pow_dvd_pow 2 hmn)]
    rw [← (family m).mul_mod_left, ← (family m).mul_mod_right, ia, ib]

def Word.index (family : BinaryFamily) (m : Nat) (w : Word) (x : Nat) : Nat :=
  act family m (w.eval family m) x

theorem Word.index_le (family : BinaryFamily) (m : Nat) (w : Word) (x : Nat) :
    w.index family m x ≤ m := act_le family m _ x

theorem Word.index_unsaturated_iff (family : BinaryFamily) (m : Nat) (w : Word) (x : Nat) :
    w.index family m x < m ↔ (family m).mul (w.eval family m) (2 ^ x) ≠ 0 := by
  have hl := w.index_le family m x
  have he := le_act_iff family m (w.eval family m) x m (Nat.le_refl _)
  change act family m (w.eval family m) x < m ↔ _
  constructor
  · intro hu hz
    have := he.mpr hz
    omega
  · intro hz
    by_cases hu : act family m (w.eval family m) x < m
    · exact hu
    · exact False.elim (hz (he.mp (by omega)))

/-- The value, once non-saturated, is stable in all larger finite tables.
The actor code itself need not be constant across the tables. -/
theorem Word.index_stable (family : BinaryFamily) {m n : Nat} (hmn : m ≤ n)
    (w : Word) (x : Nat) (hu : w.index family m x < m) :
    w.index family n x = w.index family m x := by
  let a := (family n).mul (w.eval family n) (2 ^ x)
  let b := (family m).mul (w.eval family m) (2 ^ x)
  have hp : a % 2 ^ m = b := by
    dsimp [a, b]
    rw [(family n).projection (family m) (Nat.pow_dvd_pow 2 hmn)]
    rw [← (family m).mul_mod_left, w.projection family hmn]
  have hs : signature m a = signature m b := signature_mod_eq (by
    rw [hp, Nat.mod_eq_of_lt ((family m).mul_lt _ _)])
  have ha : signature m a < m := by
    rw [hs]
    exact hu
  exact (signature_lift hmn ha).trans hs

def Word.HasIndex (family : BinaryFamily) (w : Word) (x r : Nat) : Prop :=
  ∃ m, w.index family m x = r ∧ r < m

theorem Word.hasIndex_iff_eventually (family : BinaryFamily) (w : Word) (x r : Nat) :
    w.HasIndex family x r ↔ ∃ N, ∀ n, N ≤ n → w.index family n x = r := by
  constructor
  · rintro ⟨m, he, hm⟩
    exact ⟨m, fun n hmn => (w.index_stable family hmn x (by omega)).trans he⟩
  · rintro ⟨N, hN⟩
    exact ⟨max N (r + 1), hN _ (Nat.le_max_left _ _), by
      have := Nat.le_max_right N (r + 1)
      omega⟩

theorem Word.HasIndex.unique {family : BinaryFamily} {w : Word} {x r s : Nat}
    (hr : w.HasIndex family x r) (hs : w.HasIndex family x s) : r = s := by
  obtain ⟨M, hM⟩ := (w.hasIndex_iff_eventually family x r).mp hr
  obtain ⟨N, hN⟩ := (w.hasIndex_iff_eventually family x s).mp hs
  exact (hM (max M N) (Nat.le_max_left _ _)).symm.trans
    (hN (max M N) (Nat.le_max_right _ _))

/-- The smaller endpoint in the paper: ((J11(J3))(J7))(gamma3). -/
def etaWord : Word := .app (.app (.numeral 11) (.numeral 3)) (.numeral 7)

def etaIndex (family : BinaryFamily) (m : Nat) : Nat := etaWord.index family m 3

theorem etaIndex_eq (family : BinaryFamily) (m : Nat) :
    etaIndex family m =
      act family m ((family m).mul ((family m).mul 11 3) 7) 3 := by
  simp only [etaIndex, Word.index, etaWord, Word.eval,
    (family m).mul_mod_left, (family m).mul_mod_right]

#print axioms Word.projection
#print axioms Word.index_stable
#print axioms Word.hasIndex_iff_eventually
#print axioms Word.HasIndex.unique
#print axioms etaIndex_eq

end LaverLowerBounds.FiniteTable.LowerEndpoint
