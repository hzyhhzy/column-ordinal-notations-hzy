import BTnSSBMS.Syntax
import Init.Data.List.Lex
import Init.Data.List.Sublist

/-!
The finite-word last-hole argument, independently of the notation rules.

An expanding context delays every possible input difference by a fixed,
positive number of letters. Its finite iterates from the empty word form
nested prefixes. The forward comparison has an explicit finite horizon;
no well-foundedness of word lexicographic order is used.

To apply this to the actual BMS expansion one must still identify the
actual copies with these iterates and prove the stated delay property.
-/
namespace BTnSSBMS.LastHole

structure Context (α : Type) where
  apply : List α → List α
  delay : Nat
  positive : 0 < delay
  length_apply : ∀ x, (apply x).length = delay + x.length
  causal : ∀ x y k, x.take k = y.take k →
    (apply x).take (delay + k) = (apply y).take (delay + k)

def Context.iterate (c : Context α) : Nat → List α
  | 0 => []
  | n + 1 => c.apply (c.iterate n)

/-- A length-preserving, prefix-local transformation gives exactly the
paper's context `P ++ τ(x)`. No ordering property is hidden in this constructor. -/
def Context.ofTail (p : List α) (positive : 0 < p.length)
    (τ : List α → List α) (length_τ : ∀ x, (τ x).length = x.length)
    (causal_τ : ∀ x y k, x.take k = y.take k → (τ x).take k = (τ y).take k) :
    Context α where
  apply x := p ++ τ x
  delay := p.length
  positive := positive
  length_apply x := by simp [length_τ]
  causal x y k h := by
    simp only [List.take_length_add_append]
    rw [causal_τ x y k h]

theorem Context.ofTail_apply (p : List α) (positive : 0 < p.length)
    (τ : List α → List α) (length_τ : ∀ x, (τ x).length = x.length)
    (causal_τ : ∀ x y k, x.take k = y.take k → (τ x).take k = (τ y).take k)
    (x : List α) : (Context.ofTail p positive τ length_τ causal_τ).apply x = p ++ τ x := rfl

theorem Context.prefix_mono (c : Context α) {x y : List α}
    (h : x <+: y) : c.apply x <+: c.apply y := by
  have ht : x.take x.length = y.take x.length := by
    obtain ⟨z, rfl⟩ := h
    simp
  have hc := c.causal x y x.length ht
  rw [← c.length_apply x, List.take_length] at hc
  rw [hc]
  exact List.take_prefix _ _

theorem Context.iterate_prefix (c : Context α) (n : Nat) :
    c.iterate n <+: c.iterate (n + 1) := by
  induction n with
  | zero => exact List.nil_prefix
  | succ n ih => exact c.prefix_mono ih

theorem Context.iterate_length (c : Context α) (n : Nat) :
    (c.iterate n).length = n * c.delay := by
  induction n with
  | zero => simp [Context.iterate]
  | succ n ih =>
    rw [Context.iterate, c.length_apply, ih, Nat.succ_mul, Nat.add_comm]

theorem Context.iterate_length_ge (c : Context α) (n : Nat) :
    n ≤ (c.iterate n).length := by
  rw [c.iterate_length]
  exact Nat.le_mul_of_pos_right n c.positive

private theorem take_eq_of_agree {x y : List α} {k : Nat}
    (hx : k ≤ x.length) (hy : k ≤ y.length)
    (h : ∀ i (hi : i < k), x[i]'(by omega) = y[i]'(by omega)) :
    x.take k = y.take k := by
  apply List.ext_getElem
  · simp only [List.length_take, Nat.min_eq_left hx, Nat.min_eq_left hy]
  · intro i hi hj
    simp only [List.getElem_take]
    exact h i (by simp only [List.length_take] at hi; omega)

private theorem agree_of_take_eq {x y : List α} {k i : Nat}
    (h : x.take k = y.take k) (hi : i < k)
    (hx : i < x.length) (hy : i < y.length) : x[i] = y[i] := by
  have h' := congrArg (fun z : List α => z[i]?) h
  simpa only [List.getElem?_take_of_lt hi, List.getElem?_eq_getElem hx,
    List.getElem?_eq_getElem hy, Option.some.injEq] using h'

/-- One sufficiently long iterate already decides the forward last-hole
implication. In particular `n = length y + 1` always suffices. -/
theorem Context.forward_of_long_iterate [LT α] (c : Context α)
    (y : List α) (n : Nat) (long : y.length < (c.iterate n).length)
    (below : c.iterate n < y) : c.apply y < y := by
  rcases List.lt_iff_exists.mp below with hpre | ⟨q, hqW, hqY, common, smaller⟩
  · omega
  · have hqF : q < (c.apply y).length := by rw [c.length_apply]; omega
    have shared := take_eq_of_agree (Nat.le_of_lt hqW) (Nat.le_of_lt hqY) common
    have delayed := c.causal (c.iterate n) y q shared
    have nextPrefix := c.iterate_prefix n
    have nextLength := c.length_apply (c.iterate n)
    have agrees : ∀ i (hi : i ≤ q),
        (c.apply y)[i]'(by omega) = (c.iterate n)[i]'(by omega) := by
      intro i hi
      have atNext := agree_of_take_eq (i := i) delayed (by have := c.positive; omega)
        (by omega) (by rw [c.length_apply]; omega)
      have atPrefix := nextPrefix.getElem (by omega : i < (c.iterate n).length)
      exact atNext.symm.trans atPrefix.symm
    apply List.lt_iff_exists.mpr
    right
    refine ⟨q, hqF, hqY, ?_, ?_⟩
    · intro i hi
      exact (agrees i (Nat.le_of_lt hi)).trans (common i hi)
    · rw [agrees q (Nat.le_refl q)]
      exact smaller

theorem Context.forward_at_length [LT α] (c : Context α) (y : List α)
    (below : c.iterate (y.length + 1) < y) : c.apply y < y :=
  c.forward_of_long_iterate y (y.length + 1)
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (c.iterate_length_ge _)) below

/-- Quantitative coverage of the finite target, before checking that these
iterates really are copies of the frozen notation's fundamental sequence. -/
theorem Context.cover_at_length [LT α] (c : Context α) (y : List α)
    (notBelow : ¬ c.apply y < y) : ¬ c.iterate (y.length + 1) < y :=
  fun h => notBelow (c.forward_at_length y h)

theorem Context.all_below_iff [LT α]
    [Trans (· < · : α → α → Prop) (· < ·) (· < ·)]
    (c : Context α) (increasing : ∀ x y, x < y → c.apply x < c.apply y)
    (y : List α) (nonempty : y ≠ []) :
    (∀ n, c.iterate n < y) ↔ c.apply y < y := by
  constructor
  · intro all
    exact c.forward_at_length y (all _)
  · intro below n
    induction n with
    | zero =>
      cases y with
      | nil => exact False.elim (nonempty rfl)
      | cons a y => exact List.Lex.nil
    | succ n ih =>
      exact List.lt_trans (increasing _ _ ih) below

end BTnSSBMS.LastHole
