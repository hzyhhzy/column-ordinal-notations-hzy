import ARDCore

/-! Four-coordinate label transport for ARD.  Unlike the frozen-row transport,
the row coordinate is evaluated through the reflected or spliced labeling. -/

namespace OrdinalFormal.ARD

set_option autoImplicit false
set_option maxHeartbeats 600000
universe u
variable {Label : Type u}

theorem holds_take
    (lt : Label → Label → Prop) (D : Label → Prop)
    (R : Label → Label → Label → Label → Prop)
    {g : Graph} {f : Nat → Label} (hF : Holds lt D R g f) (n : Nat) :
    Holds lt D R (g.take n) f := by
  constructor
  · intro i hi
    exact hF.domain i (by simp only [List.length_take] at hi; omega)
  · intro i j hij hj
    exact hF.ordered i j hij (by simp only [List.length_take] at hj; omega)
  · intro j a ha
    rw [List.getElem?_take] at ha
    split at ha
    · exact hF.relations j a ha
    · simp at ha

theorem weaken_relation
    (lt : Label → Label → Prop) (R : Label → Label → Label → Label → Prop)
    (hWeak : ∀ {k small large p c}, lt small large → R k large p c → R k small p c)
    (f : Nat → Label) (N j : Nat)
    (hOrdered : ∀ i k, i < k → k < N → lt (f i) (f k))
    (a s : Entry) (hrow : a.row = s.row) (hparent : a.parent = s.parent)
    (hroot : a.root ≤ s.root) (hs : s.root < N)
    (hR : R (f s.row) (f s.root) (f s.parent) (f j)) :
    R (f a.row) (f a.root) (f a.parent) (f j) := by
  rw [hrow, hparent]
  by_cases heq : a.root = s.root
  · rwa [heq]
  · exact hWeak (hOrdered _ _ (by omega) hs) hR

/-- All four references move. In particular no old row value is frozen. -/
theorem splice_four
    (R : Label → Label → Label → Label → Prop)
    {n c k q p j : Nat} (f reflected : Nat → Label)
    (hc : c ≤ n) (hk : k < n) (hq : q < n) (hp : p < n) (hj : j < n)
    (hFixed : ∀ i, i < c → reflected i = f i)
    (hR : R (f k) (f q) (f p) (f j)) :
    let next := ReflectionTransport.spliceLabel n c f reflected
    R (next (ReflectionTransport.moveColumn n c k))
      (next (ReflectionTransport.moveColumn n c q))
      (next (ReflectionTransport.moveColumn n c p))
      (next (ReflectionTransport.moveColumn n c j)) := by
  dsimp only
  rw [ReflectionTransport.spliceLabel_move f reflected hc hk hFixed,
    ReflectionTransport.spliceLabel_move f reflected hc hq hFixed,
    ReflectionTransport.spliceLabel_move f reflected hc hp hFixed,
    ReflectionTransport.spliceLabel_move f reflected hc hj hFixed]
  exact hR

/-- A seam reads every left coordinate from the reflected labeling. -/
theorem splice_seam
    (R : Label → Label → Label → Label → Prop)
    {n c : Nat} (f reflected : Nat → Label) (a : Entry)
    (ha : NeedValid n a)
    (hR : R (reflected a.row) (reflected a.root) (reflected a.parent) (f c)) :
    let next := ReflectionTransport.spliceLabel n c f reflected
    R (next a.row) (next a.root) (next a.parent) (next n) := by
  dsimp only
  rw [ReflectionTransport.spliceLabel_old f reflected ha.1,
    ReflectionTransport.spliceLabel_old f reflected (by have := ha.2; omega),
    ReflectionTransport.spliceLabel_old f reflected ha.2.2,
    ReflectionTransport.spliceLabel_first]
  exact hR

#print axioms holds_take
#print axioms weaken_relation
#print axioms splice_four
#print axioms splice_seam

end OrdinalFormal.ARD
