import ARD2Core

/-! Four-coordinate label transport for ARD2.  Unlike the frozen-row transport,
the row coordinate is evaluated through the reflected or spliced labeling. -/

namespace OrdinalFormal.ARD2

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

@[simp] theorem atEnd_before (n : Nat) (f : Nat → Label) (beta : Label) {i : Nat}
    (hi : i < n) : atEnd n f beta i = f i := by simp [atEnd, hi]

@[simp] theorem atEnd_self (n : Nat) (f : Nat → Label) (beta : Label) :
    atEnd n f beta n = beta := by simp [atEnd]

theorem atEnd_selfValue (n : Nat) (f : Nat → Label) {i : Nat} (hi : i ≤ n) :
    atEnd n f (f n) i = f i := by
  by_cases h : i < n
  · exact atEnd_before n f (f n) h
  · have he : i = n := by omega
    simp [he]

theorem atEnd_strict (lt : Label → Label → Prop) (n : Nat)
    (f : Nat → Label) (beta : Label)
    (hOrdered : ∀ i j, i < j → j < n → lt (f i) (f j))
    (hBound : ReflectionTransport.Bounded lt n f beta)
    {i j : Nat} (hij : i < j) (hj : j ≤ n) :
    lt (atEnd n f beta i) (atEnd n f beta j) := by
  have hi : i < n := by omega
  rw [atEnd_before n f beta hi]
  by_cases h : j < n
  · rw [atEnd_before n f beta h]
    exact hOrdered i j hij h
  · have he : j = n := by omega
    subst j
    rw [atEnd_self]
    exact hBound i hi

theorem atEnd_bounded (lt : Label → Label → Prop) (n : Nat)
    (f : Nat → Label) (beta : Label)
    (hBound : ReflectionTransport.Bounded lt n f beta) {i : Nat} (hi : i ≤ n) :
    atEnd n f beta i = beta ∨ lt (atEnd n f beta i) beta := by
  by_cases h : i < n
  · exact Or.inr (by rw [atEnd_before n f beta h]; exact hBound i h)
  · have he : i = n := by omega
    exact Or.inl (by simp [he])

theorem splice_atEnd {n c i : Nat} (f reflected : Nat → Label) (hi : i ≤ n) :
    ReflectionTransport.spliceLabel n c f reflected i =
      atEnd n reflected (f c) i := by
  by_cases h : i < n
  · rw [ReflectionTransport.spliceLabel_old f reflected h, atEnd_before n reflected (f c) h]
  · have he : i = n := by omega
    subst i
    rw [ReflectionTransport.spliceLabel_first, atEnd_self]

/-- Both endpoint references rebind; the parent remains a strict prefix address. -/
theorem splice_seam
    (R : Label → Label → Label → Label → Prop)
    {n c : Nat} (f reflected : Nat → Label) (a : Entry)
    (ha : NeedValid n a)
    (hR : R (atEnd n reflected (f c) a.row) (atEnd n reflected (f c) a.root)
      (reflected a.parent) (f c)) :
    let next := ReflectionTransport.spliceLabel n c f reflected
    R (next a.row) (next a.root) (next a.parent) (next n) := by
  dsimp only
  rw [splice_atEnd f reflected ha.1, splice_atEnd f reflected ha.2.1,
    ReflectionTransport.spliceLabel_old f reflected ha.2.2,
    ReflectionTransport.spliceLabel_first]
  exact hR

#print axioms holds_take
#print axioms weaken_relation
#print axioms splice_four
#print axioms atEnd_strict
#print axioms splice_seam

end OrdinalFormal.ARD2
