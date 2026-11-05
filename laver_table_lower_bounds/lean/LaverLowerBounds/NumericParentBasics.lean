import YesMetaZFC.BMS.Lemma25
import LaverLowerBounds.ParentBMS

set_option autoImplicit false

namespace LaverLowerBounds.NumericBMS

open YesMetaZFC.BMS

theorem parent_none_above_support (a : BMSArray) {r : Nat}
    (hr : trimHeight a ≤ r) (i : Nat) : parent r a i = none := by
  cases hp : parent r a i with
  | none => rfl
  | some p =>
    obtain ⟨u, v, _, hv, huv⟩ := parent_some_entry_lt hp
    have := row_lt_trimHeight_of_entry?_eq_some_of_ne_zero hv (by omega)
    omega

/-- Trimming zero rows does not change any parent, including removed rows. -/
theorem parent_trim (a : BMSArray) (r i : Nat) :
    parent r (trimZeroRows a) i = parent r a i := by
  by_cases hr : r < trimHeight a
  · exact parent_trimZeroRows_of_lt a hr i
  · rw [parent_trimZeroRows_eq_none_of_le a (by omega),
      parent_none_above_support a (by omega)]

theorem parent_take (a : BMSArray) {k i : Nat} (hi : i < k)
    (hk : k ≤ a.length) (r : Nat) : parent r (a.take k) i = parent r a i := by
  apply parent_eq_of_entry?_eq_below
  · simp only [List.length_take]; omega
  · omega
  · intro j hj q
    unfold entry?
    rw [List.getElem?_take_of_lt (by omega)]

theorem parent_expand_stem {a : ValidArray} (c : ExpansionContext a)
    (n r : Nat) {i : Nat} (hi : i < c.lastIndex) :
    parent r (a.expand n).raw i = parent r a.raw i := by
  change parent r (trimZeroRows (expandRaw a.raw n)) i = _
  rw [parent_trim]
  apply parent_eq_of_entry?_eq_below
  · rw [c.length_expandRaw]
    have := c.parentColumn_lt_lastIndex
    have hmul : c.blockLength ≤ (n + 1) * c.blockLength :=
      Nat.le_mul_of_pos_left _ (by omega)
    unfold ExpansionContext.blockLength at hmul ⊢
    omega
  · rw [c.array_length]; omega
  · intro j hj q
    exact c.entry?_expandRaw_eq_of_lt_lastIndex n (by omega)

theorem ancestor_expand_stem {a : ValidArray} (c : ExpansionContext a)
    (n r p : Nat) {i : Nat} (hi : i < c.lastIndex) :
    isAncestor (a.expand n).raw r p i = isAncestor a.raw r p i := by
  apply isAncestor_congr_below
  intro j hj
  exact parent_expand_stem c n r (by omega)

theorem parent_expand_indices {a : ValidArray} (c : ExpansionContext a)
    {n k i : Nat} (hnk : n ≤ k) (hi : i < (a.expand n).raw.length)
    (r : Nat) : parent r (a.expand n).raw i = parent r (a.expand k).raw i := by
  change parent r (trimZeroRows (expandRaw a.raw n)) i =
    parent r (trimZeroRows (expandRaw a.raw k)) i
  rw [parent_trim, parent_trim]
  apply parent_eq_of_entry?_eq_below
  · simpa only [ValidArray.raw_expand, length_expand] using hi
  · have := c.length_expand_mono hnk
    rw [← length_expand, ← ValidArray.raw_expand]
    omega
  · intro j hj q
    exact c.entry?_expandRaw_indices_eq_of_lt_length hnk (by omega)

theorem parent_some_of_greatest_ancestor {a : BMSArray} {r i p : Nat}
    (hp : isAncestor a r p i = true)
    (hmax : ∀ q, isAncestor a r q i = true → q ≤ p) : parent r a i = some p := by
  cases he : parent r a i with
  | none => have := isAncestor_eq_false_of_parent_none he (ancestor := p); simp_all
  | some q =>
    have := ancestor_le_parent he hp
    have := hmax q (direct_parent_isAncestor he)
    have : q = p := by omega
    subst q; rfl

theorem parent_map_of_ancestry {a b : BMSArray} {r i j : Nat} (f : Nat → Nat)
    (hf : ∀ p q, p ≤ q → f p ≤ f q)
    (hforward : ∀ p, isAncestor a r p i = true → isAncestor b r (f p) j = true)
    (hback : ∀ q, parent r b j = some q →
      ∃ p, isAncestor a r p i = true ∧ f p = q) :
    parent r b j = (parent r a i).map f := by
  cases ha : parent r a i with
  | none =>
    cases hb : parent r b j with
    | none => rfl
    | some q =>
      obtain ⟨p, hp, _⟩ := hback q hb
      have := isAncestor_eq_false_of_parent_none ha (ancestor := p)
      simp_all
  | some p =>
    have hp := hforward p (direct_parent_isAncestor ha)
    cases hb : parent r b j with
    | none => have := isAncestor_eq_false_of_parent_none hb (ancestor := f p); simp_all
    | some q =>
      obtain ⟨u, hu, he⟩ := hback q hb
      have := hf u p (ancestor_le_parent ha hu)
      have := ancestor_le_parent hb hp
      have : q = f p := by omega
      simp_all

theorem shift_mono (root offset : Nat) {p q : Nat} (hpq : p ≤ q) :
    ParentBMS.shift root offset p ≤ ParentBMS.shift root offset q := by
  unfold ParentBMS.shift
  split <;> split <;> omega

#print axioms parent_expand_indices
#print axioms parent_map_of_ancestry

end LaverLowerBounds.NumericBMS
