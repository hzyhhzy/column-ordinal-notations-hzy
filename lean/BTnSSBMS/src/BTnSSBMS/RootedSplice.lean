import BTnSSBMS.KeySplice
import BTnSSBMS.InsertionActivation

/-!
Every unmatched key is guarded by a still-saved binding whose latest
position is the original root. This invariant survives filtering and
saving. An inactive root therefore contributes exactly zero height,
including queries through an external frame that has lost that root.
-/
namespace BTnSSBMS.Encoder

structure RootedInsertion (root : Nat) (keyOf : Binding → Key)
    (old new : List Binding) (pool : List Key) extends RekeyedInsertion keyOf old new pool where
  gate : ∀ k ∈ inserted, ∃ b ∈ old, b.latest = some root ∧ Keys.compare (keyOf b) k = .lt

def RootedInsertion.congr {root : Nat} {keyOf nextKeyOf : Binding → Key}
    {old new : List Binding} {pool : List Key}
    (splice : RootedInsertion root keyOf old new pool)
    (same : ∀ b ∈ old, nextKeyOf b = keyOf b) : RootedInsertion root nextKeyOf old new pool where
  toRekeyedInsertion := splice.toRekeyedInsertion.congr same
  gate := by
    intro k member
    obtain ⟨b, retained, latest, less⟩ := splice.gate k member
    exact ⟨b, retained, latest, by rw [same b retained]; exact less⟩

def RootedInsertion.filtered {root : Nat} {keyOf : Binding → Key}
    {old new : List Binding} {pool : List Key}
    (splice : RootedInsertion root keyOf old new pool) (oldKey newKey : Key)
    (comparisons : ∀ b ∈ old, Keys.compare (keyOf b) newKey = Keys.compare b.key oldKey) :
    RootedInsertion root keyOf (smaller old oldKey) (smaller new newKey) pool where
  toRekeyedInsertion := splice.toRekeyedInsertion.filtered oldKey newKey comparisons
  gate := by
    intro k member
    obtain ⟨kept, below⟩ := List.mem_filter.mp member
    obtain ⟨b, retained, latest, less⟩ := splice.gate k kept
    have low : Keys.compare b.key oldKey = .lt := by
      rw [← comparisons b retained]
      exact Keys.compare_lt_trans _ _ _ less (by simpa only [beq_iff_eq] using below)
    exact ⟨b, List.mem_filter.mpr ⟨retained, by simp only [low, beq_self_eq_true]⟩, latest, less⟩

def RootedInsertion.saved {root : Nat} {keyOf nextKeyOf : Binding → Key}
    {old new : List Binding} {pool : List Key}
    (splice : RootedInsertion root keyOf old new pool) (oldKey newKey : Key)
    (comparisons : ∀ b ∈ old, Keys.compare (keyOf b) newKey = Keys.compare b.key oldKey)
    (stable : ∀ b ∈ smaller old oldKey, nextKeyOf b = keyOf b)
    (oldBinding newBinding : Binding) (oldSaved : nextKeyOf oldBinding = newKey)
    (newSaved : newBinding.key = newKey) :
    RootedInsertion root nextKeyOf (smaller old oldKey ++ [oldBinding])
      (smaller new newKey ++ [newBinding]) pool where
  toRekeyedInsertion := splice.toRekeyedInsertion.saved oldKey newKey comparisons stable
    oldBinding newBinding oldSaved newSaved
  gate := by
    intro k member
    obtain ⟨b, retained, latest, less⟩ := (splice.filtered oldKey newKey comparisons).gate k member
    exact ⟨b, List.mem_append_left _ retained, latest, by rw [stable b retained]; exact less⟩

def RootedInsertion.virtual (root : Nat) (keyOf : Binding → Key) (pool : List Key)
    (zero : keyOf zeroBinding = .nil) : RootedInsertion root keyOf virtualFrame virtualFrame pool where
  toRekeyedInsertion := RekeyedInsertion.virtual keyOf pool zero
  gate := by intro k member; cases member

def RekeyedInsertion.rooted_of_empty {root : Nat} {keyOf : Binding → Key}
    {old new : List Binding} {pool : List Key}
    (splice : RekeyedInsertion keyOf old new pool) (empty : splice.inserted = []) :
    RootedInsertion root keyOf old new pool where
  toRekeyedInsertion := splice
  gate := by intro k member; rw [empty] at member; cases member

theorem RootedInsertion.height_eq_of_inactive {root : Nat} {keyOf : Binding → Key}
    {old new : List Binding} {pool : List Key}
    (splice : RootedInsertion root keyOf old new pool)
    (oldOrdered : FrameOrdered old) (oldDense : FrameDense old) (oldZero : HasZero old)
    (newOrdered : FrameOrdered new) (newDense : FrameDense new) (newZero : HasZero new)
    (oldKey newKey : Key)
    (comparisons : ∀ b ∈ old, Keys.compare (keyOf b) newKey = Keys.compare b.key oldKey)
    (inactive : ¬ ∃ b ∈ smaller old oldKey, b.latest = some root) :
    firstHeight new newKey = firstHeight old oldKey := by
  let f := fun b : Binding => {b with key := keyOf b}
  have related := KeyFrameRel.map_preserving_height old f (fun _ => rfl)
  apply (splice.toRekeyedInsertion.toInsertion f (fun _ _ => rfl)).rekey_height_eq_below
    related oldOrdered oldDense oldZero newOrdered newDense newZero oldKey newKey comparisons
  intro k member
  obtain ⟨b, retained, latest, less⟩ := splice.gate k member
  have notAbove : Keys.compare (keyOf b) newKey ≠ .lt := by
    rw [comparisons b retained]
    intro low
    exact inactive ⟨b, List.mem_filter.mpr ⟨retained, by simp only [low, beq_self_eq_true]⟩, latest⟩
  exact keys_below_inserted_of_not_above (keyOf b) newKey [k]
    (by intro x hx; simpa only [List.mem_singleton.mp hx] using less) notAbove k (by simp)

/-- Any implication from retained roots to actual activation suffices.
The concrete standard-query theorem supplies it using the real parent
search; there is no global shift when the original root is inactive. -/
theorem RootedInsertion.height_le_activated {root : Nat} {keyOf : Binding → Key}
    {old new : List Binding} {pool : List Key}
    (splice : RootedInsertion root keyOf old new pool)
    (oldOrdered : FrameOrdered old) (oldDense : FrameDense old) (oldZero : HasZero old)
    (newOrdered : FrameOrdered new) (newDense : FrameDense new) (newZero : HasZero new)
    (oldKey newKey : Key)
    (comparisons : ∀ b ∈ old, Keys.compare (keyOf b) newKey = Keys.compare b.key oldKey)
    (active : Prop) [Decidable active]
    (activates : (∃ b ∈ smaller old oldKey, b.latest = some root) → active) :
    firstHeight new newKey ≤ firstHeight old oldKey + if active then 2 * pool.length else 0 := by
  by_cases yes : active
  · rw [if_pos yes]
    exact splice.toRekeyedInsertion.height_le_pool oldOrdered oldDense oldZero newOrdered newDense newZero
      oldKey newKey comparisons
  · rw [if_neg yes, Nat.add_zero]
    exact Nat.le_of_eq (splice.height_eq_of_inactive oldOrdered oldDense oldZero newOrdered newDense newZero
      oldKey newKey comparisons (fun retained => yes (activates retained)))

end BTnSSBMS.Encoder
