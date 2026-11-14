import BTnSSBMS.InsertionSaving
import BTnSSBMS.RekeyInsertion

/-!
A splice of actual saved keys after contextual rekeying. Unlike
KeyFrameRel this permits unequal heights and an inserted interval.
Its surviving insertions are a sublist of a fixed original pool.
Filtering and saving cannot create new unmatched keys.
-/
namespace BTnSSBMS.Encoder

structure RekeyedInsertion (keyOf : Binding → Key) (old new : List Binding) (pool : List Key) where
  before : List Key
  inserted : List Key
  after : List Key
  old_keys : old.map keyOf = before ++ after
  new_keys : new.map Binding.key = before ++ inserted ++ after
  bounded : inserted.Sublist pool

def RekeyedInsertion.congr {keyOf nextKeyOf : Binding → Key} {old new : List Binding} {pool : List Key}
    (splice : RekeyedInsertion keyOf old new pool)
    (same : ∀ b ∈ old, nextKeyOf b = keyOf b) : RekeyedInsertion nextKeyOf old new pool where
  before := splice.before
  inserted := splice.inserted
  after := splice.after
  old_keys := (List.map_congr_left same).trans splice.old_keys
  new_keys := splice.new_keys
  bounded := splice.bounded

theorem map_smaller_rekey (old : List Binding) (keyOf : Binding → Key) (oldKey newKey : Key)
    (comparisons : ∀ b ∈ old, Keys.compare (keyOf b) newKey = Keys.compare b.key oldKey) :
    (smaller old oldKey).map keyOf =
      (old.map keyOf).filter (fun k => Keys.compare k newKey == .lt) := by
  induction old with
  | nil => rfl
  | cons b old ih =>
    have head := comparisons b (by simp)
    have tail := ih (fun x member => comparisons x (by simp only [List.mem_cons]; exact Or.inr member))
    simp only [smaller, List.filter_cons, List.map_cons, head]
    split
    · simpa only [List.map_cons, smaller] using congrArg (fun xs => keyOf b :: xs) tail
    · exact tail

def RekeyedInsertion.filtered {keyOf : Binding → Key} {old new : List Binding} {pool : List Key}
    (splice : RekeyedInsertion keyOf old new pool) (oldKey newKey : Key)
    (comparisons : ∀ b ∈ old, Keys.compare (keyOf b) newKey = Keys.compare b.key oldKey) :
    RekeyedInsertion keyOf (smaller old oldKey) (smaller new newKey) pool where
  before := splice.before.filter (fun k => Keys.compare k newKey == .lt)
  inserted := splice.inserted.filter (fun k => Keys.compare k newKey == .lt)
  after := splice.after.filter (fun k => Keys.compare k newKey == .lt)
  old_keys := by rw [map_smaller_rekey old keyOf oldKey newKey comparisons, splice.old_keys, List.filter_append]
  new_keys := by rw [smaller_keys, splice.new_keys, List.filter_append, List.filter_append]
  bounded := List.filter_sublist.trans splice.bounded

def RekeyedInsertion.saved {keyOf nextKeyOf : Binding → Key} {old new : List Binding} {pool : List Key}
    (splice : RekeyedInsertion keyOf old new pool) (oldKey newKey : Key)
    (comparisons : ∀ b ∈ old, Keys.compare (keyOf b) newKey = Keys.compare b.key oldKey)
    (stable : ∀ b ∈ smaller old oldKey, nextKeyOf b = keyOf b)
    (oldBinding newBinding : Binding) (oldSaved : nextKeyOf oldBinding = newKey)
    (newSaved : newBinding.key = newKey) :
    RekeyedInsertion nextKeyOf (smaller old oldKey ++ [oldBinding])
      (smaller new newKey ++ [newBinding]) pool where
  before := (splice.filtered oldKey newKey comparisons).before
  inserted := (splice.filtered oldKey newKey comparisons).inserted
  after := (splice.filtered oldKey newKey comparisons).after ++ [newKey]
  old_keys := by
    rw [List.map_append, List.map_cons, List.map_nil, oldSaved,
      List.map_congr_left stable, (splice.filtered oldKey newKey comparisons).old_keys,
      List.append_assoc]
  new_keys := by
    rw [List.map_append, List.map_cons, List.map_nil, newSaved,
      (splice.filtered oldKey newKey comparisons).new_keys, List.append_assoc]
  bounded := (splice.filtered oldKey newKey comparisons).bounded

theorem RekeyedInsertion.saved_interval {keyOf nextKeyOf : Binding → Key}
    {old new : List Binding} {pool : List Key}
    (splice : RekeyedInsertion keyOf old new pool) (oldKey newKey : Key)
    (comparisons : ∀ b ∈ old, Keys.compare (keyOf b) newKey = Keys.compare b.key oldKey)
    (stable : ∀ b ∈ smaller old oldKey, nextKeyOf b = keyOf b)
    (oldBinding newBinding : Binding) (oldSaved : nextKeyOf oldBinding = newKey)
    (newSaved : newBinding.key = newKey) :
    (splice.saved oldKey newKey comparisons stable oldBinding newBinding oldSaved newSaved).inserted =
      splice.inserted.filter (fun k => Keys.compare k newKey == .lt) := rfl

def RekeyedInsertion.virtual (keyOf : Binding → Key) (pool : List Key)
    (zero : keyOf zeroBinding = .nil) : RekeyedInsertion keyOf virtualFrame virtualFrame pool where
  before := [.nil]
  inserted := []
  after := []
  old_keys := by simp only [virtualFrame, List.map_cons, List.map_nil, zero, List.append_nil]
  new_keys := rfl
  bounded := List.nil_sublist pool

def RekeyedInsertion.toInsertion {keyOf : Binding → Key} {old new : List Binding} {pool : List Key}
    (splice : RekeyedInsertion keyOf old new pool) (f : Binding → Binding)
    (keys : ∀ b ∈ old, (f b).key = keyOf b) : FrameKeyInsertion (old.map f) new where
  before := splice.before
  inserted := splice.inserted
  after := splice.after
  old_keys := by rw [List.map_map]; exact (List.map_congr_left keys).trans splice.old_keys
  new_keys := splice.new_keys

theorem RekeyedInsertion.height_le_pool {keyOf : Binding → Key} {old new : List Binding} {pool : List Key}
    (splice : RekeyedInsertion keyOf old new pool)
    (oldOrdered : FrameOrdered old) (oldDense : FrameDense old) (oldZero : HasZero old)
    (newOrdered : FrameOrdered new) (newDense : FrameDense new) (newZero : HasZero new)
    (oldKey newKey : Key)
    (comparisons : ∀ b ∈ old, Keys.compare (keyOf b) newKey = Keys.compare b.key oldKey) :
    firstHeight new newKey ≤ firstHeight old oldKey + 2 * pool.length := by
  let f := fun b : Binding => {b with key := keyOf b}
  have related := KeyFrameRel.map_preserving_height old f (fun _ => rfl)
  have localBound := (splice.toInsertion f (fun _ _ => rfl)).rekey_height_le_shift related
    oldOrdered oldDense oldZero newOrdered newDense newZero oldKey newKey comparisons
  have size := splice.bounded.length_le
  exact Nat.le_trans localBound (by dsimp only [RekeyedInsertion.toInsertion]; omega)

end BTnSSBMS.Encoder
