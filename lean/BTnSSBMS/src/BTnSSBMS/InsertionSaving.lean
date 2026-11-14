import BTnSSBMS.FrameInsertion

/-! The actual filtering and saving operations preserve a key insertion.
This includes forest slots, which inherit only the filtered frame and do
not save the owner's new binding. No recursive block transport is assumed. -/
namespace BTnSSBMS.Encoder

theorem smaller_keys (frame : List Binding) (key : Key) :
    (smaller frame key).map Binding.key =
      (frame.map Binding.key).filter (fun k => Keys.compare k key == .lt) := by
  simp only [List.filter_map, smaller]
  rfl

def FrameKeyInsertion.filtered {left right : List Binding}
    (splice : FrameKeyInsertion left right) (key : Key) :
    FrameKeyInsertion (smaller left key) (smaller right key) where
  before := splice.before.filter (fun k => Keys.compare k key == .lt)
  inserted := splice.inserted.filter (fun k => Keys.compare k key == .lt)
  after := splice.after.filter (fun k => Keys.compare k key == .lt)
  old_keys := by rw [smaller_keys, splice.old_keys, List.filter_append]
  new_keys := by rw [smaller_keys, splice.new_keys, List.filter_append, List.filter_append]

def FrameKeyInsertion.saved {left right : List Binding}
    (splice : FrameKeyInsertion left right) (key : Key) (old new : Binding)
    (oldKey : old.key = key) (newKey : new.key = key) :
    FrameKeyInsertion (smaller left key ++ [old]) (smaller right key ++ [new]) where
  before := (splice.filtered key).before
  inserted := (splice.filtered key).inserted
  after := (splice.filtered key).after ++ [key]
  old_keys := by
    rw [List.map_append, List.map_cons, List.map_nil, oldKey, (splice.filtered key).old_keys,
      List.append_assoc]
  new_keys := by
    rw [List.map_append, List.map_cons, List.map_nil, newKey, (splice.filtered key).new_keys,
      List.append_assoc]

theorem FrameKeyInsertion.filtered_above {left right : List Binding}
    (splice : FrameKeyInsertion left right) (key : Key)
    (above : ∀ k ∈ splice.inserted, Keys.compare k key = .lt) :
    (splice.filtered key).inserted = splice.inserted :=
  List.filter_eq_self.mpr (fun k member => by simp only [above k member, beq_self_eq_true])

theorem FrameKeyInsertion.filtered_below {left right : List Binding}
    (splice : FrameKeyInsertion left right) (key : Key)
    (below : ∀ k ∈ splice.inserted, Keys.compare key k = .lt) :
    (splice.filtered key).inserted = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro k member hit
  exact Keys.compare_asymmetric _ _ (below k member) (by simpa only [beq_iff_eq] using hit)

theorem FrameKeyInsertion.fresh_iff_of_not_inserted {left right : List Binding}
    (splice : FrameKeyInsertion left right) (key : Key) (absent : key ∉ splice.inserted) :
    equal right key = none ↔ equal left key = none := by
  rw [equal_none_iff_key_absent, equal_none_iff_key_absent, splice.present_iff]
  simp only [not_or, absent, not_false_eq_true, and_true]

/-- Saving a paired real binding changes no conclusion about the inserted
keys: above the interval it survives intact; below it is removed. Latest
and definition pointers need not be equal to derive this key-list fact. -/
theorem FrameKeyInsertion.saved_interval {left right : List Binding}
    (splice : FrameKeyInsertion left right) (key : Key) (old new : Binding)
    (oldKey : old.key = key) (newKey : new.key = key) :
    (splice.saved key old new oldKey newKey).inserted =
      splice.inserted.filter (fun k => Keys.compare k key == .lt) := rfl

def FrameKeyInsertion.of_append (left extra : List Binding) :
    FrameKeyInsertion left (left ++ extra) where
  before := left.map Binding.key
  inserted := extra.map Binding.key
  after := []
  old_keys := by rw [List.append_nil]
  new_keys := by rw [List.map_append, List.append_nil]

end BTnSSBMS.Encoder
