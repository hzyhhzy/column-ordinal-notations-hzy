import BTnSSBMS.KeyLevels

/-!
Finite query arithmetic for an insertion of bindings. The two frames may
have different pointers, and may already share an arbitrary high-key tail.
Only their complete key lists are matched. Ordered, dense real frames then
give the exact height balance, including a fresh query becoming a reuse.
This is the local comparison kernel, not a theorem about whole blocks.
-/
namespace BTnSSBMS.Encoder

def freshBit (frame : List Binding) (key : Key) : Nat :=
  if (equal frame key).isSome then 0 else 1

theorem freshBit_le_one (frame : List Binding) (key : Key) : freshBit frame key ≤ 1 := by
  cases found : equal frame key <;> simp [freshBit, found]

theorem equal_none_iff_key_absent (frame : List Binding) (key : Key) :
    equal frame key = none ↔ key ∉ frame.map Binding.key := by
  constructor
  · intro missing member
    obtain ⟨b, inside, same⟩ := List.mem_map.mp member
    have absent := List.find?_eq_none.mp missing b inside
    simp only [same, Keys.compare_self, beq_self_eq_true] at absent
    contradiction
  · intro absent
    apply List.find?_eq_none.mpr
    intro b member
    cases compared : Keys.compare b.key key with
    | lt => simp
    | gt => simp
    | eq =>
      exact False.elim (absent (List.mem_map.mpr ⟨b, member, Keys.compare_eq_imp _ _ compared⟩))

theorem freshBit_congr {left right : List Binding} (key : Key)
    (same : key ∈ left.map Binding.key ↔ key ∈ right.map Binding.key) :
    freshBit right key = freshBit left key := by
  have missing : equal left key = none ↔ equal right key = none := by
    rw [equal_none_iff_key_absent, equal_none_iff_key_absent]
    exact not_congr same
  cases old : equal left key <;> cases new : equal right key <;>
    simp_all [freshBit]

theorem smaller_length_keys (frame : List Binding) (key : Key) :
    (smaller frame key).length =
      ((frame.map Binding.key).filter (fun k => Keys.compare k key == .lt)).length := by
  simp only [List.filter_map, List.length_map, smaller]
  rfl

/-- Binding hits occupy even ranks and fresh-key gaps occupy odd ranks.
The fresh bit avoids truncated-subtraction exceptional cases at zero. -/
theorem firstHeight_rank {frame : List Binding} (ordered : FrameOrdered frame)
    (dense : FrameDense frame) (zero : HasZero frame) (key : Key) :
    firstHeight frame key + freshBit frame key = 2 * (smaller frame key).length := by
  cases found : equal frame key with
  | none => simpa [freshBit, found] using firstHeight_fresh ordered dense zero key found
  | some b => simpa [freshBit, found] using firstHeight_reused ordered dense key b found

/-- A finite splice in the key list. This does not assume an encoder
transport or any block inequality. Pointers are intentionally unrestricted. -/
structure FrameKeyInsertion (left right : List Binding) where
  before : List Key
  inserted : List Key
  after : List Key
  old_keys : left.map Binding.key = before ++ after
  new_keys : right.map Binding.key = before ++ inserted ++ after

theorem FrameKeyInsertion.present_iff {left right : List Binding}
    (splice : FrameKeyInsertion left right) (key : Key) :
    key ∈ right.map Binding.key ↔ key ∈ left.map Binding.key ∨ key ∈ splice.inserted := by
  rw [splice.old_keys, splice.new_keys]
  simp only [List.mem_append]
  constructor
  · rintro ((a | b) | c)
    · exact Or.inl (Or.inl a)
    · exact Or.inr b
    · exact Or.inl (Or.inr c)
  · rintro ((a | c) | b)
    · exact Or.inl (Or.inl a)
    · exact Or.inr c
    · exact Or.inl (Or.inr b)

theorem FrameKeyInsertion.smaller_length {left right : List Binding}
    (splice : FrameKeyInsertion left right) (key : Key) :
    (smaller right key).length = (smaller left key).length +
      (splice.inserted.filter (fun k => Keys.compare k key == .lt)).length := by
  rw [smaller_length_keys, smaller_length_keys, splice.old_keys, splice.new_keys]
  simp only [List.filter_append, List.length_append]
  omega

theorem FrameKeyInsertion.height_balance {left right : List Binding}
    (splice : FrameKeyInsertion left right)
    (oldOrdered : FrameOrdered left) (oldDense : FrameDense left) (oldZero : HasZero left)
    (newOrdered : FrameOrdered right) (newDense : FrameDense right) (newZero : HasZero right)
    (key : Key) :
    firstHeight right key + freshBit right key =
      firstHeight left key + freshBit left key +
        2 * (splice.inserted.filter (fun k => Keys.compare k key == .lt)).length := by
  rw [firstHeight_rank newOrdered newDense newZero, firstHeight_rank oldOrdered oldDense oldZero,
    splice.smaller_length]
  omega

/-- Above the inserted interval, even an already existing high-key tail
has exactly the claimed uniform shift. No fresh/reuse assumption is made. -/
theorem FrameKeyInsertion.height_eq_above {left right : List Binding}
    (splice : FrameKeyInsertion left right)
    (oldOrdered : FrameOrdered left) (oldDense : FrameDense left) (oldZero : HasZero left)
    (newOrdered : FrameOrdered right) (newDense : FrameDense right) (newZero : HasZero right)
    (key : Key) (above : ∀ k ∈ splice.inserted, Keys.compare k key = .lt) :
    firstHeight right key = firstHeight left key + 2 * splice.inserted.length := by
  have absent : key ∉ splice.inserted := by
    intro member
    have impossible := above key member
    simp only [Keys.compare_self] at impossible
    contradiction
  have same := freshBit_congr (left := left) (right := right) key (by
    rw [splice.present_iff]
    exact ⟨Or.inl, fun h => h.resolve_right absent⟩)
  have all : splice.inserted.filter (fun k => Keys.compare k key == .lt) = splice.inserted :=
    List.filter_eq_self.mpr (fun k member => by simp only [above k member, beq_self_eq_true])
  have balance := splice.height_balance oldOrdered oldDense oldZero newOrdered newDense newZero key
  rw [all, same] at balance
  omega

/-- If the query has not passed every inserted key, the uniformly shifted
old first height is strictly greater. This includes the important case
where an old fresh key is now reused from the inserted interval. -/
theorem FrameKeyInsertion.height_lt_shift {left right : List Binding}
    (splice : FrameKeyInsertion left right)
    (oldOrdered : FrameOrdered left) (oldDense : FrameDense left) (oldZero : HasZero left)
    (newOrdered : FrameOrdered right) (newDense : FrameDense right) (newZero : HasZero right)
    (key : Key) (notAbove : ¬ ∀ k ∈ splice.inserted, Keys.compare k key = .lt) :
    firstHeight right key < firstHeight left key + 2 * splice.inserted.length := by
  have countLe := List.length_filter_le (fun k => Keys.compare k key == .lt) splice.inserted
  have countNe : (splice.inserted.filter (fun k => Keys.compare k key == .lt)).length ≠
      splice.inserted.length := by
    intro same
    have all := List.length_filter_eq_length_iff.mp same
    exact notAbove (fun k member => by simpa only [beq_iff_eq] using all k member)
  have balance := splice.height_balance oldOrdered oldDense oldZero newOrdered newDense newZero key
  have oldBit := freshBit_le_one left key
  omega

theorem FrameKeyInsertion.height_le_shift {left right : List Binding}
    (splice : FrameKeyInsertion left right)
    (oldOrdered : FrameOrdered left) (oldDense : FrameDense left) (oldZero : HasZero left)
    (newOrdered : FrameOrdered right) (newDense : FrameDense right) (newZero : HasZero right)
    (key : Key) :
    firstHeight right key ≤ firstHeight left key + 2 * splice.inserted.length := by
  by_cases above : ∀ k ∈ splice.inserted, Keys.compare k key = .lt
  · exact Nat.le_of_eq (splice.height_eq_above oldOrdered oldDense oldZero newOrdered newDense newZero key above)
  · exact Nat.le_of_lt (splice.height_lt_shift oldOrdered oldDense oldZero newOrdered newDense newZero key above)

/-- Below the whole interval, inserting bindings changes neither the
fresh/reuse choice nor the first key-row height. -/
theorem FrameKeyInsertion.height_eq_below {left right : List Binding}
    (splice : FrameKeyInsertion left right)
    (oldOrdered : FrameOrdered left) (oldDense : FrameDense left) (oldZero : HasZero left)
    (newOrdered : FrameOrdered right) (newDense : FrameDense right) (newZero : HasZero right)
    (key : Key) (below : ∀ k ∈ splice.inserted, Keys.compare key k = .lt) :
    firstHeight right key = firstHeight left key := by
  have absent : key ∉ splice.inserted := by
    intro member
    have impossible := below key member
    simp only [Keys.compare_self] at impossible
    contradiction
  have same := freshBit_congr (left := left) (right := right) key (by
    rw [splice.present_iff]
    exact ⟨Or.inl, fun h => h.resolve_right absent⟩)
  have none : splice.inserted.filter (fun k => Keys.compare k key == .lt) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro k member hit
    exact Keys.compare_asymmetric _ _ (below k member) (by simpa only [beq_iff_eq] using hit)
  have balance := splice.height_balance oldOrdered oldDense oldZero newOrdered newDense newZero key
  rw [none, same] at balance
  simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at balance
  omega

end BTnSSBMS.Encoder
