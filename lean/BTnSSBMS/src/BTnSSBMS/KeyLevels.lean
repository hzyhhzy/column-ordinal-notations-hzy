import BTnSSBMS.FrameHeight

/-!
The first emitted key-row value distinguishes bound keys from fresh-key
gaps. This formalizes the nonrecursive part of fixed-entry order preservation:
if two different keys have the same first height, they are both fresh and
their entire smaller-binding environments are identical. Only that case
requires recursively comparing their attached forests.
-/
namespace BTnSSBMS.Encoder

/-- The key-row value at the first emitted representative (P or D). -/
def firstHeight (frame : List Binding) (key : Key) : Nat :=
  match equal frame key with
  | some bound => bound.height
  | none => (base (smaller frame key)).height + 1

theorem smaller_nested {frame : List Binding} (ordered : FrameOrdered frame)
    (a b : Key) (less : Keys.compare a b = .lt) :
    smaller frame a <+: smaller frame b := by
  have initial := (smaller_prefix ordered a).filter (fun bound => Keys.compare bound.key b == .lt)
  have unchanged : (smaller frame a).filter (fun bound => Keys.compare bound.key b == .lt) =
      smaller frame a := by
    apply List.filter_eq_self.mpr
    intro bound hb
    have lower : Keys.compare bound.key a = .lt := by
      simpa only [beq_iff_eq] using (List.mem_filter.mp hb).2
    simpa only [beq_iff_eq] using Keys.compare_lt_trans _ _ _ lower less
  rw [unchanged] at initial
  exact initial

theorem equal_cut_below_upper {frame : List Binding} (ordered : FrameOrdered frame)
    (a b : Key) (less : Keys.compare a b = .lt) (bound : Binding)
    (found : equal frame a = some bound) :
    smaller frame a ++ [bound] <+: smaller frame b := by
  have initial := (equal_cut_prefix ordered a bound found).filter
    (fun entry => Keys.compare entry.key b == .lt)
  have unchanged : (smaller frame a ++ [bound]).filter
      (fun entry => Keys.compare entry.key b == .lt) = smaller frame a ++ [bound] := by
    apply List.filter_eq_self.mpr
    intro entry he
    rcases List.mem_append.mp he with old | last
    · have lower : Keys.compare entry.key a = .lt := by
        simpa only [beq_iff_eq] using (List.mem_filter.mp old).2
      simpa only [beq_iff_eq] using Keys.compare_lt_trans _ _ _ lower less
    · have same : entry = bound := by simpa using last
      subst entry
      have keySame : bound.key = a := Keys.compare_eq_imp _ _
        (by simpa only [beq_iff_eq] using List.find?_some found)
      simp [keySame, less]
  rw [unchanged] at initial
  exact initial

theorem firstHeight_reused {frame : List Binding} (ordered : FrameOrdered frame)
    (dense : FrameDense frame) (key : Key) (bound : Binding)
    (found : equal frame key = some bound) :
    firstHeight frame key = 2 * (smaller frame key).length := by
  have cut := frameDense_prefix dense (equal_cut_prefix ordered key bound found)
  have height := cut (smaller frame key).length bound List.getElem?_concat_length
  simpa only [firstHeight, found] using height

theorem firstHeight_fresh {frame : List Binding} (ordered : FrameOrdered frame)
    (dense : FrameDense frame) (zero : HasZero frame) (key : Key)
    (fresh : equal frame key = none) :
    firstHeight frame key + 1 = 2 * (smaller frame key).length := by
  have below := frameDense_prefix dense (smaller_prefix ordered key)
  have nonempty := hasZero_nonempty (fresh_smaller_has_zero zero key fresh)
  simpa only [firstHeight, fresh, Nat.add_assoc] using base_height_next below nonempty

theorem firstHeight_lt_if_lower_bound {frame : List Binding} (ordered : FrameOrdered frame)
    (dense : FrameDense frame) (zero : HasZero frame) (a b : Key)
    (less : Keys.compare a b = .lt) (bound : Binding) (found : equal frame a = some bound) :
    firstHeight frame a < firstHeight frame b := by
  have lengths := (equal_cut_below_upper ordered a b less bound found).length_le
  simp only [List.length_append, List.length_cons, List.length_nil] at lengths
  have lower := firstHeight_reused ordered dense a bound found
  cases upperFound : equal frame b with
  | none => have upper := firstHeight_fresh ordered dense zero b upperFound; omega
  | some upperBound => have upper := firstHeight_reused ordered dense b upperBound upperFound; omega

theorem firstHeight_lt_if_upper_bound {frame : List Binding} (ordered : FrameOrdered frame)
    (dense : FrameDense frame) (zero : HasZero frame) (a b : Key)
    (less : Keys.compare a b = .lt) (bound : Binding) (found : equal frame b = some bound) :
    firstHeight frame a < firstHeight frame b := by
  cases lowerFound : equal frame a with
  | some lowerBound => exact firstHeight_lt_if_lower_bound ordered dense zero a b less lowerBound lowerFound
  | none =>
    have lengths := (smaller_nested ordered a b less).length_le
    have lower := firstHeight_fresh ordered dense zero a lowerFound
    have upper := firstHeight_reused ordered dense b bound found
    omega

theorem firstHeight_monotone {frame : List Binding} (ordered : FrameOrdered frame)
    (dense : FrameDense frame) (zero : HasZero frame) (a b : Key)
    (less : Keys.compare a b = .lt) : firstHeight frame a ≤ firstHeight frame b := by
  cases lowerFound : equal frame a with
  | some bound => exact Nat.le_of_lt (firstHeight_lt_if_lower_bound ordered dense zero a b less bound lowerFound)
  | none =>
    cases upperFound : equal frame b with
    | some bound => exact Nat.le_of_lt (firstHeight_lt_if_upper_bound ordered dense zero a b less bound upperFound)
    | none =>
      have lengths := (smaller_nested ordered a b less).length_le
      have lower := firstHeight_fresh ordered dense zero a lowerFound
      have upper := firstHeight_fresh ordered dense zero b upperFound
      omega

theorem firstHeight_equal_iff_fresh_same_gap {frame : List Binding} (ordered : FrameOrdered frame)
    (dense : FrameDense frame) (zero : HasZero frame) (a b : Key)
    (less : Keys.compare a b = .lt) :
    firstHeight frame a = firstHeight frame b ↔
      equal frame a = none ∧ equal frame b = none ∧ smaller frame a = smaller frame b := by
  constructor
  · intro same
    have lowerFresh : equal frame a = none := by
      cases lowerFound : equal frame a with
      | none => rfl
      | some bound =>
        have strict := firstHeight_lt_if_lower_bound ordered dense zero a b less bound lowerFound
        omega
    have upperFresh : equal frame b = none := by
      cases upperFound : equal frame b with
      | none => rfl
      | some bound =>
        have strict := firstHeight_lt_if_upper_bound ordered dense zero a b less bound upperFound
        omega
    have lower := firstHeight_fresh ordered dense zero a lowerFresh
    have upper := firstHeight_fresh ordered dense zero b upperFresh
    exact ⟨lowerFresh, upperFresh, (smaller_nested ordered a b less).eq_of_length (by omega)⟩
  · rintro ⟨lowerFresh, upperFresh, gap⟩
    simp only [firstHeight, lowerFresh, upperFresh, gap]

/-- Exhaustive comparison split for the first key-row values. There is no
third case where a binding's compressed header ties a different fresh key. -/
theorem firstHeight_compare_cases {frame : List Binding} (ordered : FrameOrdered frame)
    (dense : FrameDense frame) (zero : HasZero frame) (a b : Key)
    (less : Keys.compare a b = .lt) :
    firstHeight frame a < firstHeight frame b ∨
      (equal frame a = none ∧ equal frame b = none ∧ smaller frame a = smaller frame b) := by
  have nonstrict := firstHeight_monotone ordered dense zero a b less
  by_cases strict : firstHeight frame a < firstHeight frame b
  · exact Or.inl strict
  · exact Or.inr ((firstHeight_equal_iff_fresh_same_gap ordered dense zero a b less).mp (by omega))

end BTnSSBMS.Encoder
