import LaverLowerBounds.ParentGraph

set_option autoImplicit false

namespace LaverLowerBounds.ParentBMS

def prepare (stem : Matrix) (last : Column) (row root : Nat) : Matrix :=
  stem ++ [last.take row ++ (stem[root]?.getD []).drop row]

theorem prepare_length (stem : Matrix) (last : Column) (row root : Nat) :
    (prepare stem last row root).length = stem.length + 1 := by simp [prepare]

theorem parent_last (stem : Matrix) (last : Column) (row : Nat) :
    parent (stem ++ [last]) row stem.length = last[row]? := by simp [parent]

theorem parent_prepare_old {stem : Matrix} {last : Column} {row root q i : Nat}
    (hi : i < stem.length) : parent (prepare stem last row root) q i = parent stem q i :=
  parent_append_left hi

theorem parent_prepare_low {stem : Matrix} {last : Column} {row root q : Nat}
    (hrow : row ≤ last.length) (hq : q < row) :
    parent (prepare stem last row root) q stem.length = last[q]? := by
  rw [prepare, parent_last, List.getElem?_append_left]
  · exact List.getElem?_take_of_lt hq
  · rw [List.length_take_of_le hrow]
    exact hq

theorem parent_prepare_high {stem : Matrix} {last : Column} {row root q : Nat}
    (hrow : row ≤ last.length) (hq : row ≤ q) (hr : root < stem.length) :
    parent (prepare stem last row root) q stem.length = parent stem q root := by
  rw [prepare, parent_last, List.getElem?_append_right]
  · rw [List.length_take_of_le hrow, List.getElem?_drop]
    have he : row + (q - row) = q := by omega
    rw [he]
    simp only [parent, List.getElem?_eq_getElem hr, Option.getD_some, Option.bind_some]
  · rw [List.length_take_of_le hrow]
    exact hq

theorem prepare_prefix_one {stem : Matrix} {last : Column} {root : Nat}
    (hl : last.getLast? = some root) (hr : root < stem.length) :
    (prepare stem last (last.length - 1) root).IsPrefix (expandTail stem last 1) := by
  let head := last.take (last.length - 1) ++ (stem[root]?.getD []).drop (last.length - 1)
  have hhead : (copy stem last (last.length - 1) root (stem.length - root) 0)[0]? = some head := by
    rw [copy_zero, List.getElem?_map, List.getElem?_range (show 0 < stem.length - root by omega)]
    rfl
  cases hc : copy stem last (last.length - 1) root (stem.length - root) 0 with
  | nil => simp only [hc, List.getElem?_nil] at hhead; contradiction
  | cons c tail =>
      have he : c = head := by simpa only [hc, List.getElem?_cons_zero, Option.some.injEq] using hhead
      subst c
      rw [expandTail_one_positive hl, hc]
      exact ⟨tail, by simp only [prepare, List.append_assoc, List.singleton_append]; rfl⟩

theorem prepare_spends_budget {stem : Matrix} {last : Column} {root n : Nat}
    (hl : last.getLast? = some root) (hr : root < stem.length)
    (hn : PrefixDescent.Stops (fun s => expand s 1) (stem ++ [last]) n) :
    ∃ k, PrefixDescent.Stops (fun s => expand s 1) (prepare stem last (last.length - 1) root) k ∧ k < n := by
  exact PrefixDescent.stops_after_truncation (expand_preserves_stem 1) hn (by simp)
    (by rw [expand_append]; exact prepare_prefix_one hl hr)

theorem ancestry_prepare_low {stem : Matrix} {last : Column} {row root q p i : Nat}
    (hrow : row ≤ last.length) (hq : q < row)
    (ha : Ancestor (stem ++ [last]) q p i) : Ancestor (prepare stem last row root) q p i := by
  apply ha.map_edges (f := id)
  intro p i he
  apply Ancestor.direct
  change parent (prepare stem last row root) q i = some p
  have hi := parent_column_lt he
  simp only [List.length_append, List.length_singleton] at hi
  by_cases hiold : i < stem.length
  · rw [parent_prepare_old hiold]
    rwa [parent_append_left hiold] at he
  · have hei : i = stem.length := by omega
    subst i
    rw [parent_prepare_low hrow hq]
    rwa [parent_last] at he

theorem ancestry_prepare_from_root {stem : Matrix} {last : Column} {row root q p : Nat}
    (hrow : row ≤ last.length) (hq : row ≤ q) (hr : root < stem.length)
    (ha : Ancestor stem q p root) : Ancestor (prepare stem last row root) q p stem.length := by
  cases ha with
  | direct he => exact .direct (by rw [parent_prepare_high hrow hq hr]; exact he)
  | step he htail =>
      exact .step (by rw [parent_prepare_high hrow hq hr]; exact he)
        (htail.to_prefix_extension ⟨_, rfl⟩)

theorem prepare_leftward {stem : Matrix} {last : Column} {row root : Nat}
    (hrow : row ≤ last.length) (hr : root < stem.length)
    (hs : Leftward (stem ++ [last])) : Leftward (prepare stem last row root) := by
  intro q i p hp
  have hi := parent_column_lt hp
  rw [prepare_length] at hi
  by_cases hiold : i < stem.length
  · rw [parent_prepare_old hiold] at hp
    exact hs q i p (by rw [parent_append_left hiold]; exact hp)
  · have hei : i = stem.length := by omega
    subst i
    by_cases hq : q < row
    · rw [parent_prepare_low hrow hq] at hp
      exact hs q stem.length p (by rw [parent_last]; exact hp)
    · rw [parent_prepare_high hrow (by omega) hr] at hp
      have he := hs q root p (by rw [parent_append_left hr]; exact hp)
      omega

theorem prepare_nested {stem : Matrix} {last : Column} {row root : Nat}
    (hrow : row ≤ last.length) (hr : root < stem.length)
    (hcontrol : parent (stem ++ [last]) row stem.length = some root)
    (hs : Leftward (stem ++ [last])) (hn : Nested (stem ++ [last])) :
    Nested (prepare stem last row root) := by
  intro q i p hp
  have hi := parent_column_lt hp
  rw [prepare_length] at hi
  by_cases hiold : i < stem.length
  · rw [parent_prepare_old hiold] at hp
    have he : parent (stem ++ [last]) (q + 1) i = some p := by rw [parent_append_left hiold]; exact hp
    have ha := (hn q i p he).of_prefix ⟨[last], rfl⟩ hs hiold
    exact ha.to_prefix_extension ⟨_, rfl⟩
  · have hei : i = stem.length := by omega
    subst i
    by_cases hqlo : q + 1 < row
    · rw [parent_prepare_low hrow hqlo] at hp
      have he : parent (stem ++ [last]) (q + 1) stem.length = some p := by rw [parent_last]; exact hp
      exact ancestry_prepare_low hrow (by omega) (hn q stem.length p he)
    · rw [parent_prepare_high hrow (by omega) hr] at hp
      have he : parent (stem ++ [last]) (q + 1) root = some p := by rw [parent_append_left hr]; exact hp
      have ha := (hn q root p he).of_prefix ⟨[last], rfl⟩ hs hr
      by_cases hqhi : row ≤ q
      · exact ancestry_prepare_from_root hrow hqhi hr ha
      · have hqr : q + 1 = row := by omega
        have hroot : Ancestor (stem ++ [last]) q root stem.length := by
          apply hn q stem.length root
          rwa [hqr]
        have hroot' := ancestry_prepare_low (root := root) hrow (by omega : q < row) hroot
        exact (ha.to_prefix_extension ⟨_, rfl⟩).trans hroot'

#print axioms prepare_spends_budget
#print axioms prepare_nested

end LaverLowerBounds.ParentBMS
