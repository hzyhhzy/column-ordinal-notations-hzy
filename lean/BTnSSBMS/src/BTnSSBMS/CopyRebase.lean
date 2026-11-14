import BTnSSBMS.BMSBlocks

/-!
The ancestor-sensitive rebase used in the block conditions is exactly
the first copy of the actual BMS algorithm, cut at the requested endpoint.
This is a concrete bridge, not an abstract-context hypothesis. The full
last-hole coverage argument still needs its separate case analysis.
-/
namespace BTnSSBMS.BMS

theorem copy_length (m : Matrix) (active delta : List Nat) (root endIndex phase : Nat) :
    (copy m active delta root endIndex phase).length = endIndex - root := by
  simp only [copy, List.length_map, List.length_range]

theorem copy_column (m : Matrix) (active delta : List Nat) (root endIndex phase offset : Nat)
    (inside : offset < endIndex - root) :
    (copy m active delta root endIndex phase)[offset]? =
      some ((m[root + offset]?.getD []).mapIdx fun j v =>
        if j < active[root + offset]?.getD 0 then v + delta[j]?.getD 0 * phase else v) := by
  simp only [copy, List.getElem?_map, List.getElem?_range, inside, Option.map_some]

theorem rebase_length (d : Nat) (m : Matrix) (cut root destination : Nat) :
    (rebase d m cut root destination).length = (block m root).length := by
  simp only [rebase, List.length_mapIdx]

theorem rebase_column (d : Nat) (m : Matrix) (cut root destination offset : Nat)
    (inside : offset < (block m root).length) :
    (rebase d m cut root destination)[offset]? =
      (m[root + offset]?).map fun col => col.mapIdx fun j v =>
        if j < (thresholds (parentTable d m) root cut)[root + offset]?.getD 0 then
          v + ((m[destination]?.getD [])[j]?.getD 0 - (m[root]?.getD [])[j]?.getD 0)
        else v := by
  rw [rebase, List.getElem?_mapIdx, block_column m root offset inside]

private theorem column_zip_difference (m : Matrix) (root destination : Nat)
    (rootBound : root < m.length) (destinationBound : destination < m.length)
    (col : List Nat) (rootWidth : (m[root]).length = col.length)
    (destinationWidth : (m[destination]).length = col.length) (active : Nat) :
    (col.mapIdx fun j v => if j < active then
      v + ((m[destination]).zipWith (· - ·) m[root])[j]?.getD 0 * 1 else v) =
    (col.mapIdx fun j v => if j < active then
      v + ((m[destination]?.getD [])[j]?.getD 0 - (m[root]?.getD [])[j]?.getD 0)
      else v) := by
  apply List.ext_getElem
  · simp
  · intro j left right
    have inside : j < col.length := by simpa only [List.length_mapIdx] using left
    have inRoot : j < (m[root]).length := by omega
    have inDestination : j < (m[destination]).length := by omega
    simp only [List.getElem_mapIdx, List.getElem?_eq_getElem rootBound,
      List.getElem?_eq_getElem destinationBound, Option.getD_some, List.getElem?_zipWith,
      List.getElem?_eq_getElem inRoot, List.getElem?_eq_getElem inDestination,
      Nat.mul_one]

/-- The phase-one copy is a prefix of the concrete partial-rebased block.
No standardness, block sorting, or well-foundedness premise is needed. -/
theorem first_copy_eq_rebase_take (d : Nat) (m : Matrix) (cut root destination endIndex : Nat)
    (width : ∀ col ∈ m, col.length = d)
    (rootBound : root < m.length) (destinationBound : destination < m.length)
    (contained : endIndex - root ≤ (block m root).length) :
    copy m (thresholds (parentTable d m) root cut)
      ((m[destination]).zipWith (· - ·) m[root]) root endIndex 1 =
      (rebase d m cut root destination).take (endIndex - root) := by
  apply List.ext_getElem
  · simp only [copy_length, List.length_take, rebase_length, Nat.min_eq_left contained]
  · intro offset left right
    have copyBound : offset < endIndex - root := by simpa only [copy_length] using left
    have blockBound : offset < (block m root).length := by omega
    have prefixBound := (block_prefix m root).length_le
    have positionBound : root + offset < m.length := by
      simp only [List.length_drop] at prefixBound
      omega
    have first := copy_column m (thresholds (parentTable d m) root cut)
      ((m[destination]).zipWith (· - ·) m[root]) root endIndex 1 offset copyBound
    have second := rebase_column d m cut root destination offset blockBound
    have matching := column_zip_difference m root destination rootBound destinationBound
      m[root + offset] (by rw [width _ (List.getElem_mem rootBound), width _ (List.getElem_mem positionBound)])
      (by rw [width _ (List.getElem_mem destinationBound), width _ (List.getElem_mem positionBound)])
      ((thresholds (parentTable d m) root cut)[root + offset]?.getD 0)
    have optionEquality :
        (copy m (thresholds (parentTable d m) root cut)
          ((m[destination]).zipWith (· - ·) m[root]) root endIndex 1)[offset]? =
        ((rebase d m cut root destination).take (endIndex - root))[offset]? := by
      rw [first, List.getElem?_take_of_lt copyBound, second,
        List.getElem?_eq_getElem positionBound]
      simpa only [Option.getD_some, Option.map_some] using congrArg some matching
    simpa only [List.getElem?_eq_getElem left, List.getElem?_eq_getElem right,
      Option.some.injEq] using optionEquality

/-- For an actual selected parent, containment of the copied interval in
the block follows from ancestry; it is not an additional hypothesis. This
is the phase-one identity at an actual expansion root and endpoint. -/
theorem first_copy_from_parent (d : Nat) (m : Matrix) (top root endpoint : Nat)
    (width : ∀ col ∈ m, col.length = d) (room : top < d)
    (edge : Parents.parent (parentTable d m) top endpoint = some root) :
    copy m (thresholds (parentTable d m) root top)
      ((m[endpoint]?.getD []).zipWith (· - ·) (m[root]?.getD [])) root endpoint 1 =
      (rebase d m top root endpoint).take (endpoint - root) := by
  obtain ⟨a, lookup, _⟩ := Option.bind_eq_some_iff.mp edge
  have endpointBound : endpoint < m.length := by
    have bound := (List.getElem?_eq_some_iff.mp lookup).choose
    simpa only [parentTable_length] using bound
  have before := Parents.parent_earlier (parentTable_valid d m) edge
  have rootBound : root < m.length := by omega
  have high : Parents.Ancestor (parentTable d m) top root endpoint := .up edge (.refl _)
  have low := high.lower_row (parentTable_coherent d m) room (Nat.zero_le top)
  have reconstructed : root + (endpoint - root) = endpoint := by omega
  have contained : endpoint - root < (block m root).length := by
    apply (block_length_iff_ancestor d m (by omega) root (endpoint - root) (by omega)).mpr
    simpa only [reconstructed] using low
  simpa only [List.getElem?_eq_getElem rootBound, List.getElem?_eq_getElem endpointBound,
    Option.getD_some] using first_copy_eq_rebase_take d m top root endpoint endpoint
      width rootBound endpointBound (Nat.le_of_lt contained)

end BTnSSBMS.BMS
