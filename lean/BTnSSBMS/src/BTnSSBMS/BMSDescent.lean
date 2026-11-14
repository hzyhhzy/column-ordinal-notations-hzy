import BTnSSBMS.ParentValues
import BTnSSBMS.Order

/-!
Lexicographic descent for every defined, nonempty, fixed-width BM4 short
expansion. This is only strict descent in the raw order; the raw order is
not well-founded. Thus this module is not a BMS well-ordering proof.
-/
namespace BTnSSBMS

theorem columnCompare_lt_at (xs ys : List Nat) (k : Nat)
    (left : k < xs.length) (right : k < ys.length)
    (common : ∀ j, j < k → xs[j]?.getD 0 = ys[j]?.getD 0)
    (strict : xs[k]?.getD 0 < ys[k]?.getD 0) : listCompare compare xs ys = .lt := by
  induction k generalizing xs ys with
  | zero =>
    cases xs with
    | nil => simp at left
    | cons x xs =>
      cases ys with
      | nil => simp at right
      | cons y ys =>
        have small : x < y := by simpa using strict
        simp only [listCompare, Nat.compare_eq_lt.mpr small]
  | succ k ih =>
    cases xs with
    | nil => simp at left
    | cons x xs =>
      cases ys with
      | nil => simp at right
      | cons y ys =>
        have same : x = y := by simpa using common 0 (by omega)
        subst y
        simp only [listCompare, natCompare_self]
        apply ih xs ys (by simpa using left) (by simpa using right)
        · intro j hj
          simpa only [List.getElem?_cons_succ] using common (j + 1) (by omega)
        · simpa only [List.getElem?_cons_succ] using strict

namespace BMS

theorem lastPositive_bounds (start : Nat) (xs : List Nat) (row : Nat)
    (found : lastPositive start xs = some row) : start ≤ row ∧ row < start + xs.length := by
  induction xs generalizing start with
  | nil => simp [lastPositive] at found
  | cons x xs ih =>
    cases tail : lastPositive (start + 1) xs with
    | some i =>
      have same : i = row := by simpa [lastPositive, tail] using found
      subst i
      have bounds := ih (start + 1) tail
      simp only [List.length_cons]
      omega
    | none =>
      by_cases positive : 0 < x
      · have same : start = row := by simpa [lastPositive, tail, positive] using found
        subst row
        simp only [List.length_cons]
        omega
      · simp [lastPositive, tail, positive] at found

theorem thresholds_at_root (d : Nat) (m : Matrix) (root cap : Nat)
    (inside : root < m.length) (room : cap ≤ d) :
    (thresholds (parentTable d m) root cap)[root]?.getD 0 = cap := by
  have atCap := thresholds_ancestry d m root cap room root inside cap
  have atValue := thresholds_ancestry d m root cap room root inside
    ((thresholds (parentTable d m) root cap)[root]?.getD 0)
  have allRoot : Parents.Ancestor (parentTable d m)
      ((thresholds (parentTable d m) root cap)[root]?.getD 0) root root := .refl _
  have upper : ¬ cap < (thresholds (parentTable d m) root cap)[root]?.getD 0 :=
    fun h => Nat.lt_irrefl _ (atCap.mp h).1
  have lower : ¬ (thresholds (parentTable d m) root cap)[root]?.getD 0 < cap :=
    fun h => Nat.lt_irrefl _ (atValue.mpr ⟨h, allRoot⟩)
  omega

private theorem mapIdx_reading (xs : List Nat) (f : Nat → Nat → Nat) (j : Nat)
    (inside : j < xs.length) :
    (xs.mapIdx f)[j]?.getD 0 = f j (xs[j]?.getD 0) := by
  rw [List.getElem?_mapIdx, List.getElem?_eq_getElem inside]
  rfl

private theorem zip_sub_reading (xs ys : List Nat) (j : Nat)
    (left : j < xs.length) (right : j < ys.length) :
    (xs.zipWith (· - ·) ys)[j]?.getD 0 = xs[j]?.getD 0 - ys[j]?.getD 0 := by
  rw [List.getElem?_zipWith, List.getElem?_eq_getElem left, List.getElem?_eq_getElem right]
  rfl

theorem first_copy_column_smaller (d : Nat) (m : Matrix) (root endpoint top : Nat)
    (rootCol last : List Nat) (rootLookup : m[root]? = some rootCol)
    (lastLookup : m[endpoint]? = some last)
    (rootWidth : rootCol.length = d) (lastWidth : last.length = d) (room : top < d)
    (edge : Parents.parent (parentTable d m) top endpoint = some root) :
    listCompare compare
      (rootCol.mapIdx fun j v => if j < top then v + (last.zipWith (· - ·) rootCol)[j]?.getD 0 else v)
      last = .lt := by
  apply columnCompare_lt_at _ last top (by simpa only [List.length_mapIdx, rootWidth] using room)
    (by omega)
  · intro j lower
    have inRoot : j < rootCol.length := by omega
    have inLast : j < last.length := by omega
    rw [mapIdx_reading rootCol _ j inRoot]
    simp only [lower, if_true]
    rw [zip_sub_reading last rootCol j inLast inRoot]
    have reconstruct := root_difference_reconstruct d m root endpoint top j room (by omega) edge
    simpa only [rootLookup, lastLookup, Option.getD_some] using reconstruct
  · rw [mapIdx_reading rootCol _ top (by omega)]
    simp only [Nat.lt_irrefl, if_false]
    simpa only [rootLookup, lastLookup, Option.getD_some] using
      root_reading_lt d m root endpoint top top room (Nat.le_refl _) edge

theorem copy_first_column (m : Matrix) (thresholds delta : List Nat) (root endIndex phase : Nat)
    (nonempty : root < endIndex) :
    ∃ rest, copy m thresholds delta root endIndex phase =
      ((m[root]?.getD []).mapIdx fun j v =>
        if j < thresholds[root]?.getD 0 then v + delta[j]?.getD 0 * phase else v) :: rest := by
  have positive : 0 < endIndex - root := by omega
  obtain ⟨k, same⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  simp only [copy, same, List.range_succ_eq_map, List.map_cons, Nat.add_zero]
  exact ⟨_, rfl⟩

/-- A defined nonzero short expansion strictly decreases raw lexicographic
order. This conclusion does not assert that the raw order is well-founded. -/
theorem expand_lt (d : Nat) (m result : Matrix) (index : Nat)
    (width : ∀ col ∈ m, col.length = d) (nonempty : m ≠ [])
    (success : expand? d m index = some result) : matrixCompare result m = .lt := by
  cases lastFound : m.getLast? with
  | none =>
    have empty : m = [] := List.getLast?_eq_none_iff.mp lastFound
    exact False.elim (nonempty empty)
  | some last =>
    obtain ⟨stem, shape⟩ := List.getLast?_eq_some_iff.mp lastFound
    have dropped : m.dropLast = stem := by simp [shape]
    have lastWidth : last.length = d := width last (by rw [shape]; simp)
    cases topFound : lastPositive 0 last with
    | none =>
      have value : result = m.dropLast := by simpa [expand?, lastFound, topFound] using success.symm
      rw [value, dropped, shape]
      unfold matrixCompare
      simpa only [List.append_nil, listCompare] using
        listCompare_common_prefix (listCompare compare) columnCompare_self stem [] [last]
    | some top =>
      have room : top < d := by
        have bound := (lastPositive_bounds 0 last top topFound).2
        omega
      cases finalFound : (parentTable d m).getLast? with
      | none => simp [expand?, lastFound, topFound, finalFound] at success
      | some final =>
        cases rootFound : final.parents[top]?.join with
        | none => simp [expand?, lastFound, topFound, finalFound, rootFound] at success
        | some root =>
          cases rootLookup : m[root]? with
          | none => simp [expand?, lastFound, topFound, finalFound, rootFound, rootLookup] at success
          | some rootCol =>
            have lastLookup : m[m.length - 1]? = some last := by
              rw [← List.getLast?_eq_getElem?]
              exact lastFound
            have finalLookup : (parentTable d m)[m.length - 1]? = some final := by
              rw [← parentTable_length d m, ← List.getLast?_eq_getElem?]
              exact finalFound
            have edge : Parents.parent (parentTable d m) top (m.length - 1) = some root := by
              simp only [Parents.parent, finalLookup, Option.bind_some, rootFound]
            have before : root < m.length - 1 := Parents.parent_earlier (parentTable_valid d m) edge
            have inside : root < m.length := by omega
            have rootWidth := width rootCol (List.mem_of_getElem? rootLookup)
            have threshold := thresholds_at_root d m root top inside (by omega)
            let a := thresholds (parentTable d m) root top
            let delta := last.zipWith (· - ·) rootCol
            have value : result = m.dropLast ++ (List.range index).flatMap
                (fun k => copy m a delta root (m.length - 1) (k + 1)) := by
              simpa [expand?, lastFound, topFound, finalFound, rootFound, rootLookup, a, delta]
                using success.symm
            have firstSmall := first_copy_column_smaller d m root (m.length - 1) top
              rootCol last rootLookup lastLookup rootWidth lastWidth room edge
            obtain ⟨rest, first⟩ := copy_first_column m a delta root (m.length - 1) 1 before
            have first' : copy m a delta root (m.length - 1) 1 =
                (rootCol.mapIdx fun j v =>
                  if j < top then v + delta[j]?.getD 0 else v) :: rest := by
              simpa only [a, rootLookup, Option.getD_some, threshold, Nat.mul_one] using first
            rw [value, dropped, shape]
            rw [shape] at first'
            unfold matrixCompare
            rw [listCompare_common_prefix (listCompare compare) columnCompare_self]
            cases index with
            | zero => rfl
            | succ n =>
              simp only [List.range_succ_eq_map, List.flatMap_cons, Nat.zero_add, first',
                List.cons_append, listCompare, delta, firstSmall]

end BMS
end BTnSSBMS
