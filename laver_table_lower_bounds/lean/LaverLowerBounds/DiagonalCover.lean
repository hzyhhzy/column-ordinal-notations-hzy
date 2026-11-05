import LaverLowerBounds.CoverDescent

set_option autoImplicit false

namespace LaverLowerBounds.ParentBMS

/-- Parent form of the numeric diagonal (0^h)(1^h)...((m-1)^h). -/
def diagonal (h m : Nat) : Matrix :=
  (List.range m).map fun i => if i = 0 then [] else List.replicate h (i - 1)

@[simp] theorem diagonal_length (h m : Nat) : (diagonal h m).length = m := by simp [diagonal]

theorem diagonal_column {h m i : Nat} (hi : i < m) :
    (diagonal h m)[i]? = some (if i = 0 then [] else List.replicate h (i - 1)) := by
  rw [diagonal, List.getElem?_map, List.getElem?_range hi]
  rfl

theorem diagonal_parent_iff {h m q p i : Nat} :
    parent (diagonal h m) q i = some p ↔ i < m ∧ 0 < i ∧ q < h ∧ p = i - 1 := by
  by_cases hi : i < m
  · rw [parent, diagonal_column hi, Option.bind_some]
    by_cases hz : i = 0
    · simp [hz]
    · rw [if_neg hz, List.getElem?_replicate]
      by_cases hq : q < h
      · simp only [if_pos hq, Option.some.injEq]
        constructor
        · intro he; exact ⟨hi, by omega, hq, he.symm⟩
        · intro he; exact he.2.2.2.symm
      · simp [hq]
  · have hn : ¬ i < (diagonal h m).length := by simpa using hi
    simp only [parent, List.getElem?_eq_none (by omega : (diagonal h m).length ≤ i), Option.bind_none]
    simp [hi]

theorem diagonal_parent {h m q i : Nat} (hi : i < m) (hpos : 0 < i) (hq : q < h) :
    parent (diagonal h m) q i = some (i - 1) :=
  diagonal_parent_iff.mpr ⟨hi, hpos, hq, rfl⟩

theorem diagonal_ancestor {h m q p i : Nat} (hpi : p < i) (hi : i < m) (hq : q < h) :
    Ancestor (diagonal h m) q p i := by
  induction i using Nat.strongRecOn with
  | ind i ih =>
      have he := diagonal_parent hi (by omega) hq
      by_cases hp : p = i - 1
      · rw [hp]; exact .direct he
      · exact .step he (ih (i - 1) (by omega) (by omega) (by omega))

theorem diagonal_leftward (h m : Nat) : Leftward (diagonal h m) := by
  intro q i p hp
  obtain ⟨_, hpos, _, rfl⟩ := diagonal_parent_iff.mp hp
  omega

theorem diagonal_nested (h m : Nat) : Nested (diagonal h m) := by
  intro q i p hp
  obtain ⟨hi, hpos, hq, rfl⟩ := diagonal_parent_iff.mp hp
  exact .direct (diagonal_parent hi hpos (by omega))

theorem diagonal_shape (h m : Nat) : Shape h 0 (diagonal h m) := by
  intro i c hc
  have hi : i < m := by simpa using (List.getElem?_eq_some_iff.mp hc).1
  rw [diagonal_column hi, Option.some.injEq] at hc
  rw [← hc]
  by_cases hz : i = 0
  · simp [hz]
  · rw [if_neg hz]
    constructor
    · simp
    · intro p hp
      have := List.eq_of_mem_replicate hp
      omega

/-- Every leftward parent table with at most h rows and m columns is covered
by the diagonal. Canonicity is not needed for this combinatorial statement. -/
def diagonal_cover {s : Matrix} {h m : Nat} (hs : Shape h 0 s) (hm : s.length ≤ m) :
    Cover s (diagonal h m) where
  column i := m - s.length + i
  bounded i hi := by rw [diagonal_length]; omega
  strict i j hij _ := by omega
  edge q p i hp := by
    obtain ⟨c, hc, hcp⟩ := parent_some_iff.mp hp
    have hi := (List.getElem?_eq_some_iff.mp hc).1
    have hrow := (List.getElem?_eq_some_iff.mp hcp).1
    obtain ⟨hh, hleft⟩ := hs i c hc
    have hpi := hleft p (List.mem_of_getElem? hcp)
    exact diagonal_ancestor (by omega) (by omega) (by omega)
  last hne := by
    have hlen : 0 < s.length := by cases s <;> simp_all
    rw [diagonal_length]
    omega

#print axioms diagonal_cover

end LaverLowerBounds.ParentBMS
