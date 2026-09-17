import ARD2SkylineBridge
import ARD2Decrease

namespace OrdinalFormal.ARD2Skyline
open Columns
set_option autoImplicit false
set_option maxHeartbeats 900000

@[simp] theorem expand_zero (g : Graph) : expand g 0 = g.take (g.length-1) := by
  simp [expand]
  split <;> simp

@[simp] theorem expand_empty (n : Nat) : expand ([] : Graph) n = [] := by
  simp [expand, Columns.control]

theorem expand_prefix_succ (g : Graph) (n : Nat) :
    (expand g n).IsPrefix (expand g (n+1)) := by
  unfold expand
  split
  · exact ⟨[], by simp⟩
  · rename_i e he
    exact ⟨block g e n, by simp [List.range_succ, List.flatMap_append, List.append_assoc]⟩

theorem expand_prefix (g : Graph) {i j : Nat} (h : i ≤ j) :
    (expand g i).IsPrefix (expand g j) := by
  induction h with
  | refl => exact ⟨[], by simp⟩
  | @step j _ ih => exact ih.trans (expand_prefix_succ g j)

theorem expand_canonical {g : Graph} (hg : Canonical g) (n : Nat) : Canonical (expand g n) := by
  intro c hc
  unfold expand at hc
  split at hc
  · exact hg c (List.mem_of_mem_take hc)
  · rcases List.mem_append.mp hc with hc | hc
    · exact hg c (List.mem_of_mem_take hc)
    · obtain ⟨b, _, hb⟩ := List.mem_flatMap.mp hc
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hb
      exact skyline_sorted _

@[simp] theorem seed_length (n : Nat) : (seed n).length = n := by simp [seed]

theorem seed_valid (n : Nat) : Valid (seed n) := by
  intro j a ha
  by_cases hj : j < n
  · simp only [seed, List.getElem?_map, List.getElem?_range, hj,
      Option.map_some, Option.getD_some] at ha
    split at ha
    · simp at ha
    · rename_i hzero
      obtain rfl := List.mem_singleton.mp ha
      exact ⟨by dsimp; omega, by dsimp; omega, by dsimp; omega⟩
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hj)] at ha
    simp at ha

theorem seed_canonical (n : Nat) : Canonical (seed n) := by
  intro c hc
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
  split <;> simp [GenericSortedColumns.Sorted]

theorem seed_succ_take (n : Nat) : (seed (n+1)).take n = seed n := by
  simp [seed, List.range_succ, List.map_append]

theorem seed_succ_zero (n : Nat) : expand (seed (n+1)) 0 = seed n := by
  rw [expand_zero, seed_length]
  simpa using seed_succ_take n

def firstColumn (g : Graph) (e : Entry) : Column :=
  skyline ((g[e.parent]?.getD []).map (moveEntry e.parent (g.length-1-e.parent) 1) ++
    seam (g.getLast?.getD []) e (g.length-1-e.parent) 0)

theorem firstColumn_entry {g : Graph} (hg : Valid g) (e : Entry) {a : Entry}
    (ha : a ∈ firstColumn g e) :
    a.parent < e.parent ∨ (a ∈ g.getLast?.getD [] ∧ pairLess a e) ∨
      (a.parent = e.parent ∧ pairLess a e) := by
  unfold firstColumn at ha
  rcases List.mem_append.mp (skyline_subset _ ha) with hs | hs
  · obtain ⟨s, hsource, rfl⟩ := List.mem_map.mp hs
    have hp := (hg e.parent s hsource).2.2
    exact Or.inl (by simp [moveEntry, ARD2.moveEntry, move, hp])
  · have hmove : ∀ s : Entry, moveEntry e.parent (g.length-1-e.parent) 0 s = s := by
      intro s
      cases s
      simp [moveEntry, ARD2.moveEntry, move]
    have hfun : moveEntry e.parent (g.length-1-e.parent) 0 = id := funext hmove
    simp only [seam, hfun, List.map_id, id_eq, List.mem_append] at hs
    rcases hs with hs | hs
    · exact Or.inr (Or.inl ⟨(List.mem_filter.mp hs).1,
        of_decide_eq_true (List.mem_filter.mp hs).2⟩)
    · unfold predecessor at hs
      split at hs
      · rename_i hq
        obtain rfl := List.mem_singleton.mp hs
        exact Or.inr (Or.inr ⟨rfl, Or.inr ⟨rfl, by dsimp; omega⟩⟩)
      · split at hs
        · rename_i hk
          obtain rfl := List.mem_singleton.mp hs
          exact Or.inr (Or.inr ⟨rfl, Or.inl (by dsimp; omega)⟩)
        · simp at hs

theorem firstColumn_lt {g : Graph} (hg : Valid g) (hcan : Canonical g)
    {e : Entry} (he : control compare (g.getLast?.getD []) = some e) :
    listCompare (entryCompare compare) (firstColumn g e) (g.getLast?.getD []) = .lt := by
  have hn := ARD2.nonempty_of_control he
  have hl : g.getLast?.getD [] ∈ g := by
    rw [List.getLast?_eq_some_getLast hn]
    exact List.getLast_mem hn
  apply GenericSortedColumns.compare_lt_of_deleted_pivot compare ARD2.nat_compare_laws
    (skyline_sorted _) (hcan _ hl) e (ExpansionValidity.control_mem compare he)
  · intro hm
    rcases firstColumn_entry hg e hm with hp | ⟨_, hr | ⟨_, hq⟩⟩ | ⟨_, hr | ⟨_, hq⟩⟩ <;> omega
  · intro a ha hnew
    apply (Comparison.entryCompare_lt_iff compare ARD2.nat_compare_laws.eq_iff a e).mpr
    rcases firstColumn_entry hg e ha with hp | ⟨hm, _⟩ | ⟨hp, hr | ⟨hr, hq⟩⟩
    · exact Or.inl hp
    · exact False.elim (hnew hm)
    · exact Or.inr ⟨hp, Or.inl (Nat.compare_eq_lt.mpr hr)⟩
    · exact Or.inr ⟨hp, Or.inr ⟨hr, hq⟩⟩

theorem expand_zero_lt (g : Graph) (hg : g ≠ []) : CompareLt (expand g 0) g := by
  unfold CompareLt ARD2.CompareLt
  rw [expand_zero, ← List.dropLast_eq_take]
  exact RPDDecrease.listCompare_dropLast_lt _ ARD2.columnCompare_self g hg

theorem expand_lt {g : Graph} (hg : Valid g) (hcan : Canonical g) (hn : g ≠ [])
    (n : Nat) : CompareLt (expand g n) g := by
  cases he : control compare (g.getLast?.getD []) with
  | none =>
    have hfs : expand g n = expand g 0 := by simp [expand, he]
    rw [hfs]
    exact expand_zero_lt g hn
  | some e =>
    cases n with
    | zero => exact expand_zero_lt g hn
    | succ n =>
      have hpos : 0 < g.length-1-e.parent := by have := ARD2.control_valid hg he; omega
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
      have hb : ∃ tail, block g e 0 = firstColumn g e :: tail := by
        unfold block firstColumn
        simp only [hm, List.range_succ_eq_map, List.map_cons, Nat.add_zero, Nat.zero_add, ite_true]
        exact ⟨_, rfl⟩
      obtain ⟨tail, ht⟩ := hb
      have hx : ∃ tail, expand g (n+1) = g.dropLast ++ firstColumn g e :: tail := by
        unfold expand
        rw [he, List.range_succ_eq_map]
        simp only [List.flatMap_cons, ht, List.cons_append, ← List.dropLast_eq_take]
        exact ⟨_, rfl⟩
      obtain ⟨tail, ht⟩ := hx
      have hlast : g.getLast?.getD [] = g.getLast hn := by simp [List.getLast?_eq_some_getLast hn]
      have hf := firstColumn_lt hg hcan he
      rw [hlast] at hf
      have hc := RPDDecrease.listCompare_append_left _ ARD2.columnCompare_self g.dropLast
        (firstColumn g e :: tail) [g.getLast hn]
      rw [List.dropLast_concat_getLast hn] at hc
      unfold CompareLt ARD2.CompareLt graphCompare
      rw [ht, hc]
      simp [listCompare, hf, thenCompare]

#print axioms expand_prefix
#print axioms expand_canonical
#print axioms seed_valid
#print axioms expand_lt
end OrdinalFormal.ARD2Skyline
