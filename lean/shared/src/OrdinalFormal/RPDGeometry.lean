import OrdinalFormal.RPD
import OrdinalFormal.Comparison
import OrdinalFormal.ColumnRepresentation
import OrdinalFormal.Reachability

/-!
Exact geometry of the actual RPD seeds. In particular the adjacent seed path
is proved by reducing the real normalization, controller, and seam operations;
it is not an independent abstract seed-nesting assumption.
-/

namespace OrdinalFormal.RPDGeometry

set_option autoImplicit false
set_option maxHeartbeats 600000

open Columns

def starEntry (k : Nat) : Entry Nat := ⟨k, 0, 0⟩

def star (n : Nat) : Column Nat := (List.range n).reverse.map starEntry

@[simp] theorem entryCompare_star (a b : Nat) :
    entryCompare compare (starEntry a) (starEntry b) = compare a b := by
  simp [entryCompare, starEntry, thenCompare]
  cases h : compare a b <;> simp

@[simp] theorem star_zero : star 0 = [] := rfl

@[simp] theorem star_succ (n : Nat) : star (n + 1) = starEntry n :: star n := by
  simp [star, List.range_succ, List.reverse_append]

theorem sort_append_max (a : Entry Nat) (c : Column Nat)
    (h : ∀ e ∈ c, entryCompare compare e a = .lt) :
    sortDescending compare (c ++ [a]) = a :: sortDescending compare c := by
  induction c with
  | nil => rfl
  | cons e es ih =>
      have he := h e List.mem_cons_self
      have ht := ih (fun x hx => h x (List.mem_cons_of_mem e hx))
      simp only [List.cons_append, sortDescending, ht, insertDescending, he]
      rfl

theorem sort_range (n : Nat) :
    sortDescending compare ((List.range n).map starEntry) = star n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ, List.map_append]
      change sortDescending compare ((List.range n).map starEntry ++ [starEntry n]) = _
      rw [sort_append_max, ih, star_succ]
      intro e he
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp he
      exact (entryCompare_star k n).trans (Nat.compare_eq_lt.mpr (List.mem_range.mp hk))

theorem dedup_star (n : Nat) : dedupSorted compare (star n) = star n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [star_succ]
      simp only [dedupSorted, ih]
      cases n with
      | zero => rfl
      | succ n =>
          simp [star_succ, entryCompare_star, Nat.compare_eq_gt.mpr (Nat.lt_succ_self n)]

theorem roots_star_map (ks : List Nat) :
    ((ks.map starEntry).flatMap fun e =>
      (List.range (e.root + 1)).map fun q => { e with root := q }) = ks.map starEntry := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
      simp only [List.map_cons, List.flatMap_cons, ih]
      rfl

theorem normalize_range (n : Nat) :
    normalizeColumn compare ((List.range n).map starEntry) = star n := by
  simp only [normalizeColumn, roots_star_map, sort_range, dedup_star]

theorem seed_eq (n : Nat) : RPD.seed n = [[], star (n + 1)] := by
  unfold RPD.seed
  change [[], normalizeColumn compare ((List.range (n + 1)).map starEntry)] = _
  rw [normalize_range]

theorem sort_star (n : Nat) : sortDescending compare (star n) = star n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [star_succ]
      simp only [sortDescending, ih]
      cases n with
      | zero => rfl
      | succ n =>
          simp [star_succ, insertDescending, entryCompare_star,
            Nat.compare_eq_gt.mpr (Nat.lt_succ_self n)]

theorem normalize_star (n : Nat) : normalizeColumn compare (star n) = star n := by
  unfold normalizeColumn
  have h := roots_star_map (List.range n).reverse
  change (star n).flatMap (fun e =>
    (List.range (e.root + 1)).map fun q => { e with root := q }) = star n at h
  rw [h, sort_star, dedup_star]

@[simp] theorem controlCompare_star (a b : Nat) :
    controlCompare compare (starEntry a) (starEntry b) = compare a b := by
  simp [controlCompare, starEntry, thenCompare]
  cases h : compare a b <;> simp

theorem fold_control_stable (a : Entry Nat) (c : Column Nat)
    (h : ∀ e ∈ c, controlCompare compare a e ≠ .lt) :
    c.foldl (fun a b => if controlCompare compare a b == .lt then b else a) a = a := by
  induction c with
  | nil => rfl
  | cons e es ih =>
      have he := h e List.mem_cons_self
      simp only [List.foldl_cons, beq_iff_eq, if_neg he]
      simpa only [beq_iff_eq] using ih (fun x hx => h x (List.mem_cons_of_mem e hx))

theorem control_star (n : Nat) : control compare (star (n + 1)) = some (starEntry n) := by
  rw [star_succ]
  simp only [Columns.control]
  rw [fold_control_stable]
  intro e he
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp he
  have hk' : k < n := by simpa using hk
  rw [controlCompare_star, Nat.compare_eq_gt.mpr hk']
  decide

theorem seam_star_below (n k : Nat) (h : n ≤ k) :
    ordinarySeam compare (star n) (starEntry k) 1 0 = star n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hn : n < k := by omega
      have ht := ih (by omega)
      simp only [ordinarySeam] at ht
      simp only [star_succ, ordinarySeam, List.flatMap_cons, ht]
      simp [starEntry, move, List.range_succ, Nat.compare_eq_lt.mpr hn]

theorem seam_star (n : Nat) :
    ordinarySeam compare (star (n + 1)) (starEntry n) 1 0 = star n := by
  have ht := seam_star_below n n (Nat.le_refl n)
  simp only [ordinarySeam] at ht
  simp only [star_succ, ordinarySeam, List.flatMap_cons, ht]
  simp [starEntry, move, List.range_succ]

theorem seed_fs_one (n : Nat) : RPD.fs (RPD.seed (n + 1)) 1 = RPD.seed n := by
  rw [seed_eq, seed_eq]
  unfold RPD.fs expand
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd,
    List.take_succ_cons, List.take_zero, List.getLast?_cons_cons,
    List.getLast?_singleton, Option.getD_some, control_star]
  simp [List.range_succ, block, starEntry, generatedSeam, -star_succ]
  change normalizeColumn compare
    (ordinarySeam compare (star (n + 1 + 1)) (starEntry (n + 1)) 1 0) = star (n + 1)
  rw [seam_star, normalize_star]

theorem seed_reachable (n : Nat) :
    Reach (FSStep ([] : RPD.Diagram) RPD.fs) (RPD.seed (n + 1)) (RPD.seed n) := by
  apply Reach.single
  refine ⟨?_, 1, seed_fs_one n⟩
  rw [seed_eq]
  simp

theorem seed_reachable_of_le {i j : Nat} (hij : i ≤ j) :
    Reach (FSStep ([] : RPD.Diagram) RPD.fs) (RPD.seed j) (RPD.seed i) :=
  seed_reach_of_le RPD.seed seed_reachable hij

#print axioms seed_fs_one
#print axioms seed_reachable

end OrdinalFormal.RPDGeometry
