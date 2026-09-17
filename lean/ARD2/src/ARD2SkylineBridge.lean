import ARD2SkylineCore

/-! Every small-rule output is a columnwise subdiagram of the legacy output
on the same input, with exactly the same width. This is a finite theorem,
not an assumed simulator, quotient isomorphism or well-ordering premise. -/

namespace OrdinalFormal.ARD2Skyline
open Columns
set_option autoImplicit false
set_option maxHeartbeats 900000
universe u

theorem skyline_subset (c : Column) : skyline c ⊆ c := by
  intro a ha
  have h := ColumnRepresentation.mem_dedupSorted_subset compare ha
  have h' := (ColumnRepresentation.mem_sortDescending compare a _).mp h
  exact (List.mem_filter.mp h').1

theorem skyline_sorted (c : Column) : GenericSortedColumns.Sorted compare (skyline c) :=
  GenericSortedColumns.dedup_sorted compare ARD2.nat_compare_laws
    (GenericSortedColumns.sort_weakSorted compare ARD2.nat_compare_laws _)

theorem normalize_contains {c : Column} {a : Entry} (ha : a ∈ c) :
    a ∈ normalizeColumn compare c := by
  unfold normalizeColumn
  rw [GenericSortedColumns.mem_dedupSorted_iff compare ARD2.nat_compare_laws,
    ColumnRepresentation.mem_sortDescending]
  apply List.mem_flatMap.mpr
  refine ⟨a, ha, ?_⟩
  exact List.mem_map.mpr ⟨a.root, List.mem_range.mpr (by omega), by cases a; rfl⟩

theorem move_strict (cut len b : Nat) {i j : Nat} (h : i < j) :
    move cut len b i < move cut len b j := by
  unfold move
  split <;> split <;> omega

theorem seam_subset (last : Column) (e : Entry) (he : e ∈ last) (len b : Nat) :
    seam last e len b ⊆ ARD2.ordinarySeam last e len b ++ ARD2.generatedSeam e len b := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ha
    obtain ⟨hs, hp⟩ := List.mem_filter.mp hs
    have hp' : pairLess s e := of_decide_eq_true hp
    apply List.mem_append_left
    apply List.mem_flatMap.mpr
    refine ⟨s, hs, List.mem_map.mpr ⟨move e.parent len b s.root, ?_, rfl⟩⟩
    apply List.mem_filter.mpr
    refine ⟨List.mem_range.mpr (by omega), ?_⟩
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    rcases hp' with h | ⟨h, hq⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, move_strict _ _ _ hq⟩
  · unfold predecessor at ha
    split at ha
    · rename_i hroot
      obtain rfl := List.mem_singleton.mp ha
      apply List.mem_append_left
      apply List.mem_flatMap.mpr
      refine ⟨e, he, List.mem_map.mpr ⟨move e.parent len b e.root - 1, ?_, rfl⟩⟩
      apply List.mem_filter.mpr
      refine ⟨List.mem_range.mpr (by omega), ?_⟩
      have hr : 0 < move e.parent len b e.root := hroot
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
      exact Or.inr ⟨trivial, by omega⟩
    · split at ha
      · rename_i hk
        obtain rfl := List.mem_singleton.mp ha
        apply List.mem_append_right
        apply List.mem_flatMap.mpr
        refine ⟨move e.parent len b e.row - 1, List.mem_range.mpr (by exact Nat.sub_lt hk (by omega)), ?_⟩
        exact List.mem_map.mpr ⟨e.parent + (b+1)*len,
          List.mem_range.mpr (by omega), rfl⟩
      · simp at ha

inductive Aligned : Graph → Graph → Prop
  | nil : Aligned [] []
  | cons {c d : Column} {g h : Graph} : c ⊆ d → Aligned g h → Aligned (c :: g) (d :: h)

theorem Aligned.self (g : Graph) : Aligned g g := by
  induction g with
  | nil => exact .nil
  | cons c g ih => exact .cons (fun _ h => h) ih

theorem Aligned.length_eq {g h : Graph} (ha : Aligned g h) : g.length = h.length := by
  induction ha <;> simp_all

theorem Aligned.entries {g h : Graph} (ha : Aligned g h) (j : Nat) :
    g[j]?.getD [] ⊆ h[j]?.getD [] := by
  induction ha generalizing j with
  | nil => exact fun _ hm => hm
  | cons hsub _ ih =>
    cases j with
    | zero => exact hsub
    | succ j => exact ih j

theorem Aligned.append {a b c d : Graph} (h₁ : Aligned a b) (h₂ : Aligned c d) :
    Aligned (a ++ c) (b ++ d) := by
  induction h₁ with
  | nil => exact h₂
  | cons h _ ih => exact .cons h ih

theorem aligned_map (indices : List Nat) (f h : Nat → Column)
    (hh : ∀ i ∈ indices, f i ⊆ h i) : Aligned (indices.map f) (indices.map h) := by
  induction indices with
  | nil => exact .nil
  | cons i tail ih =>
    exact .cons (hh i (by simp)) (ih (fun j hj => hh j (by simp [hj])))

theorem aligned_flatMap (indices : List Nat) (f h : Nat → Graph)
    (hh : ∀ i, Aligned (f i) (h i)) : Aligned (indices.flatMap f) (indices.flatMap h) := by
  induction indices with
  | nil => exact .nil
  | cons i tail ih => exact (hh i).append ih

theorem block_aligned (g : Graph) (e : Entry) (he : e ∈ g.getLast?.getD []) (b : Nat) :
    Aligned (block g e b) (ARD2.block g e b) := by
  apply aligned_map
  intro i _ a ha
  apply normalize_contains
  have hs := skyline_subset _ ha
  rcases List.mem_append.mp hs with hs | hs
  · exact List.mem_append_left _ hs
  · apply List.mem_append_right
    split at hs
    · rename_i hi
      rw [if_pos hi]
      exact seam_subset _ e he _ b hs
    · simp at hs

theorem expand_aligned (g : Graph) (n : Nat) : Aligned (expand g n) (ARD2.expand g n) := by
  cases he : control compare (g.getLast?.getD []) with
  | none => simpa [expand, ARD2.expand, he] using Aligned.self (g.take (g.length-1))
  | some e =>
    simpa [expand, ARD2.expand, he] using
      (Aligned.self (g.take (g.length-1))).append (aligned_flatMap (List.range n) _ _
        (block_aligned g e (ExpansionValidity.control_mem compare he)))

theorem expand_valid {g : Graph} (hg : Valid g) (n : Nat) : Valid (expand g n) := by
  intro j a ha
  exact ARD2.expand_valid hg n j a ((expand_aligned g n).entries j ha)

theorem holds_restrict {Label : Type u} (lt : Label → Label → Prop) (D : Label → Prop)
    (R : Label → Label → Label → Label → Prop) {g h : Graph} (ha : Aligned g h)
    {f : Nat → Label} (hf : Holds lt D R h f) : Holds lt D R g f := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    exact hf.domain i (ha.length_eq ▸ hi)
  · intro i j hij hj
    exact hf.ordered i j hij (ha.length_eq ▸ hj)
  · intro j a hm
    exact hf.relations j a (ha.entries j hm)

#print axioms expand_aligned
#print axioms expand_valid
#print axioms holds_restrict
end OrdinalFormal.ARD2Skyline
