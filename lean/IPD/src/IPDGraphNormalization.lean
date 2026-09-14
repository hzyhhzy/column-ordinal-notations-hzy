import IPDGraphCore

/-! Normalization selects existing edges and gives exactly descending,
duplicate-free parent lists. In particular it does not synthesize an unproved
semantic relation at a seam. -/

namespace IPD
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem insertEdge_mem (e : Edge) (c : Column) (t : Edge) :
    t ∈ insertEdge e c → t = e ∨ t ∈ c := by
  induction c with
  | nil => simp [insertEdge]
  | cons a as ih =>
    intro ht
    rw [insertEdge] at ht
    split at ht
    · exact List.mem_cons.mp ht
    · split at ht
      · split at ht
        · exact .inr ht
        · rcases List.mem_cons.mp ht with he | hm
          · exact .inl he
          · exact .inr (List.mem_cons_of_mem a hm)
      · rcases List.mem_cons.mp ht with he | hm
        · exact .inr (List.mem_cons.mpr (.inl he))
        · rcases ih hm with he | hm
          · exact .inl he
          · exact .inr (List.mem_cons_of_mem a hm)

theorem normalize_mem (c : Column) (t : Edge) : t ∈ normalize c → t ∈ c := by
  induction c with
  | nil => simp [normalize]
  | cons a as ih =>
    intro ht
    change t ∈ insertEdge a (normalize as) at ht
    rcases insertEdge_mem a (normalize as) t ht with he | hm
    · exact List.mem_cons.mpr (.inl he)
    · exact List.mem_cons_of_mem a (ih hm)

theorem insertEdge_canonical (e : Edge) (c : Column)
    (hc : c.Pairwise (fun a b => b.parent < a.parent)) :
    (insertEdge e c).Pairwise (fun a b => b.parent < a.parent) := by
  induction c with
  | nil => simp [insertEdge]
  | cons a as ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hc
    rw [insertEdge]
    split
    · rename_i hae
      apply List.Pairwise.cons
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact hae
        · exact lt_trans (hhead b hb) hae
      · exact List.pairwise_cons.mpr ⟨hhead, htail⟩
    · rename_i hnae
      split
      · rename_i heq
        split
        · exact List.pairwise_cons.mpr ⟨hhead, htail⟩
        · exact List.pairwise_cons.mpr ⟨fun b hb => by simpa only [heq] using hhead b hb, htail⟩
      · rename_i hne
        apply List.Pairwise.cons
        · intro b hb
          rcases insertEdge_mem e as b hb with rfl | hb
          · omega
          · exact hhead b hb
        · exact ih htail

theorem normalize_canonical (c : Column) :
    (normalize c).Pairwise (fun a b => b.parent < a.parent) := by
  induction c with
  | nil => simp [normalize]
  | cons a as ih => exact insertEdge_canonical a (normalize as) ih

theorem insertEdge_of_above (e : Edge) (c : Column)
    (h : ∀ a ∈ c, a.parent < e.parent) : insertEdge e c = e :: c := by
  cases c with
  | nil => rfl
  | cons a as => rw [insertEdge, if_pos (h a (by simp))]

theorem normalize_eq_self (c : Column) (hc : c.Pairwise (fun a b => b.parent < a.parent)) :
    normalize c = c := by
  induction c with
  | nil => rfl
  | cons a as ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hc
    change insertEdge a (normalize as) = a :: as
    rw [ih htail]
    exact insertEdge_of_above a as hhead

theorem expand_canonical (g : Graph) (hg : Canonical g) (n : Nat) : Canonical (expand g n) := by
  intro c hc
  unfold expand at hc
  split at hc
  · exact hg c (List.mem_of_mem_take hc)
  · rcases List.mem_append.mp hc with hc | hc
    · exact hg c (List.mem_of_mem_take hc)
    · obtain ⟨b, _, hb⟩ := List.mem_flatMap.mp hc
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hb
      exact normalize_canonical _

end IPD

#print axioms IPD.normalize_mem
#print axioms IPD.normalize_canonical
#print axioms IPD.normalize_eq_self
#print axioms IPD.expand_canonical
