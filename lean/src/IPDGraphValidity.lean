import IPDGraphNormalization
import IPDProfileValidity

/-! All copied and seam edges have the actual shifted ROOT/SELF alphabet.
The proof applies to the entire expanded graph, not merely its final column. -/

namespace IPD
set_option autoImplicit false
set_option maxHeartbeats 1200000

private theorem fold_select_mem {A : Type*} (f : A → A → A)
    (hf : ∀ a b, f a b = a ∨ f a b = b) (xs : List A) (a : A) :
    xs.foldl f a = a ∨ xs.foldl f a ∈ xs := by
  induction xs generalizing a with
  | nil => exact .inl rfl
  | cons x xs ih =>
    rcases ih (f a x) with he | hm
    · rcases hf a x with hf | hf
      · exact .inl (he.trans hf)
      · exact .inr (List.mem_cons.mpr (.inl (he.trans hf)))
    · exact .inr (List.mem_cons_of_mem x hm)

theorem controller_mem {c : Column} {e : Edge} (he : controller c = some e) : e ∈ c := by
  classical
  cases c with
  | nil => simp [controller] at he
  | cons a as =>
    have hv : as.foldl (fun best e => if ControlLt best e then e else best) a = e :=
      Option.some.inj he
    have hm := fold_select_mem (fun best e => if ControlLt best e then e else best)
      (by intro a b; split <;> simp) as a
    rw [hv] at hm
    exact List.mem_cons.mpr hm

theorem valid_take {g : Graph} (hg : Valid g) (n : Nat) : Valid (g.take n) := by
  intro j e he
  rw [List.getElem?_take] at he
  split at he
  · exact hg j e he
  · simp at he

theorem control_parent_lt {g : Graph} (hg : Valid g) {e : Edge}
    (he : controller (g.getLast?.getD []) = some e) : e.parent < g.length-1 := by
  have hm := controller_mem he
  rw [List.getLast?_eq_getElem?] at hm
  exact (hg _ e hm).1

theorem moveEdge_valid (cut width b j : Nat) (e : Edge) (he : e.Valid j) :
    (moveEdge cut width b e).Valid (shift cut width b j) := by
  refine ⟨shift_strictMono cut width b he.1, ?_⟩
  apply profileAtoms_rename _ _ (shift cut width b) ?_ e.profile he.2
  intro i hi
  rcases hi with hi | rfl
  · exact .inl ((shift_strictMono cut width b).monotone hi)
  · exact .inr rfl

theorem seam_valid {g : Graph} (hg : Valid g) (e : Edge) (b : Nat) :
    ∀ t ∈ seam g e b, t.Valid (shift e.parent (g.length-1-e.parent) b (g.length-1)) := by
  classical
  intro t ht
  obtain ⟨old, hold, hval⟩ := List.mem_filterMap.mp ht
  have hold' := hold
  rw [List.getLast?_eq_getElem?] at hold'
  have hm := moveEdge_valid e.parent (g.length-1-e.parent) b (g.length-1) old (hg _ old hold')
  dsimp only at hval
  split at hval
  · obtain ⟨p, hp, htp⟩ := Option.map_eq_some_iff.mp hval
    rw [← htp]
    exact ⟨hm.1, lowerProfile_valid _ _ _ _ _ hm.2 hp⟩
  · have htp := Option.some.inj hval
    rw [← htp]
    exact hm

noncomputable def stage (g : Graph) (e : Edge) (b : Nat) : Graph :=
  g.take (g.length-1) ++ (List.range b).flatMap (block g e)

def stageWidth (g : Graph) (e : Edge) (b : Nat) : Nat :=
  g.length-1 + b * (g.length-1-e.parent)

@[simp] theorem stage_length (g : Graph) (e : Edge) (b : Nat) :
    (stage g e b).length = stageWidth g e b := by
  simp only [stage, List.length_append, List.length_take, blocks_length, stageWidth,
    Nat.min_eq_left (Nat.sub_le g.length 1)]

theorem stage_succ (g : Graph) (e : Edge) (b : Nat) :
    stage g e (b+1) = stage g e b ++ block g e b := by
  simp [stage, List.range_succ, List.flatMap_append, List.append_assoc]

theorem shift_last {g : Graph} {e : Edge} (he : e.parent < g.length-1) (b : Nat) :
    shift e.parent (g.length-1-e.parent) b (g.length-1) = stageWidth g e b := by
  simp only [shift, if_neg (by omega : ¬g.length-1 < e.parent), stageWidth]

theorem shift_source {g : Graph} {e : Edge} (he : e.parent < g.length-1) (b i : Nat) :
    shift e.parent (g.length-1-e.parent) (b+1) (e.parent+i) = stageWidth g e b + i := by
  simp only [shift, if_neg (by omega : ¬e.parent+i < e.parent), stageWidth, Nat.add_mul, Nat.one_mul]
  omega

theorem block_valid {g : Graph} (hg : Valid g) (e : Edge)
    (he : e.parent < g.length-1) (b i : Nat) (hi : i < g.length-1-e.parent) :
    ∀ t ∈ (block g e b)[i]?.getD [], t.Valid (stageWidth g e b+i) := by
  classical
  intro t ht
  simp only [block, List.getElem?_map, List.getElem?_range, hi, Option.map_some, Option.getD_some] at ht
  have hnorm := normalize_mem _ t ht
  rcases List.mem_append.mp hnorm with hsource | hseam
  · obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hsource
    have hv := moveEdge_valid e.parent (g.length-1-e.parent) (b+1) (e.parent+i) old (hg _ old hold)
    simpa only [shift_source he b i] using hv
  · split at hseam
    · rename_i hi0
      subst i
      simpa only [shift_last he b, Nat.add_zero] using seam_valid hg e b t hseam
    · simp at hseam

theorem stage_valid {g : Graph} (hg : Valid g) (e : Edge)
    (he : e.parent < g.length-1) (b : Nat) : Valid (stage g e b) := by
  induction b with
  | zero => simpa [stage] using valid_take hg (g.length-1)
  | succ b ih =>
    intro j t ht
    rw [stage_succ, List.getElem?_append] at ht
    split at ht
    · exact ih j t ht
    · rename_i hj
      have hbound : j - (stage g e b).length < (block g e b).length := by
        by_contra hn
        have hz : (block g e b)[j-(stage g e b).length]?.getD [] = [] := by
          rw [List.getElem?_eq_none (by omega)]
          rfl
        simp only [hz, List.not_mem_nil] at ht
      rw [stage_length, block_length] at hbound
      rw [stage_length] at ht hj
      have hv := block_valid hg e he b (j-stageWidth g e b) hbound t ht
      have heq : stageWidth g e b + (j-stageWidth g e b) = j := by omega
      simpa only [heq] using hv

theorem expand_valid {g : Graph} (hg : Valid g) (n : Nat) : Valid (expand g n) := by
  cases he : controller (g.getLast?.getD []) with
  | none => simpa [expand, he] using valid_take hg (g.length-1)
  | some e =>
    have hcut := control_parent_lt hg he
    simpa only [expand, he, stage] using stage_valid hg e hcut n

end IPD

#print axioms IPD.moveEdge_valid
#print axioms IPD.seam_valid
#print axioms IPD.stage_valid
#print axioms IPD.expand_valid
