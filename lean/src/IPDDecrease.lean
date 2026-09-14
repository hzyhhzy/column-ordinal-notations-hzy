import IPDColumnOrder
import IPDProfileIdentity

/-! Actual parent-first column decrease. The first new column loses the
controller; every genuinely new edge is smaller than that pivot. -/

namespace IPD
set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable def firstColumn (G : Graph) (e : Edge) : Column :=
  normalize ((G[e.parent]?.getD []).map (moveEdge e.parent (G.length-1-e.parent) 1) ++ seam G e 0)

theorem controlLt_irrefl (e : Edge) : ¬ ControlLt e e := by
  rintro (h | ⟨_,h⟩) <;> exact lt_irrefl _ h

theorem first_source_parent {G : Graph} (hv : Valid G) (e : Edge) (t : Edge)
    (ht : t ∈ (G[e.parent]?.getD []).map (moveEdge e.parent (G.length-1-e.parent) 1)) :
    t.parent < e.parent := by
  obtain ⟨old,hold,rfl⟩ := List.mem_map.mp ht
  have hp := (hv e.parent old hold).1
  simpa only [moveEdge,shift,if_pos hp] using hp

theorem firstColumn_deletes_controller {G : Graph} (hv : Valid G) {e : Edge}
    (he : controller (G.getLast?.getD []) = some e) : e ∉ firstColumn G e := by
  intro hem
  have hm := normalize_mem _ e hem
  rcases List.mem_append.mp hm with hsource | hseam
  · exact lt_irrefl _ (first_source_parent hv e e hsource)
  · obtain ⟨old,hold,hp,hprof,hl⟩ := seam_spec hv he 0 e hseam
    apply controlLt_irrefl e
    simpa only [moveEdge_zero] using hl

theorem seam_zero_eq (G : Graph) (e : Edge) :
    seam G e 0 = (G.getLast?.getD []).filterMap (fun old =>
      if old.parent = e.parent then
        Option.map (fun p => (⟨old.parent,p⟩ : Edge)) (lowerProfile old.parent (G.length-1) 0 old.profile)
      else some old) := by
  simp only [seam,moveEdge_zero,shift_zero]

theorem firstColumn_new_below {G : Graph} (hv : Valid G) {e : Edge}
    (he : controller (G.getLast?.getD []) = some e) (t : Edge)
    (ht : t ∈ firstColumn G e) (hnew : t ∉ G.getLast?.getD []) : EdgeLt t e := by
  have hm := normalize_mem _ t ht
  rcases List.mem_append.mp hm with hsource | hseam
  · exact .inl (first_source_parent hv e t hsource)
  · rw [seam_zero_eq] at hseam
    obtain ⟨old,hold,hval⟩ := List.mem_filterMap.mp hseam
    split at hval
    · rename_i hp
      obtain ⟨p,hpval,htp⟩ := Option.map_eq_some_iff.mp hval
      rw [← htp]
      have hold' := hold
      rw [List.getLast?_eq_getElem?] at hold'
      have hlt := lowerProfile_lt _ _ _ (hv _ old hold').1 _ _ hpval
      exact .inr ⟨hp,lt_of_lt_of_le hlt (controlLe_profile (controller_max he old hold))⟩
    · exact (hnew ((Option.some.inj hval) ▸ hold)).elim

theorem nonempty_of_control {G : Graph} {e : Edge}
    (he : controller (G.getLast?.getD []) = some e) : G ≠ [] := by
  intro hn
  subst G
  simp [controller] at he

theorem firstColumn_lt {G : Graph} (hv : Valid G) (hcan : Canonical G) {e : Edge}
    (he : controller (G.getLast?.getD []) = some e) :
    ColumnLt (firstColumn G e) (G.getLast?.getD []) := by
  have hn := nonempty_of_control he
  have hl : G.getLast?.getD [] ∈ G := by
    rw [List.getLast?_eq_some_getLast hn]
    exact List.getLast_mem hn
  exact normalize_deleted_pivot _ _ e (hcan _ hl) (controller_mem he)
    (firstColumn_deletes_controller hv he) (firstColumn_new_below hv he)

theorem block_zero_first {G : Graph} {e : Edge} (he : e.parent < G.length-1) :
    ∃ tail, block G e 0 = firstColumn G e :: tail := by
  have hl : 0 < G.length-1-e.parent := by omega
  obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hl)
  unfold block firstColumn
  simp only [hm,List.range_succ_eq_map,List.map_cons,Nat.add_zero,Nat.zero_add,ite_true]
  exact ⟨_,rfl⟩

theorem expand_positive_first {G : Graph} (hv : Valid G) {e : Edge}
    (he : controller (G.getLast?.getD []) = some e) (n : Nat) :
    ∃ tail, expand G (n+1) = G.dropLast ++ firstColumn G e :: tail := by
  obtain ⟨tail,ht⟩ := block_zero_first (control_parent_lt hv he)
  unfold expand
  rw [he,List.range_succ_eq_map]
  simp only [List.flatMap_cons,ht,List.cons_append,← List.dropLast_eq_take]
  exact ⟨_,rfl⟩

theorem expand_zero_lt (G : Graph) (hn : G ≠ []) : GraphLt (expand G 0) G := by
  rw [expand_zero,← List.dropLast_eq_take]
  have h : List.Lex ColumnLt [] [G.getLast hn] := List.Lex.nil
  have hh := List.Lex.append_left ColumnLt h G.dropLast
  simpa only [GraphLt,List.append_nil,List.dropLast_concat_getLast hn] using hh

theorem expand_lt {G : Graph} (hv : Valid G) (hcan : Canonical G) (hn : G ≠ []) (n : Nat) :
    GraphLt (expand G n) G := by
  cases he : controller (G.getLast?.getD []) with
  | none =>
    have hsame : expand G n = expand G 0 := by simp only [expand,he]
    rw [hsame]
    exact expand_zero_lt G hn
  | some e =>
    cases n with
    | zero => exact expand_zero_lt G hn
    | succ n =>
      obtain ⟨tail,ht⟩ := expand_positive_first hv he n
      have hc : List.Lex ColumnLt (firstColumn G e :: tail) [G.getLast?.getD []] :=
        List.Lex.rel (firstColumn_lt hv hcan he)
      have hh := List.Lex.append_left ColumnLt hc G.dropLast
      have hlast : G.dropLast ++ [G.getLast?.getD []] = G := by
        rw [List.getLast?_eq_some_getLast hn]
        exact List.dropLast_concat_getLast hn
      simpa only [GraphLt,← ht,hlast] using hh

end IPD

#print axioms IPD.firstColumn_lt
#print axioms IPD.expand_lt
