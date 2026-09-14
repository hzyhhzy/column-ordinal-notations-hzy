import IPDGraphValidity

/-! The controller really is maximal for profile-first, parent-second order.
Every seam edge is a same-parent weakening of an old edge and is strictly
below the moved controller in that order. -/

namespace IPD
set_option autoImplicit false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

def ControlLe (a b : Edge) : Prop :=
  a.profile < b.profile ∨ (a.profile = b.profile ∧ a.parent ≤ b.parent)

theorem controlLe_refl (a : Edge) : ControlLe a a := .inr ⟨rfl,le_rfl⟩

theorem controlLe_trans {a b c : Edge} (hab : ControlLe a b) (hbc : ControlLe b c) :
    ControlLe a c := by
  rcases hab with hab | ⟨heq,hab⟩
  · rcases hbc with hbc | ⟨heq,hbc⟩
    · exact .inl (lt_trans hab hbc)
    · exact .inl (heq ▸ hab)
  · rcases hbc with hbc | ⟨heq',hbc⟩
    · exact .inl (heq ▸ hbc)
    · exact .inr ⟨heq.trans heq',le_trans hab hbc⟩

theorem controlLe_of_lt {a b : Edge} (h : ControlLt a b) : ControlLe a b := by
  rcases h with h | ⟨heq,h⟩
  · exact .inl h
  · exact .inr ⟨heq,le_of_lt h⟩

theorem controlLe_of_not_lt {a b : Edge} (h : ¬ ControlLt a b) : ControlLe b a := by
  rcases lt_trichotomy a.profile b.profile with hab | heq | hba
  · exact (h (.inl hab)).elim
  · exact .inr ⟨heq.symm,le_of_not_gt (fun hab => h (.inr ⟨heq,hab⟩))⟩
  · exact .inl hba

private theorem fold_control_max (xs : Column) (a : Edge) :
    let m := xs.foldl (fun best e => if ControlLt best e then e else best) a
    ControlLe a m ∧ ∀ e ∈ xs, ControlLe e m := by
  classical
  induction xs generalizing a with
  | nil => exact ⟨controlLe_refl a,by simp⟩
  | cons x xs ih =>
    let b := if ControlLt a x then x else a
    have hab : ControlLe a b := by
      dsimp only [b]
      split
      · exact controlLe_of_lt (by assumption)
      · exact controlLe_refl a
    have hxb : ControlLe x b := by
      dsimp only [b]
      split
      · exact controlLe_refl x
      · exact controlLe_of_not_lt (by assumption)
    have hi := ih b
    refine ⟨controlLe_trans hab hi.1,?_⟩
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact controlLe_trans hxb hi.1
    · exact hi.2 e he

theorem controller_max {c : Column} {e : Edge} (he : controller c = some e) :
    ∀ a ∈ c, ControlLe a e := by
  classical
  cases c with
  | nil => simp [controller] at he
  | cons a as =>
    have heq := Option.some.inj he
    have hm := fold_control_max as a
    rw [heq] at hm
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hm.1
    · exact hm.2 x hx

theorem controlLe_profile {a b : Edge} (h : ControlLe a b) : a.profile ≤ b.profile := by
  rcases h with h | ⟨heq,_⟩
  · exact le_of_lt h
  · exact le_of_eq heq

theorem controlLt_of_parent_ne {a b : Edge} (h : ControlLe a b) (hn : a.parent ≠ b.parent) :
    ControlLt a b := by
  rcases h with h | ⟨heq,h⟩
  · exact .inl h
  · exact .inr ⟨heq,lt_of_le_of_ne h hn⟩

theorem moveEdge_controlLt (cut width b : Nat) {a e : Edge} (h : ControlLt a e) :
    ControlLt (moveEdge cut width b a) (moveEdge cut width b e) := by
  rcases h with h | ⟨heq,h⟩
  · exact .inl (renameProfile_strictMono _ (shift_strictMono cut width b) h)
  · exact .inr ⟨congrArg (renameProfile (shift cut width b)) heq,shift_strictMono cut width b h⟩

theorem seam_spec {g : Graph} (hg : Valid g) {e : Edge}
    (he : controller (g.getLast?.getD []) = some e) (b : Nat) :
    ∀ t ∈ seam g e b, ∃ old ∈ g.getLast?.getD [],
      t.parent = (moveEdge e.parent (g.length-1-e.parent) b old).parent ∧
      t.profile ≤ (moveEdge e.parent (g.length-1-e.parent) b old).profile ∧
      ControlLt t (moveEdge e.parent (g.length-1-e.parent) b e) := by
  classical
  intro t ht
  obtain ⟨old,hold,hval⟩ := List.mem_filterMap.mp ht
  have hmax := controller_max he old hold
  have hold' := hold
  rw [List.getLast?_eq_getElem?] at hold'
  have hmv := moveEdge_valid e.parent (g.length-1-e.parent) b (g.length-1) old (hg _ old hold')
  dsimp only at hval
  split at hval
  · obtain ⟨p,hp,htp⟩ := Option.map_eq_some_iff.mp hval
    rw [← htp]
    have hlt := lowerProfile_lt _ _ _ hmv.1 _ _ hp
    refine ⟨old,hold,rfl,le_of_lt hlt,Or.inl ?_⟩
    exact lt_of_lt_of_le hlt
      ((renameProfile_strictMono _ (shift_strictMono _ _ _)).monotone (controlLe_profile hmax))
  · rename_i hne
    have htp := Option.some.inj hval
    rw [← htp]
    exact ⟨old,hold,rfl,le_rfl,moveEdge_controlLt _ _ _ (controlLt_of_parent_ne hmax hne)⟩

end IPD

#print axioms IPD.controller_max
#print axioms IPD.moveEdge_controlLt
#print axioms IPD.seam_spec
