import IPDGraphController

/-! Actual parent-first column order and a generic sorted-list pivot lemma. -/

namespace IPD
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem edgeLt_irrefl (a : Edge) : ¬ EdgeLt a a := by
  rintro (h | ⟨_,h⟩) <;> exact lt_irrefl _ h

theorem edgeLt_trans {a b c : Edge} (hab : EdgeLt a b) (hbc : EdgeLt b c) : EdgeLt a c := by
  rcases hab with hab | ⟨heq,hab⟩
  · rcases hbc with hbc | ⟨heq,hbc⟩
    · exact .inl (lt_trans hab hbc)
    · exact .inl (heq ▸ hab)
  · rcases hbc with hbc | ⟨heq',hbc⟩
    · exact .inl (heq ▸ hbc)
    · exact .inr ⟨heq.trans heq',lt_trans hab hbc⟩

theorem edgeLt_total (a b : Edge) : EdgeLt a b ∨ a = b ∨ EdgeLt b a := by
  rcases lt_trichotomy a.parent b.parent with hp | hp | hp
  · exact .inl (.inl hp)
  · rcases lt_trichotomy a.profile b.profile with hq | hq | hq
    · exact .inl (.inr ⟨hp,hq⟩)
    · exact .inr (.inl (by cases a; cases b; simp_all))
    · exact .inr (.inr (.inr ⟨hp.symm,hq⟩))
  · exact .inr (.inr (.inl hp))

theorem columnLt_trans {a b c : Column} (hab : ColumnLt a b) (hbc : ColumnLt b c) :
    ColumnLt a c := List.lex_trans @edgeLt_trans hab hbc

theorem graphLt_trans {a b c : Graph} (hab : GraphLt a b) (hbc : GraphLt b c) :
    GraphLt a c := List.lex_trans @columnLt_trans hab hbc

theorem graphLt_irrefl (G : Graph) : ¬ GraphLt G G := List.lex_irrefl (List.lex_irrefl edgeLt_irrefl) G

theorem sorted_deleted_pivot {A : Type*} (r : A → A → Prop)
    (hir : ∀ a, ¬ r a a) (htr : ∀ {a b c}, r a b → r b c → r a c)
    (hto : ∀ a b, r a b ∨ a = b ∨ r b a)
    (xs ys : List A) (p : A) (hx : xs.Pairwise (fun a b => r b a))
    (hy : ys.Pairwise (fun a b => r b a)) (hpy : p ∈ ys) (hpx : p ∉ xs)
    (hnew : ∀ z ∈ xs, z ∉ ys → r z p) : List.Lex r xs ys := by
  classical
  induction ys generalizing xs with
  | nil => simp at hpy
  | cons y ys ih =>
    obtain ⟨hyhead,hytail⟩ := List.pairwise_cons.mp hy
    cases xs with
    | nil => exact List.Lex.nil
    | cons x xs =>
      obtain ⟨hxhead,hxtail⟩ := List.pairwise_cons.mp hx
      rcases hto x y with hxy | rfl | hyx
      · exact List.Lex.rel hxy
      · apply List.Lex.cons
        apply ih xs hxtail hytail
        · rcases List.mem_cons.mp hpy with heq | hm
          · exact (hpx (List.mem_cons.mpr (.inl heq))).elim
          · exact hm
        · exact fun hm => hpx (List.mem_cons_of_mem x hm)
        · intro z hz hnot
          apply hnew z (List.mem_cons_of_mem x hz)
          intro hm
          rcases List.mem_cons.mp hm with heq | hm
          · exact hir x (heq ▸ hxhead z hz)
          · exact hnot hm
      · have hnot : x ∉ y :: ys := by
          intro hm
          rcases List.mem_cons.mp hm with heq | hm
          · exact hir y (heq ▸ hyx)
          · exact hir x (htr (hyhead x hm) hyx)
        have hxp := hnew x (by simp) hnot
        have hxy : r x y := by
          rcases List.mem_cons.mp hpy with heq | hm
          · exact heq ▸ hxp
          · exact htr hxp (hyhead p hm)
        exact (hir x (htr hxy hyx)).elim

theorem parent_sorted_edge_sorted (c : Column)
    (hc : c.Pairwise (fun a b => b.parent < a.parent)) :
    c.Pairwise (fun a b => EdgeLt b a) :=
  hc.imp (fun h => Or.inl h)

theorem normalize_deleted_pivot (c old : Column) (e : Edge)
    (hs : old.Pairwise (fun a b => b.parent < a.parent)) (hem : e ∈ old)
    (hne : e ∉ normalize c) (hnew : ∀ t ∈ normalize c, t ∉ old → EdgeLt t e) :
    ColumnLt (normalize c) old :=
  sorted_deleted_pivot EdgeLt edgeLt_irrefl @edgeLt_trans edgeLt_total _ old e
    (parent_sorted_edge_sorted _ (normalize_canonical c)) (parent_sorted_edge_sorted old hs)
    hem hne hnew

end IPD

#print axioms IPD.graphLt_trans
#print axioms IPD.sorted_deleted_pivot
#print axioms IPD.normalize_deleted_pivot
