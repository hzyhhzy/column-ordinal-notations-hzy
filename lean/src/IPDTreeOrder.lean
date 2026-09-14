import IPDTreeWellFounded

/-! The exact tree order is total and transitive, and its constructors obey
the comparison rules needed by the IPD lowering algorithm. -/

namespace IPD.Tree
set_option autoImplicit false
set_option maxHeartbeats 600000
universe u
variable {H : Type u} {r : H → H → Prop}

theorem argsLt_of_listLex {xs ys : List (Tree H)}
    (hlen : xs.length = ys.length) (h : List.Lex (LPO r) xs ys) : ArgsLt r xs ys := by
  induction h with
  | nil => simp at hlen
  | rel h => exact .rel h
  | cons _ ih => exact .cons (ih (by simpa using hlen))

private theorem list_trichotomy_on {α : Type*} {s : α → α → Prop}
    (xs ys : List α) (ht : ∀ x ∈ xs, ∀ y ∈ ys, s x y ∨ x = y ∨ s y x) :
    List.Lex s xs ys ∨ xs = ys ∨ List.Lex s ys xs := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact .inr (.inl rfl)
    | cons _ _ => exact .inl .nil
  | cons x xs ih =>
    cases ys with
    | nil => exact .inr (.inr .nil)
    | cons y ys =>
      rcases ht x (by simp) y (by simp) with h | he | h
      · exact .inl (.rel h)
      · subst y
        rcases ih ys (fun a ha b hb => ht a (by simp [ha]) b (by simp [hb])) with h | he | h
        · exact .inl (.cons h)
        · exact .inr (.inl (congrArg (List.cons x) he))
        · exact .inr (.inr (.cons h))
      · exact .inr (.inr (.rel h))

/-- Finite structural comparison: this theorem itself does not invoke
well-foundedness of the tree order. -/
theorem lpo_trichotomy
    (hr : ∀ g h, r g h ∨ g = h ∨ r h g) (s t : Tree H) :
    LPO r s t ∨ s = t ∨ LPO r t s := by
  classical
  induction s using IPD.Tree.inductionOn generalizing t with
  | hz =>
    cases t with
    | zero => exact .inr (.inl rfl)
    | node h ys => exact .inl (.zero h ys)
  | hn g xs ixs =>
    induction t using IPD.Tree.inductionOn with
    | hz => exact .inr (.inr (.zero g xs))
    | hn h ys iys =>
      by_cases hx : ∃ x ∈ xs, x = .node h ys ∨ LPO r (.node h ys) x
      · obtain ⟨x, hm, he | he⟩ := hx
        · subst x
          exact .inr (.inr (.child hm))
        · exact .inr (.inr (.sub hm he))
      by_cases hy : ∃ y ∈ ys, y = .node g xs ∨ LPO r (.node g xs) y
      · obtain ⟨y, hm, he | he⟩ := hy
        · subst y
          exact .inl (.child hm)
        · exact .inl (.sub hm he)
      have hxs : ∀ x ∈ xs, LPO r x (.node h ys) := by
        intro x hm
        rcases ixs x hm (.node h ys) with h | he | h
        · exact h
        · exact (hx ⟨x, hm, .inl he⟩).elim
        · exact (hx ⟨x, hm, .inr h⟩).elim
      have hys : ∀ y ∈ ys, LPO r y (.node g xs) := by
        intro y hm
        rcases iys y hm with h | he | h
        · exact (hy ⟨y, hm, .inr h⟩).elim
        · exact (hy ⟨y, hm, .inl he.symm⟩).elim
        · exact h
      rcases hr g h with hgh | he | hhg
      · exact .inl (.head hgh hxs)
      · subst h
        rcases lt_trichotomy xs.length ys.length with hl | hl | hl
        · exact .inl (.arity hl hxs)
        · rcases list_trichotomy_on xs ys (fun x hx y _ => ixs x hx y) with hh | he | hh
          · exact .inl (.lex hl (argsLt_of_listLex hl hh) hxs)
          · exact .inr (.inl (congrArg (Tree.node g) he))
          · exact .inr (.inr (.lex hl.symm (argsLt_of_listLex hl.symm hh) hys))
        · exact .inr (.inr (.arity hl hys))
      · exact .inr (.inr (.head hhg hys))

theorem lpo_trans (hwell : WellFounded r)
    (htotal : ∀ g h, r g h ∨ g = h ∨ r h g)
    {s t u : Tree H} (hst : LPO r s t) (htu : LPO r t u) : LPO r s u := by
  rcases lpo_trichotomy htotal s u with h | he | h
  · exact h
  · subst u
    exact ((lpo_wellFounded hwell).asymmetric s t hst htu).elim
  · exact ((lpo_wellFounded hwell).asymmetric₃ s t u hst htu h).elim

theorem node_ne_zero (h : H) (xs : List (Tree H)) : (.node h xs : Tree H) ≠ .zero := by
  intro h
  cases h

theorem leaf_lt_nonleaf {h : H} {xs : List (Tree H)} (hne : xs ≠ []) :
    LPO r (.node h []) (.node h xs) := by
  apply LPO.arity
  · simpa using List.length_pos_iff.mpr hne
  · simp

end IPD.Tree

#print axioms IPD.Tree.lpo_trichotomy
#print axioms IPD.Tree.lpo_trans
#print axioms IPD.Tree.leaf_lt_nonleaf
