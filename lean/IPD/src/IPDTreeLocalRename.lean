import IPDTreeRename

/-! Local relabeling: a finite diagram labeling is ordered only on the
addresses it uses, not necessarily on all natural numbers.  This lemma
prevents using global monotonicity where the graph semantics only gives
monotonicity on a finite alphabet. -/

namespace IPD.Tree
set_option autoImplicit false
set_option maxHeartbeats 800000
universe u v
variable {H : Type u} {J : Type v}

def All (P : H → Prop) : Tree H → Prop
  | .zero => True
  | .node h xs => P h ∧ ∀ x ∈ xs, All P x

@[simp] theorem all_zero (P : H → Prop) : All P .zero := by simp [All]

theorem all_node_iff (P : H → Prop) (h : H) (xs : List (Tree H)) :
    All P (.node h xs) ↔ P h ∧ ∀ x ∈ xs, All P x := by simp [All]

private theorem rename_args_on {r : H → H → Prop} {s : J → J → Prop}
    {f : H → J} {xs ys : List (Tree H)} (h : ArgsLt r xs ys)
    (hm : ∀ x ∈ xs, ∀ y ∈ ys, LPO r x y → LPO s (rename f x) (rename f y)) :
    ArgsLt s (xs.map (rename f)) (ys.map (rename f)) := by
  induction xs generalizing ys with
  | nil => cases h
  | cons x xs ih =>
    cases h with
    | rel h => exact .rel (hm _ (by simp) _ (by simp) h)
    | cons h =>
      exact .cons (ih h (fun a ha b hb => hm a (by simp [ha]) b (by simp [hb])))

theorem rename_lpo_on {r : H → H → Prop} {s : J → J → Prop}
    (P : H → Prop) (f : H → J)
    (hf : ∀ a b, P a → P b → r a b → s (f a) (f b))
    (b : Tree H) : ∀ a, All P a → All P b → LPO r a b →
      LPO s (rename f a) (rename f b) := by
  induction b using IPD.Tree.inductionOn with
  | hz =>
    intro a _ _ hab
    exact (not_lpo_zero r a hab).elim
  | hn h ys iys =>
    intro a
    induction a using IPD.Tree.inductionOn with
    | hz =>
      intro _ _ _
      simpa only [rename_zero, rename_node] using LPO.zero (r := s) (f h) (ys.map (rename f))
    | hn g xs ixs =>
      intro ha hb hab
      obtain ⟨hPg, hPxs⟩ := (all_node_iff P g xs).mp ha
      obtain ⟨hPh, hPys⟩ := (all_node_iff P h ys).mp hb
      have hpa : All P (.node g xs) := (all_node_iff P g xs).mpr ⟨hPg, hPxs⟩
      have hpb : All P (.node h ys) := (all_node_iff P h ys).mpr ⟨hPh, hPys⟩
      simp only [rename_node]
      cases hab with
      | child hm =>
        apply LPO.child
        simpa only [rename_node] using List.mem_map_of_mem (f := rename f) hm
      | sub hm hsub =>
        apply LPO.sub (List.mem_map_of_mem (f := rename f) hm)
        simpa only [rename_node] using iys _ hm _ hpa (hPys _ hm) hsub
      | head hgh hxs =>
        apply LPO.head (hf _ _ hPg hPh hgh)
        intro x hx
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        simpa only [rename_node] using ixs y hy (hPxs y hy) hpb (hxs y hy)
      | arity hlen hxs =>
        apply LPO.arity (by simpa only [List.length_map] using hlen)
        intro x hx
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        simpa only [rename_node] using ixs y hy (hPxs y hy) hpb (hxs y hy)
      | lex hlen hlex hxs =>
        apply LPO.lex (by simpa only [List.length_map] using hlen)
          (rename_args_on hlex (fun x hx y hy hxy => iys y hy x (hPxs x hx) (hPys y hy) hxy))
        intro x hx
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        simpa only [rename_node] using ixs y hy (hPxs y hy) hpb (hxs y hy)

theorem rename_lpo_iff_on {r : H → H → Prop} {s : J → J → Prop}
    (ht : ∀ a b, r a b ∨ a = b ∨ r b a) (hw : WellFounded s)
    (P : H → Prop) (f : H → J)
    (hf : ∀ a b, P a → P b → r a b → s (f a) (f b))
    (a b : Tree H) (ha : All P a) (hb : All P b) :
    LPO s (rename f a) (rename f b) ↔ LPO r a b := by
  constructor
  · intro h
    rcases lpo_trichotomy ht a b with h' | he | h'
    · exact h'
    · subst b
      exact (lpo_irrefl hw _ h).elim
    · exact ((lpo_wellFounded hw).asymmetric _ _ h
        (rename_lpo_on P f hf a b hb ha h')).elim
  · exact rename_lpo_on P f hf b a ha hb

end IPD.Tree

#print axioms IPD.Tree.rename_lpo_on
#print axioms IPD.Tree.rename_lpo_iff_on
