import IPDTreeOrder

/-! Uniform relabeling preserves LPO. This includes relabeling the head,
not only the child list; iterating this map will move nested ROOT/SELF heads. -/

namespace IPD.Tree
set_option autoImplicit false
set_option maxHeartbeats 600000
universe u v w
variable {H : Type u} {J : Type v} {K : Type w}

def rename (f : H → J) : Tree H → Tree J
  | .zero => .zero
  | .node h xs => .node (f h) (xs.map (rename f))

@[simp] theorem rename_zero (f : H → J) : rename f .zero = .zero := by simp [rename]
@[simp] theorem rename_node (f : H → J) (h : H) (xs : List (Tree H)) :
    rename f (.node h xs) = .node (f h) (xs.map (rename f)) := by simp [rename]

theorem rename_comp (f : H → J) (g : J → K) (t : Tree H) :
    rename g (rename f t) = rename (g ∘ f) t := by
  induction t using IPD.Tree.inductionOn with
  | hz => simp
  | hn h xs ih =>
    simp only [rename_node, List.map_map]
    congr 1
    exact List.map_congr_left fun t ht => ih t ht

@[simp] theorem rename_id (t : Tree H) : rename id t = t := by
  induction t using IPD.Tree.inductionOn with
  | hz => simp
  | hn h xs ih =>
    simp only [rename_node, id_eq]
    congr 1
    calc
      xs.map (rename id) = xs.map id := List.map_congr_left fun x hx => ih x hx
      _ = xs := List.map_id xs

private theorem rename_args {r : H → H → Prop} {s : J → J → Prop}
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

theorem rename_lpo {r : H → H → Prop} {s : J → J → Prop}
    (f : H → J) (hf : ∀ a b, r a b → s (f a) (f b))
    {a b : Tree H} (hab : LPO r a b) : LPO s (rename f a) (rename f b) := by
  induction b using IPD.Tree.inductionOn generalizing a with
  | hz => exact (not_lpo_zero r a hab).elim
  | hn h ys iys =>
    induction a using IPD.Tree.inductionOn with
    | hz => simpa only [rename_zero, rename_node] using LPO.zero (r := s) (f h) (ys.map (rename f))
    | hn g xs ixs =>
      simp only [rename_node]
      cases hab with
      | child hm =>
        apply LPO.child
        simpa only [rename_node] using List.mem_map_of_mem (f := rename f) hm
      | sub hm hsub =>
        apply LPO.sub (List.mem_map_of_mem (f := rename f) hm)
        simpa only [rename_node] using iys _ hm hsub
      | head hgh hxs =>
        apply LPO.head (hf _ _ hgh)
        intro x hx
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        simpa only [rename_node] using ixs y hy (hxs y hy)
      | arity hlen hxs =>
        apply LPO.arity (by simpa only [List.length_map] using hlen)
        intro x hx
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        simpa only [rename_node] using ixs y hy (hxs y hy)
      | lex hlen hlex hxs =>
        apply LPO.lex (by simpa only [List.length_map] using hlen)
          (rename_args hlex (fun x _ y hy hxy => iys y hy hxy))
        intro x hx
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        simpa only [rename_node] using ixs y hy (hxs y hy)

/-- Strict embeddings of the head precedence reflect the tree comparison too. -/
theorem rename_lpo_iff {r : H → H → Prop} {s : J → J → Prop}
    (ht : ∀ a b, r a b ∨ a = b ∨ r b a) (hw : WellFounded s)
    (f : H → J) (hf : ∀ a b, r a b → s (f a) (f b)) (a b : Tree H) :
    LPO s (rename f a) (rename f b) ↔ LPO r a b := by
  constructor
  · intro h
    rcases lpo_trichotomy ht a b with h' | he | h'
    · exact h'
    · subst b
      exact (lpo_irrefl hw _ h).elim
    · exact ((lpo_wellFounded hw).asymmetric _ _ h (rename_lpo f hf h')).elim
  · exact rename_lpo f hf

theorem rename_injective {r : H → H → Prop} {s : J → J → Prop}
    (ht : ∀ a b, r a b ∨ a = b ∨ r b a) (hw : WellFounded s)
    (f : H → J) (hf : ∀ a b, r a b → s (f a) (f b)) :
    Function.Injective (rename f) := by
  intro a b hab
  rcases lpo_trichotomy ht a b with h | h | h
  · have h' := rename_lpo f hf h
    rw [hab] at h'
    exact (lpo_irrefl hw _ h').elim
  · exact h
  · have h' := rename_lpo f hf h
    rw [hab] at h'
    exact (lpo_irrefl hw _ h').elim

end IPD.Tree

#print axioms IPD.Tree.rename_comp
#print axioms IPD.Tree.rename_lpo
#print axioms IPD.Tree.rename_lpo_iff
#print axioms IPD.Tree.rename_injective
