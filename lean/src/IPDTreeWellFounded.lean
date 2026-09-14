import IPDTree

/-!
# Direct accessibility proof for IPD's tree order

The subtype of already accessible trees is an auxiliary proof construction,
not a restriction of the term syntax.  Constructor closure is proved by
head precedence and shortlex induction on accessible arguments, then finite
structural induction on a predecessor.  Finally structural induction shows
that **every** tree is accessible.  No Kruskal, tree-order oracle, or IPD
well-ordering hypothesis is used.
-/

namespace IPD.Tree
set_option autoImplicit false
set_option maxHeartbeats 600000
universe u
variable {H : Type u} {r : H → H → Prop}

private abbrev Good (r : H → H → Prop) := {t : Tree H // Acc (LPO r) t}
private abbrev GoodLt (r : H → H → Prop) : Good r → Good r → Prop :=
  InvImage (LPO r) Subtype.val

private theorem good_wf (r : H → H → Prop) : WellFounded (GoodLt r) :=
  .intro fun t => InvImage.accessible Subtype.val t.property

private def pack (xs : List (Tree H)) (h : ∀ x ∈ xs, Acc (LPO r) x) : List (Good r) :=
  xs.attachWith (Acc (LPO r)) h

@[simp] private theorem map_pack (xs : List (Tree H)) (h : ∀ x ∈ xs, Acc (LPO r) x) :
    (pack xs h).map Subtype.val = xs := List.attachWith_map_subtype_val h

@[simp] private theorem length_pack (xs : List (Tree H)) (h : ∀ x ∈ xs, Acc (LPO r) x) :
    (pack xs h).length = xs.length := by
  have hh := congrArg List.length (map_pack xs h)
  simpa using hh

private theorem good_lex {xs ys : List (Good r)}
    (h : List.Lex (LPO r) (xs.map Subtype.val) (ys.map Subtype.val)) :
    List.Lex (GoodLt r) xs ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => cases h
    | cons y ys => exact .nil
  | cons x xs ih =>
    cases ys with
    | nil => cases h
    | cons y ys =>
      rcases List.cons_lex_cons_iff.mp h with hxy | ⟨heq, htail⟩
      · exact .rel hxy
      · have heq' : x = y := Subtype.ext heq
        subst y
        exact .cons (ih htail)

/-- Constructor closure is the substantive step: the new root need not
already be accessible. -/
private theorem node_acc_good (hr : WellFounded r) :
    ∀ p : H × List (Good r), Acc (LPO r) (.node p.1 (p.2.map Subtype.val)) := by
  let key := Prod.Lex r (List.Shortlex (GoodLt r))
  have hkey : WellFounded key := hr.prod_lex (List.Shortlex.wf (good_wf r))
  intro p
  induction p using hkey.induction with
  | h p ih =>
    rcases p with ⟨h, ys⟩
    have smaller : ∀ s : Tree H, LPO r s (.node h (ys.map Subtype.val)) → Acc (LPO r) s := by
      intro s
      induction s using IPD.Tree.inductionOn with
      | hz => exact fun _ => zero_acc r
      | hn g xs ixs =>
        intro hs
        cases hs with
        | child hm =>
          obtain ⟨t, _, ht⟩ := List.mem_map.mp hm
          rw [← ht]
          exact t.property
        | sub hm hs =>
          obtain ⟨t, _, ht⟩ := List.mem_map.mp hm
          rw [← ht] at hs
          exact t.property.inv hs
        | head hgh hxs =>
          let X := pack xs (fun x hx => ixs x hx (hxs x hx))
          have hX : X.map Subtype.val = xs := map_pack _ _
          have ha := ih (g, X) (Prod.Lex.left _ _ hgh)
          simpa only [hX] using ha
        | arity hlen hxs =>
          let X := pack xs (fun x hx => ixs x hx (hxs x hx))
          have hX : X.map Subtype.val = xs := map_pack _ _
          have hl : X.length < ys.length := by
            simpa only [X, length_pack, List.length_map] using hlen
          have ha := ih (h, X) (Prod.Lex.right _ (List.Shortlex.of_length_lt hl))
          simpa only [hX] using ha
        | lex hlen hlex hxs =>
          let X := pack xs (fun x hx => ixs x hx (hxs x hx))
          have hX : X.map Subtype.val = xs := map_pack _ _
          have hl : X.length = ys.length := by
            simpa only [X, length_pack, List.length_map] using hlen
          have hx : List.Lex (GoodLt r) X ys := by
            apply good_lex
            rw [hX]
            exact argsLt_to_listLex hlex
          have ha := ih (h, X) (Prod.Lex.right _ (List.Shortlex.of_lex hl hx))
          simpa only [hX] using ha
    exact .intro _ smaller

theorem node_acc (hr : WellFounded r) (h : H) (xs : List (Tree H))
    (hxs : ∀ x ∈ xs, Acc (LPO r) x) : Acc (LPO r) (.node h xs) := by
  have ha := node_acc_good hr (h, pack xs hxs)
  simpa only [map_pack] using ha

/-- Every finite IPD tree is accessible when the head precedence is. -/
theorem lpo_wellFounded (hr : WellFounded r) : WellFounded (LPO r) := by
  refine .intro fun t => ?_
  induction t using IPD.Tree.inductionOn with
  | hz => exact zero_acc r
  | hn h xs ih => exact node_acc hr h xs ih

theorem lpo_irrefl (hr : WellFounded r) (t : Tree H) : ¬ LPO r t t :=
  (lpo_wellFounded hr).irrefl.irrefl t

end IPD.Tree

#print axioms IPD.Tree.node_acc
#print axioms IPD.Tree.lpo_wellFounded
#print axioms IPD.Tree.lpo_irrefl
