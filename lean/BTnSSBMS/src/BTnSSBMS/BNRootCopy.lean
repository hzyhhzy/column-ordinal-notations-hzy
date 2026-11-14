import BTnSSBMS.BNRelocation

/-! Include the forced copy root in BN transport. Its complete outer
template lies strictly above the root after the first column. The
root therefore has no later P0 sibling; nested comparisons use the
ordinary transport theorem. Actual selected-root templates are covered. -/
namespace BTnSSBMS.Source

theorem headBN_above {d : Nat} {context : ParentContext} (positive : 0 < d)
    {a : List Nat} {hs : Forests (List Nat)} {rest : NumericalExpr}
    (legal : FiniteLegal d context (.cons a hs rest))
    (above : ∀ col ∈ labels rest, a[0]?.getD 0 < col[0]?.getD 0) :
    HeadBN d context a hs rest := by
  intro index b ks tail selected same
  have laterLegal := legal.2.2.2.2.drop index
  rw [selected] at laterLegal
  have initial := (List.prefix_append context [Parents.label d context a]).trans (dropContext_prefix d _ index rest)
  have equal := same_zero_parent_value positive initial a b legal.2.1 laterLegal.2.1 same
  have strict := above b (List.mem_of_getElem? (labels_drop_head index rest selected))
  omega

theorem copied_root_BN {d : Nat} {context target : ParentContext} {a : List Nat}
    {visible : List Nat} {cap : Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d (context ++ [Parents.label d context a])
      (target ++ [Parents.label d target (shift a cap delta phase)]) visible
      (List.replicate context.length 0 ++ [cap]) context.length cap delta phase)
    (positive : 0 < d) (hs : Forests (List Nat)) (rest : NumericalExpr)
    (legal : FiniteLegal d context (.cons a hs rest)) (ordered : BN d context (.cons a hs rest))
    (above : ∀ col ∈ labels rest, a[0]?.getD 0 < col[0]?.getD 0) :
    BN d target (copied d context.length cap delta phase context (List.replicate context.length 0) (.cons a hs rest)) := by
  have copiedLegal := copied_root_finiteLegal scope positive hs rest legal
  have higher := copied_above scope positive (by simp : context.length < (context ++ [Parents.label d context a]).length)
    (by simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_sub_cancel]; exact Parents.Ancestor.refl _)
    rest legal.2.2.2.2 (by rw [Parents.reading_append_label]; exact above)
  rw [root_view_point scope, Parents.reading_append_label] at higher
  rw [copied_at_root] at copiedLegal ⊢
  exact ⟨headBN_above positive copiedLegal higher,
    copiedForests_BN scope positive (a[0]?.getD 0) hs legal.2.2.2.1 ordered.2.1,
    copied_BN scope positive rest legal.2.2.2.2 ordered.2.2⟩

/-- Every real low-class selected-root template has the required outer
fence. The property is not supplied by a guessed comparison invariant. -/
theorem selected_root_copied_BN {d cap : Nat} {context target : ParentContext}
    {a : List Nat} {hs : Forests (List Nat)} {rest : NumericalExpr}
    {depth : Nat} {site : HoleSite} {visible : List Nat} {delta : List Nat} {phase : Nat}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    (legal : FiniteLegal d context (.cons a hs rest)) (ordered : BN d context (.cons a hs rest))
    (found : holeSite d context none depth (.cons a hs rest) = some site) (room : cap < d)
    (selected : (Parents.label d site.context site.terminal).parents[cap]?.join = some context.length)
    (scope : ShiftView d (context ++ [Parents.label d context a])
      (target ++ [Parents.label d target (shift a cap delta phase)]) visible
      (List.replicate context.length 0 ++ [cap]) context.length cap delta phase) :
    BN d target (copied d context.length cap delta phase context (List.replicate context.length 0) (.cons a hs rest)) := by
  have states := holeSite_contexts coherent valid depth (.cons a hs rest) found
  have finalCoherent := Parents.coherent_append_label states.1 site.terminal
  have finalValid := Parents.context_valid_append_label d site.context states.2 site.terminal
  have path : Parents.Ancestor (site.context ++ [Parents.label d site.context site.terminal]) cap
      context.length site.context.length := Parents.Ancestor.up (by rw [Parents.append_label_parent]; exact selected) (.refl _)
  have lower := path.lower_row finalCoherent room (Nat.zero_le cap)
  exact copied_root_BN scope (by omega) hs rest legal ordered
    (holeSite_root_tail_above depth rest found finalCoherent finalValid (by omega) lower)

/-- The first real low-class root installs its own verified transport
state. There is no extra ShiftView premise in this instance. The result
is the full ordinary copy, before the terminal hole is replaced. -/
theorem initial_selected_root_copied_BN {d cap : Nat} {context : ParentContext}
    {a : List Nat} {hs : Forests (List Nat)} {rest : NumericalExpr}
    {depth : Nat} {site : HoleSite}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    (legal : FiniteLegal d context (.cons a hs rest)) (ordered : BN d context (.cons a hs rest))
    (found : holeSite d context none depth (.cons a hs rest) = some site) (room : cap < d)
    (selected : (Parents.label d site.context site.terminal).parents[cap]?.join = some context.length) :
    let delta := (List.range cap).map (fun j => site.terminal[j]?.getD 0 - a[j]?.getD 0)
    BN d site.context (copied d context.length cap delta 1 context (List.replicate context.length 0) (.cons a hs rest)) := by
  dsimp only
  have state := holeSite_contexts coherent valid depth (.cons a hs rest) found
  have sourceHole := (holeSite_finiteLegal depth (.cons a hs rest) legal
    (by intro bound impossible; cases impossible) found).1
  have unit := sourceHole.2.1.restrict
    (Parents.context_valid_append_label d site.context state.2 site.terminal) (List.prefix_append _ _)
  have later := Parents.label_parent_bound d site.context site.terminal cap context.length selected
  have coordinates := holeSite_root_coordinates found later
  have takeRoot := holeSite_root_take found later
  have width : (site.context[context.length]?.getD default).coordinates.length = d := by
    rw [coordinates]
    exact legal.1
  have scope := first_copy_shiftView state.1 state.2 unit site.terminal sourceHole.2.1 room selected width
  dsimp only at scope
  rw [takeRoot, coordinates] at scope
  exact selected_root_copied_BN coherent valid legal ordered found room selected scope

end BTnSSBMS.Source
