import BTnSSBMS.BNZeroCopies
import BTnSSBMS.BNPrefixSplice

/-! Zero-class expansion of a complete stopping forest, including
all old columns before the selected root. The root and terminal have
their actual context-dependent parent relation. -/
namespace BTnSSBMS.Source

theorem zero_forest_expand_BN {d : Nat} {context : ParentContext} {e : NumericalExpr}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    (positive : 0 < d) (legal : FiniteLegal d context e) (ordered : BN d context e)
    (index : Nat) {a : List Nat} {hs : Forests (List Nat)} {rest : NumericalExpr}
    (cut : drop index e = .cons a hs rest)
    {terminal : List Nat} {attached : Forests (List Nat)}
    (last : last? e = some (terminal, attached))
    (selected : (Parents.label d (outerContext d context (dropLast e)) terminal).parents[0]?.join =
      some (dropContext d context index e).length) (count : Nat) :
    let rootContext := dropContext d context index e
    let part := mark 0 rootContext.length (List.replicate rootContext.length 0)
      (Parents.annotate d rootContext (.cons a hs rest))
    BN d context (splice 0 (copies part 0 [] none count 1) e) := by
  dsimp only
  let rootContext := dropContext d context index e
  let part := mark 0 rootContext.length (List.replicate rootContext.length 0)
    (Parents.annotate d rootContext (.cons a hs rest))
  let replacement := copies part 0 [] none count 1
  let site : HoleSite := ⟨outerContext d context (dropLast e), none, terminal, attached⟩
  have inside := drop_shape_inside cut
  have rootHole : holeSite d rootContext none 0 (.cons a hs rest) = some site := by
    rw [← cut, holeSite_drop d context none 0 index e inside]
    exact holeSite_zero_last d context none e last
  have pieceLegal := legal.drop index
  have pieceBN := ordered.drop index
  rw [cut] at pieceLegal pieceBN
  have rootState := drop_contexts coherent valid index e legal
  have later : rootContext.length < site.context.length :=
    Parents.label_parent_bound d site.context site.terminal 0 rootContext.length selected
  have nonempty : rest ≠ .nil := (holeSite_root_not_terminal rootHole later).resolve_right (fun h => h rfl)
  have rootData := holeSite_zero_data (.cons a hs rest) rootHole
  have beforeCoherent := outerContext_coherent coherent (dropLast e)
  have beforeValid := outerContext_valid (d := d) valid (dropLast e)
  have fullCoherent := Parents.coherent_append_label beforeCoherent terminal
  have fullValid := Parents.context_valid_append_label d site.context beforeValid terminal
  have path : Parents.Ancestor (site.context ++ [Parents.label d site.context site.terminal]) 0
      rootContext.length site.context.length := Parents.Ancestor.up
    (by rw [Parents.append_label_parent]; exact selected) (.refl _)
  have above := holeSite_root_tail_above 0 rest rootHole fullCoherent fullValid positive path
  have good : BN d site.context replacement :=
    initial_copies_zero_BN rootState.1 rootState.2.1 pieceLegal pieceBN rootHole positive selected count
  have finite := initial_copies_low_finiteLegal rootState.1 rootState.2.1 pieceLegal rootHole
    (.inr rfl) positive selected count
  dsimp only at finite
  simp only [List.range_zero, List.map_nil, shift_empty] at finite
  change FiniteLegal d site.context replacement ∧
    (∀ col ∈ labels replacement, a[0]?.getD 0 ≤ col[0]?.getD 0) at finite
  have erase : part.map Prod.fst = .cons a hs rest := by
    simp only [part, mark_erase, Parents.annotate_erase]
  have strict := Parents.label_root_lower_value beforeCoherent beforeValid terminal positive selected (Nat.le_refl 0)
  change (site.context[rootContext.length]?.getD default).coordinates[0]?.getD 0 < terminal[0]?.getD 0 at strict
  rw [holeSite_root_coordinates rootHole later] at strict
  have headLess : listCompare Ord.compare a terminal = .lt :=
    columnCompare_lt_at a terminal 0 (by rw [pieceLegal.1]; exact positive)
      (by rw [(legal.last_context last).1]; exact positive) (by intro j impossible; omega) strict
  have seam : replacement.compare (listCompare Ord.compare) (.cons terminal attached .nil) = .lt ∧
      TerminalFloor a replacement ∧ ExprLE (rootBlock replacement) (dropLast (.cons a hs rest)) := by
    cases count with
    | zero => exact ⟨by simp only [replacement, copies, Expr.compare], trivial, ExprLE.nil _⟩
    | succ count =>
      have blocks := zero_copies_rootBlock erase nonempty above count 1
      refine ⟨?_, ?_, ?_⟩
      · change (copies part 0 [] none (count + 1) 1).compare _ _ = .lt
        rw [zero_copies_succ, erase, splice_cons_tail 0 _ a hs rest nonempty]
        simp only [Expr.compare, headLess]
      · change TerminalFloor a (copies part 0 [] none (count + 1) 1)
        rw [zero_copies_succ, erase, splice_cons_tail 0 _ a hs rest nonempty]
        refine ⟨rfl, ?_⟩
        intro col member
        apply finite.2 col
        change col ∈ labels (copies part 0 [] none (count + 1) 1)
        rwa [zero_copies_succ, erase, splice_cons_tail 0 _ a hs rest nonempty]
      · change ExprLE (rootBlock (copies part 0 [] none (count + 1) 1)) _
        rw [blocks]
        exact .refl _
  have rootGood := pieceBN.splice_zero_root positive pieceLegal nonempty above rootData.2
    (by rw [← rootData.1]; exact good) (by rw [← rootData.1]; exact finite.1)
    (.of_lt seam.1) seam.2.1 seam.2.2
  have cutoff := zero_copies_cut erase nonempty count 1
  have complete := rootBlock_splice_zero_high (hs := hs) nonempty above replacement cutoff
  have rootLower := rootBlock_mono (splice_zero_le (.cons a hs rest) replacement rootData.2 (.of_lt seam.1))
  rw [complete] at rootLower
  exact ordered.splice_zero_before_root positive legal index cut nonempty above rootGood last good
    (.of_lt seam.1) seam.2.1 (seam.2.2.trans rootLower)

end BTnSSBMS.Source
