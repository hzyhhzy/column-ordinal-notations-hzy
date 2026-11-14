import BTnSSBMS.RootCopyBlock

/-! The forced-root block identity instantiated along the literal copied
hole iteration, for any positive finite gap. Scope reset, ancestry, and
the shared higher parent are derived from the actual computation; they
are not premises left to a future caller. This still concerns the complete
unspliced templates, rather than their final substituted descendants. -/
namespace BTnSSBMS.Source

theorem copyHoleAfter_root_rebaseBlock {d : Nat} {context target : ParentContext} {a : List Nat}
    {visible : List Nat} {cap : Nat} {delta : List Nat} {phase : Nat}
    (scope : ShiftView d (context ++ [Parents.label d context a])
      (target ++ [Parents.label d target (shift a cap delta phase)]) visible
      (List.replicate context.length 0 ++ [cap]) context.length cap delta phase)
    (hs : Forests (List Nat)) (rest : NumericalExpr)
    (legal : FiniteLegal d context (.cons a hs rest)) (depth : Nat) {site : HoleSite}
    (found : holeSite d context none depth (.cons a hs rest) = some site)
    (positive : 0 < cap) (room : cap < d)
    (selected : (Parents.label d site.context site.terminal).parents[cap]?.join = some context.length)
    (difference : ∀ row, row < cap → site.terminal[row]?.getD 0 = a[row]?.getD 0 + delta[row]?.getD 0)
    (count : Nat) (nonzero : 0 < count) {result : ParentContext}
    (computed : copyHoleAfter d cap delta context (.cons a hs rest) depth count phase target = some result) :
    rebaseBlock d cap result target.length (shift a cap delta (phase + count))
        (copied d context.length cap delta phase context (List.replicate context.length 0) (.cons a hs rest)) =
      rootBlock (copied d context.length cap delta (phase + count) context
        (List.replicate context.length 0) (.cons a hs rest)) := by
  obtain ⟨observed, finalVisible, actual, finalScope, fixed, protectedPrefix, rootChain⟩ :=
    copyHoleAfter_state scope hs rest legal depth found room selected difference count
  have sameResult : observed = result := Option.some.inj (actual.symm.trans computed)
  subst observed
  have later := Parents.label_parent_bound d site.context site.terminal cap context.length selected
  have growth := copyHoleAfter_strict_length d cap delta context target a hs rest depth count phase
    found later nonzero computed
  have initial : target ++ [Parents.label d target (shift a cap delta phase)] <+: result :=
    List.prefix_of_prefix_length_le protectedPrefix (List.prefix_append _ _) (by simp; omega)
  have same := copyHoleAfter_high_parents scope hs rest legal depth found room selected difference
    count computed (Nat.le_refl cap) room
  exact root_copy_rebaseBlock scope finalScope fixed hs rest legal positive room initial
    (rootChain (cap - 1) (by omega)) same

end BTnSSBMS.Source
