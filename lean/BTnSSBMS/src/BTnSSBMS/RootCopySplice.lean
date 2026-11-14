import BTnSSBMS.RebaseSplice
import BTnSSBMS.CopyRunRootBlock

/-! Rebasing complete, spliced forced-root material. The first theorem
uses the two actual root scopes; the second constructs the later scope
from the literal finite copy-hole iteration. The transported replacement
is explicit. Identifying it with another entire copy run, and comparing
the two remaining copy counts, are still separate obligations. -/
namespace BTnSSBMS.Source

theorem root_copy_splice_rebaseBlock {d : Nat} {context target later : ParentContext} {a : List Nat}
    {visible nextVisible : List Nat} {cap : Nat} {delta : List Nat} {phase nextPhase : Nat}
    (scope : ShiftView d (context ++ [Parents.label d context a])
      (target ++ [Parents.label d target (shift a cap delta phase)]) visible
      (List.replicate context.length 0 ++ [cap]) context.length cap delta phase)
    (next : ShiftView d (context ++ [Parents.label d context a])
      (later ++ [Parents.label d later (shift a cap delta nextPhase)]) nextVisible
      (List.replicate context.length 0 ++ [cap]) context.length cap delta nextPhase)
    (fixed : nextVisible.take context.length = visible.take context.length)
    (hs : Forests (List Nat)) (rest : NumericalExpr) (legal : FiniteLegal d context (.cons a hs rest))
    (positive : 0 < cap) (room : cap < d)
    (initial : target ++ [Parents.label d target (shift a cap delta phase)] <+: later)
    (path : Parents.Ancestor (later ++ [Parents.label d later (shift a cap delta nextPhase)])
      (cap - 1) target.length later.length)
    (same : (Parents.label d later (shift a cap delta nextPhase)).parents[cap]?.join =
      (Parents.label d target (shift a cap delta phase)).parents[cap]?.join)
    (depth : Nat) {site : HoleSite}
    (found : holeSite d target none depth
      (copied d context.length cap delta phase context (List.replicate context.length 0)
        (.cons a hs rest)) = some site)
    (afterHead : target.length < site.context.length) :
    ∃ targetSite moved,
      holeSite d later none depth
        (copied d context.length cap delta nextPhase context (List.replicate context.length 0)
          (.cons a hs rest)) = some targetSite ∧
      (List.range target.length ++ [later.length]) <+: moved ∧
      Parents.Coherent d site.context ∧ Parents.ContextValid site.context ∧
      Parents.Coherent d targetSite.context ∧ Parents.ContextValid targetSite.context ∧
      Parents.NumericalView d site.context targetSite.context moved ∧
      ∀ replacement, FiniteLegal d site.context replacement → FitsOwner site.owner replacement →
        rebaseBlock d cap later target.length (shift a cap delta nextPhase)
          (splice depth replacement
            (copied d context.length cap delta phase context (List.replicate context.length 0)
              (.cons a hs rest))) =
        rootBlock (splice depth (relocate d site.context targetSite.context moved replacement)
          (copied d context.length cap delta nextPhase context (List.replicate context.length 0)
            (.cons a hs rest))) := by
  have dimension : 0 < d := by omega
  have inside : target.length < later.length := by
    have bound := initial.length_le
    simp only [List.length_append, List.length_cons, List.length_nil] at bound
    omega
  have before : target <+: later := (List.prefix_append _ _).trans initial
  have takeBefore : later.take target.length = target := (List.prefix_iff_eq_take.mp before).symm
  have coordinates := root_prefix_coordinates initial
  have parentSame : (Parents.label d later (shift a cap delta nextPhase)).parents[cap]?.join =
      Parents.parent later cap target.length := by
    rw [← Parents.parent_prefix_eq initial cap target.length (by simp), Parents.append_label_parent]
    exact same
  let forests := copiedForests d context.length cap delta phase (context ++ [Parents.label d context a])
    (List.replicate context.length 0 ++ [cap]) hs
  let tail := copied d context.length cap delta phase (context ++ [Parents.label d context a])
    (List.replicate context.length 0 ++ [cap]) rest
  have atRoot : FiniteLegal d (later.take target.length)
      (.cons (later[target.length]?.getD default).coordinates forests tail) := by
    rw [takeBefore, coordinates]
    simpa only [copied_at_root, forests, tail] using copied_root_finiteLegal scope dimension hs rest legal
  have hole : holeSite d (later.take target.length) none depth
      (.cons (later[target.length]?.getD default).coordinates forests tail) = some site := by
    rw [takeBefore, coordinates]
    simpa only [copied_at_root, forests, tail] using found
  obtain ⟨targetSite, moved, targetFound, extended, sc, sv, tc, tv, view, equation⟩ :=
    rebaseBlock_splice_at_hole (next.targetCoherent.restrict (List.prefix_append _ _))
      (next.targetValid.restrict (List.prefix_append _ _))
      (next.targetUnit.restrict next.targetValid (List.prefix_append _ _))
      (shift a cap delta nextPhase) next.targetUnit positive room inside path parentSame forests tail
      atRoot depth hole afterHead
  have reset := root_copy_partialMaterial scope next fixed hs rest legal positive room initial path
  change partialMaterial d later target.length cap (shift a cap delta nextPhase) forests tail = _ at reset
  rw [reset] at targetFound equation
  refine ⟨targetSite, moved, targetFound, extended, sc, sv, tc, tv, view, ?_⟩
  intro replacement replacementLegal replacementAbove
  have result := equation replacement replacementLegal replacementAbove
  simpa only [coordinates, forests, tail, copied_at_root] using result

theorem copyHoleAfter_spliced_rebaseBlock {d : Nat} {context target : ParentContext} {a : List Nat}
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
    ∃ oldHole newHole moved,
      holeSite d target none depth
        (copied d context.length cap delta phase context (List.replicate context.length 0)
          (.cons a hs rest)) = some oldHole ∧
      holeSite d result none depth
        (copied d context.length cap delta (phase + count) context (List.replicate context.length 0)
          (.cons a hs rest)) = some newHole ∧
      (List.range target.length ++ [result.length]) <+: moved ∧
      Parents.NumericalView d oldHole.context newHole.context moved ∧
      ∀ replacement, FiniteLegal d oldHole.context replacement → FitsOwner oldHole.owner replacement →
        rebaseBlock d cap result target.length (shift a cap delta (phase + count))
          (splice depth replacement
            (copied d context.length cap delta phase context (List.replicate context.length 0)
              (.cons a hs rest))) =
        rootBlock (splice depth (relocate d oldHole.context newHole.context moved replacement)
          (copied d context.length cap delta (phase + count) context (List.replicate context.length 0)
            (.cons a hs rest))) := by
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
  obtain ⟨oldHole, oldFound, _⟩ := copied_root_holeSite scope hs rest legal depth found later
  have span := copied_root_holeSite_span d cap delta phase context target a hs rest depth found oldFound
  obtain ⟨newHole, moved, newFound, extended, _, _, _, _, view, equation⟩ :=
    root_copy_splice_rebaseBlock scope finalScope fixed hs rest legal positive room initial
      (rootChain (cap - 1) (by omega)) same depth oldFound (by omega)
  exact ⟨oldHole, newHole, moved, oldFound, newFound, extended, view, equation⟩

end BTnSSBMS.Source
