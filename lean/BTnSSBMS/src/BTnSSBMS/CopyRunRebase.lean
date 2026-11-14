import BTnSSBMS.CopyRunNaturality
import BTnSSBMS.CopyCountOrder

/-! Actual arbitrary-gap forced-root pairs with complete historical
copy runs. The phase-transport identity is instantiated from computed
copy-hole contexts, then copy-count monotonicity supplies the root-block
inequality. This covers this pair class, not every source SB pair. -/
namespace BTnSSBMS.Source

theorem root_copy_run_rebaseBlock {d : Nat} {context target later : ParentContext} {a : List Nat}
    {visible nextVisible : List Nat} {cap : Nat} {delta : List Nat} {phase nextPhase : Nat}
    (scope : ShiftView d (context ++ [Parents.label d context a])
      (target ++ [Parents.label d target (shift a cap delta phase)]) visible
      (List.replicate context.length 0 ++ [cap]) context.length cap delta phase)
    (next : ShiftView d (context ++ [Parents.label d context a])
      (later ++ [Parents.label d later (shift a cap delta nextPhase)]) nextVisible
      (List.replicate context.length 0 ++ [cap]) context.length cap delta nextPhase)
    (fixed : nextVisible.take context.length = visible.take context.length)
    (hs : Forests (List Nat)) (rest : NumericalExpr)
    (legal : FiniteLegal d context (.cons a hs rest)) (depth : Nat) {site : HoleSite}
    (found : holeSite d context none depth (.cons a hs rest) = some site)
    (positive : 0 < cap) (room : cap < d)
    (selected : (Parents.label d site.context site.terminal).parents[cap]?.join = some context.length)
    (difference : ∀ row, row < cap → site.terminal[row]?.getD 0 = a[row]?.getD 0 + delta[row]?.getD 0)
    (initial : target ++ [Parents.label d target (shift a cap delta phase)] <+: later)
    (path : Parents.Ancestor (later ++ [Parents.label d later (shift a cap delta nextPhase)])
      (cap - 1) target.length later.length)
    (same : ∀ row, cap ≤ row → row < d →
      (Parents.label d later (shift a cap delta nextPhase)).parents[row]?.join =
        (Parents.label d target (shift a cap delta phase)).parents[row]?.join)
    (count : Nat) :
    let part := mark cap context.length (List.replicate context.length 0)
      (Parents.annotate d context (.cons a hs rest))
    rebaseBlock d cap later target.length (shift a cap delta nextPhase)
      (copies part depth delta none (count + 1) phase) =
      rootBlock (copies part depth delta none (count + 1) nextPhase) := by
  dsimp only
  have coherent := next.targetCoherent.restrict (List.prefix_append _ _)
  have valid := next.targetValid.restrict (List.prefix_append _ _)
  have unit := next.targetUnit.restrict next.targetValid (List.prefix_append _ _)
  have inside : target.length < later.length := by
    have bound := initial.length_le
    simp only [List.length_append, List.length_cons, List.length_nil] at bound
    omega
  have before : target <+: later := (List.prefix_append _ _).trans initial
  have takeBefore : later.take target.length = target := (List.prefix_iff_eq_take.mp before).symm
  have takeOld : later.take (target.length + 1) = target ++ [Parents.label d target (shift a cap delta phase)] := by
    simpa only [List.length_append, List.length_cons, List.length_nil] using (List.prefix_iff_eq_take.mp initial).symm
  have coordinates := root_prefix_coordinates initial
  have oldWidth : (later[target.length]?.getD default).coordinates.length = d := by
    rw [coordinates, shift_width, legal.1]
  have parentSame : (Parents.label d later (shift a cap delta nextPhase)).parents[cap]?.join =
      Parents.parent later cap target.length := by
    rw [← Parents.parent_prefix_eq initial cap target.length (by simp), Parents.append_label_parent]
    exact same cap (Nat.le_refl cap) room
  have head := root_copy_partial_head coherent legal.1 positive room initial path
  have values := partialHead_values coherent (shift a cap delta nextPhase) positive room inside path oldWidth
  rw [head] at values
  have view := Parents.partial_rebase_numericalView coherent valid unit
    (shift a cap delta nextPhase) (shift a cap delta nextPhase) next.targetUnit positive room inside
    path parentSame values.1 values.2
  rw [takeOld] at view
  have highExact : ∀ row, cap ≤ row → row < d →
      Parents.parent (later ++ [Parents.label d later (shift a cap delta nextPhase)]) row
        (Parents.point (List.range target.length ++ [later.length]) target.length) =
      (Parents.parent (target ++ [Parents.label d target (shift a cap delta phase)]) row target.length).map
        (Parents.point (List.range target.length ++ [later.length])) := by
    intro row high rowRoom
    have last : Parents.point (List.range target.length ++ [later.length]) target.length = later.length := by
      simpa only [List.length_range] using Parents.point_append_last (List.range target.length) later.length
    rw [last, Parents.append_label_parent, Parents.append_label_parent, same row high rowRoom]
    cases parent : (Parents.label d target (shift a cap delta phase)).parents[row]?.join with
    | none => rfl
    | some p =>
      have bound := Parents.label_parent_bound d target (shift a cap delta phase) row p parent
      simp only [Option.map_some]
      rw [Parents.point_append_old _ p later.length (by simpa using bound), Parents.point_range _ _ bound]
  have transported := rooted_copies_relocation_square scope next view (root_views_reset_map scope next fixed)
    highExact hs rest legal depth found room selected difference (count + 1)
  dsimp only at transported
  have afterHead := Parents.label_parent_bound d site.context site.terminal cap context.length selected
  obtain ⟨hole, holeFound, _⟩ := copied_root_holeSite scope hs rest legal depth found afterHead
  have span := copied_root_holeSite_span d cap delta phase context target a hs rest depth found holeFound
  rw [copied_at_root] at holeFound
  obtain ⟨forests, tail, shape⟩ := splice_after_head_shape holeFound (by omega)
    (copies (mark cap context.length (List.replicate context.length 0)
      (Parents.annotate d context (.cons a hs rest))) depth delta none count (phase + 1))
  rw [← copied_at_root] at shape
  have fullShape : copies (mark cap context.length (List.replicate context.length 0)
      (Parents.annotate d context (.cons a hs rest))) depth delta none (count + 1) phase =
        .cons (shift a cap delta phase) forests tail := by
    simpa only [copies, ascendReplace_splice, copied] using shape
  have wholeLegal := (copies_low_finiteLegal legal found (.inl positive) room selected delta difference
    (count + 1) phase target visible scope).1
  rw [fullShape] at wholeLegal
  have atRoot : FiniteLegal d (later.take target.length)
      (.cons (later[target.length]?.getD default).coordinates forests tail) := by
    rw [takeBefore, coordinates]
    exact wholeLegal
  have rebased := rebaseBlock_eq_rootedRelocate coherent valid unit (shift a cap delta nextPhase)
    next.targetUnit positive room inside path parentSame forests tail atRoot
  rw [coordinates, takeBefore, head] at rebased
  rw [fullShape] at transported ⊢
  rw [rebased, transported]

theorem copyHoleAfter_complete_rebaseBlock {d : Nat} {context target : ParentContext} {a : List Nat}
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
    (gap : Nat) (nonzero : 0 < gap) {result : ParentContext}
    (computed : copyHoleAfter d cap delta context (.cons a hs rest) depth gap phase target = some result)
    (count : Nat) :
    let part := mark cap context.length (List.replicate context.length 0)
      (Parents.annotate d context (.cons a hs rest))
    rebaseBlock d cap result target.length (shift a cap delta (phase + gap))
      (copies part depth delta none (count + 1) phase) =
      rootBlock (copies part depth delta none (count + 1) (phase + gap)) := by
  obtain ⟨observed, finalVisible, actual, finalScope, fixed, protectedPrefix, rootChain⟩ :=
    copyHoleAfter_state scope hs rest legal depth found room selected difference gap
  have sameResult : observed = result := Option.some.inj (actual.symm.trans computed)
  subst observed
  have afterHead := Parents.label_parent_bound d site.context site.terminal cap context.length selected
  have growth := copyHoleAfter_strict_length d cap delta context target a hs rest depth gap phase
    found afterHead nonzero computed
  have initial : target ++ [Parents.label d target (shift a cap delta phase)] <+: result :=
    List.prefix_of_prefix_length_le protectedPrefix (List.prefix_append _ _) (by simp; omega)
  exact root_copy_run_rebaseBlock scope finalScope fixed hs rest legal depth found positive room selected difference
    initial (rootChain (cap - 1) (by omega))
    (fun row high rowRoom => copyHoleAfter_high_parents scope hs rest legal depth found room selected difference
      gap computed high rowRoom) count

theorem copyHoleAfter_forced_root_SB {d : Nat} {context target : ParentContext} {a : List Nat}
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
    (gap : Nat) (nonzero : 0 < gap) {result : ParentContext}
    (computed : copyHoleAfter d cap delta context (.cons a hs rest) depth gap phase target = some result)
    (oldCount newCount : Nat) (counts : newCount ≤ oldCount + 1) :
    let part := mark cap context.length (List.replicate context.length 0)
      (Parents.annotate d context (.cons a hs rest))
    ExprLE (rootBlock (copies part depth delta none newCount (phase + gap)))
      (rebaseBlock d cap result target.length (shift a cap delta (phase + gap))
        (copies part depth delta none (oldCount + 1) phase)) := by
  dsimp only
  rw [copyHoleAfter_complete_rebaseBlock scope hs rest legal depth found positive room selected difference
    gap nonzero computed oldCount]
  exact copies_rootBlock_count_mono _ depth delta newCount (oldCount + 1) (phase + gap) counts

end BTnSSBMS.Source
