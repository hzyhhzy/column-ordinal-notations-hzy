import BTnSSBMS.CopyKeyTransport

/-!
Exact comparison under one common partial rebase. The proof uses the complete
transported keys and the independently proved fixed-entry key comparison.
It does not compare distinct source entry scopes, and hence does not yet
prove conjugacy of every old binding against every internal copied key.
-/
namespace BTnSSBMS.Source

theorem copied_compare {d : Nat} {source target : ParentContext}
    {visible history keyHistory targetHistory : List Nat} {root cap : Nat}
    {delta : List Nat} {phase : Nat}
    (scope : ShiftView d source target visible history root cap delta phase)
    (keys : KeyShiftView scope keyHistory targetHistory)
    (targetCorrect : BMS.HistoryCorrect target (Parents.point visible root) d targetHistory)
    (positive : 0 < d) (base : List Nat) (baseWidth : base.length = d)
    (e f : NumericalExpr) (leftLegal : FiniteLegal d source e) (rightLegal : FiniteLegal d source f) :
    (copied d root cap delta phase source history e).compare (listCompare Ord.compare)
      (copied d root cap delta phase source history f) = e.compare (listCompare Ord.compare) f := by
  have leftKey := copied_forest_key d e source target visible history keyHistory targetHistory
    root cap delta phase scope keys base baseWidth leftLegal
  have rightKey := copied_forest_key d f source target visible history keyHistory targetHistory
    root cap delta phase scope keys base baseWidth rightLegal
  have targetOrder := Keys.forest_compare d
    (copied d root cap delta phase source history e) (copied d root cap delta phase source history f)
    target (Parents.point visible root) (shift base cap delta phase) targetHistory
    scope.targetCoherent scope.targetValid targetCorrect keys.targetLength
    (scope.view.bounded root scope.afterRoot)
    (copied_finiteLegal scope positive e leftLegal) (copied_finiteLegal scope positive f rightLegal)
  rw [leftKey, rightKey, Keys.forest_compare d e f source root base keyHistory
    scope.sourceCoherent scope.sourceValid keys.correct keys.sourceLength scope.afterRoot leftLegal rightLegal]
    at targetOrder
  exact targetOrder.symm

theorem copiedForests_compare {d : Nat} {source target : ParentContext}
    {visible history keyHistory targetHistory : List Nat} {root cap : Nat}
    {delta : List Nat} {phase : Nat}
    (scope : ShiftView d source target visible history root cap delta phase)
    (keys : KeyShiftView scope keyHistory targetHistory)
    (targetCorrect : BMS.HistoryCorrect target (Parents.point visible root) d targetHistory)
    (positive : 0 < d) (base : List Nat) (baseWidth : base.length = d) (owner : Nat)
    (hs ks : Forests (List Nat)) (leftLegal : FiniteLegalForests d source owner hs)
    (rightLegal : FiniteLegalForests d source owner ks) :
    (copiedForests d root cap delta phase source history hs).compare (listCompare Ord.compare)
      (copiedForests d root cap delta phase source history ks) = hs.compare (listCompare Ord.compare) ks := by
  cases hs with
  | nil => cases ks <;> rfl
  | cons h hs =>
    cases ks with
    | nil => rfl
    | cons k ks =>
      have first := copied_compare scope keys targetCorrect positive base baseWidth
        h k leftLegal.2.1 rightLegal.2.1
      have rest := copiedForests_compare scope keys targetCorrect positive base baseWidth owner
        hs ks leftLegal.2.2 rightLegal.2.2
      simp only [copiedForests_cons, Forests.compare, first, rest]

/-- The common intermediate-row rebase preserves all three comparison
outcomes for finite-legal rooted materials, including arbitrary attached
forests and tails. The actual entering invariant is constructed here. -/
theorem partial_rebase_compare {d : Nat} {context : ParentContext}
    (coherent : Parents.Coherent d context) (valid : Parents.ContextValid context)
    (unit : Parents.UnitSteps d context) (position : List Nat)
    (positionUnit : Parents.UnitSteps d (context ++ [Parents.label d context position]))
    {cut root : Nat} (positive : 0 < cut) (room : cut < d) (insideRoot : root < context.length)
    (path : Parents.Ancestor (context ++ [Parents.label d context position]) (cut - 1) root context.length)
    (same : (Parents.label d context position).parents[cut]?.join = Parents.parent context cut root)
    (hs ks : Forests (List Nat)) (tail rest : NumericalExpr)
    (leftLegal : FiniteLegal d (context.take root)
      (.cons (context[root]?.getD default).coordinates hs tail))
    (rightLegal : FiniteLegal d (context.take root)
      (.cons (context[root]?.getD default).coordinates ks rest)) :
    let base := (context[root]?.getD default).coordinates
    let delta := (List.range cut).map (fun j => position[j]?.getD 0 - base[j]?.getD 0)
    (copied d root cut delta 1 (context.take root) (List.replicate root 0) (.cons base hs tail)).compare
      (listCompare Ord.compare)
      (copied d root cut delta 1 (context.take root) (List.replicate root 0) (.cons base ks rest)) =
    (.cons base hs tail : NumericalExpr).compare (listCompare Ord.compare) (.cons base ks rest) := by
  dsimp only
  let base := (context[root]?.getD default).coordinates
  let delta := (List.range cut).map (fun j => position[j]?.getD 0 - base[j]?.getD 0)
  have scope := partial_rebase_shiftView coherent valid unit position positionUnit
    positive room insideRoot path same leftLegal.1
  have keys := partial_rebase_keyShiftView coherent valid unit position positionUnit
    positive room insideRoot path same leftLegal.1
  have point : Parents.point (List.range root ++ [context.length]) root = context.length := by
    simpa only [List.length_range] using Parents.point_append_last (List.range root) context.length
  have targetCorrect : BMS.HistoryCorrect (context ++ [Parents.label d context (shift base cut delta 1)])
      (Parents.point (List.range root ++ [context.length]) root) d (List.replicate context.length 0 ++ [d]) := by
    rw [point]
    exact BMS.HistoryCorrect.at_root (Parents.context_valid_append_label d context valid _) context.length d
  have divided := coherent.take_succ_label insideRoot
  have left := leftLegal
  have right := rightLegal
  simp only [FiniteLegal] at left right
  rw [← divided] at left right
  have attached := copiedForests_compare scope keys targetCorrect (by omega) base leftLegal.1
    (base[0]?.getD 0) hs ks left.2.2.2.1 right.2.2.2.1
  have continued := copied_compare scope keys targetCorrect (by omega) base leftLegal.1
    tail rest left.2.2.2.2 right.2.2.2.2
  rw [copied_at_root, copied_at_root]
  simp only [Expr.compare, listCompare_self Ord.compare (fun a : Nat => Nat.compare_eq_eq.mpr rfl)]
  rw [← divided]
  simp only [attached, continued]

end BTnSSBMS.Source
